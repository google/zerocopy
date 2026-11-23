# `lean-zip` Verification Boundary, Anneal `Profile v1` DEFLATE MIR Audit, and Certified-Ratchet Design

## Summary

Comparing formally verified compression engines in Lean 4 (`kim-em/lean-zip` @ `2f7a63f38195bc667a926881b55d10c9f8a88eeb`) against Rust MIR verification under Anneal (`google/zerocopy` `anneal/` @ `f8f13a17d398ae688f0a4bbd24595e09e358eda7`, `0.2.0-alpha.8+`) establishes four durable technical facts:

1. **`lean-zip` (`2f7a63f3`) proves production raw-DEFLATE round-trip (`inflate_deflateRaw`) across `1,703` theorems (`51,722` LOC, `0` `sorry`), while trusting C FFI, `bv_decide`, and two `@[implemented_by]` matchers:** `Zip/Spec/DeflateRoundtripProduction.lean:28-32` proves `Zip.Native.Inflate.inflate (deflateRaw data level) maxOutputSize = .ok data`, and `Zip/Spec/InflateProductionCorrect.lean:19-64` ties production `Inflate.inflate` to RFC 1951 specification predicates. Its trusted computing base includes `4` C FFI files implementing `11` C functions across `12` `@[extern]` declarations (`c/*.c`), `bv_decide` (`Lean.ofReduceBool`/`Lean.trustCompiler`), Lean 4's `ByteArray` runtime + `clang -flto -O3`, and **`2` unproved `@[implemented_by]` specializations** in `Zip/Native/Deflate.lean:3159, 3189` (`lz77ChainLazyIterPMergedH3` and `lz77ChainLazyIterPMergedNoH3`), while `zlib_decompressSingle_compress` (`ZlibCorrect.lean:147`) and `gzip_decompressSingle_compress` (`GzipCorrect.lean:210`) target pure `decompressSingle` rather than production `ZlibDecode.decompress`/`GzipDecode.decompress` (`Zip/Native/Gzip.lean:47, 181`).
2. **Anneal `Profile v1` (`f8f13a17d3`) verifies scalar arithmetic and pure scalar CFG loops end-to-end, while unbundled `theory/` libraries outrun `extract.rs` and `Step.lean`:** Empirical `cargo-anneal verify` probes (`rustc 1.98.0-nightly`, Lean `v4.34.1`, `linux_bwrap`) verify scalar kernels (`adler32_chunk_safe_len`, `43.5 s`) and pure scalar `while` loops using `+` under `-Coverflow-checks=no` via `Anneal.LoopInv` (`adler_scalar_step_loop`, `35.7 s`, axioms `["propext"]`), whereas `u32::wrapping_add` fails capture at `-Copt-level=0` (`TerminatorKind::Call`). Meanwhile, `anneal/theory/Anneal/` already contains `PureLift`, `ByteSubLens` (`MutSummary`), `F2Simd`, `CnfOrd`, `Core`, and `MirTotal`, yet `theory/bundle-manifest.json` omits them, `Trusted/MirSemantics/Layout.lean:55` hardcodes `.big` endianness, and `extract.rs`/`State.lean`/`Step.lean` refuse slices, structs, raw pointers, `MaybeUninit`, `Call`/`Assert`, and `core::arch` SIMD.
3. **Scalar-only proof boundaries miss real outer-loop corruptions and buffer-slack overflows:** Verifying only scalar bit-packing or slack-check helpers leaves loop tail bounds (such as comparing `32 * 8 = 256` bytes and omitting bytes `256..258`) and caller-to-helper slack composition (emitting up to `3`–`4` literals plus a `258`-byte match rounded to `8`/`16`/`32`-byte wild-copy width, e.g., `3 + 264 = 267 > 266`, or reading `out_pos - dist` across `MaybeUninit` when `dist < width`) outside the formal guarantee.
4. **Decoupled certified-token-replay + stored-block ratchet enables full Rust round-trip proofs without verifying heuristic matchfinders:** Separating untrusted heuristic LZ77/DP matchfinders from a verified **token-replay checker**, **canonical Huffman emitter**, **RFC 1951 `BTYPE=00` stored-block fallback**, and **verified RFC 1951 decoder** achieves end-to-end `decompress(compress(x)) == Ok(x)` without mechanizing complex hash-chain or binary-tree parsers, while exposing substantial speed headroom relative to `libdeflate` (`~897–945 MB/s` inflate, `~117 MB/s` L6, `~49 MB/s` L9) and `zlib-rs` (`~859 MB/s` inflate, `~358 MB/s` L1).

## Applicability

- **Formal verification targets:** `kim-em/lean-zip` (`2f7a63f38195bc667a926881b55d10c9f8a88eeb`, Lean `v4.35.0-rc2`), `google/zerocopy` `anneal/` (`f8f13a17d398ae688f0a4bbd24595e09e358eda7`, `cargo-anneal 0.2.0-alpha.8+`, `rustc 1.98.0-nightly f8a08b688`, Lean `v4.34.1`), and `Frommi/miniz_oxide` (`0.9.1`, `b28c237471f63efebe152bddd962dc57bbb531eb`).
- **Benchmark comparators:** `kim-em/lean-zip-benchmark` (`c0a635509312a94642fe616f8a750cae8ead3052`, `results/latest.json` on full 12-file Silesia `211,938,580` bytes, `fetch_corpora.sh` SHA-256 manifest).
- **Related `google/zerocopy:reference` reports:** Cross-references sibling reports `compression-benchmark-methodology-and-rust-vs-lean-zip-pareto-comparison` (Pareto convex-hull and prefix-truncation methodology), `deflate-inflate-algorithms-optimal-dp-and-block-splitting` (`BT_MAX_DIST`, `OPT_NO_TRUNC`, `enough.c`, bitreader refill), `miniz-deflate-kraft-prefix-tables-and-lz77-overlapping-ring-buffer-matches` (Kraft trie invariants and ring-buffer aliasing), `x86-64-adler32-simd-lane-overflow-bounds-and-avx512-codegen-width` (Ice Lake `+prefer-256-bit`, `u16 -> u32` superblock and AVX-512 VNNI lane ceilings, Miri `MaybeUninit` lookback straddle, SSSE3 `pshufb`, BMI2 `shrx`/`bzhi`), and `zero-tcb-verified-asm-macros-and-core-arch-mir-equivalence-stability` (24-primitive `stdarch` MIR Pareto curve).

## Findings

### 1. Exact Theorem Coverage and Trusted Computing Base of `kim-em/lean-zip` (`2f7a63f3`)

`Basis: source`

Inspection of `Zip/Spec/*.lean` (`51,722` lines, `1,703` `theorem` declarations) and `Zip/Native/*.lean` + `c/*.c` establishes the exact boundary of `lean-zip`'s mechanized guarantee:

| Component / Claim | Exact Status in `kim-em/lean-zip` (`2f7a63f3`) | Primary Source Location |
| :--- | :--- | :--- |
| **Raw DEFLATE round-trip** | `Zip.Native.Deflate.inflate_deflateRaw` proves `Inflate.inflate (deflateRaw data level) maxOutputSize = .ok data` for all `data : ByteArray`, `level : UInt8`, and `data.size ≤ maxOutputSize` (routing through `inflateReference_deflateRaw` and `inflate_ok_iff_reference`). | `Zip/Spec/DeflateRoundtripProduction.lean:28-32`, `DeflateRoundtrip.lean:211-213` |
| **RFC 1951 spec soundness/completeness** | `Inflate.decodesTo_of_inflate_eq_ok`, `Inflate.inflate_ok_iff_decodesTo`, `Inflate.inflate_of_isValidStreamFor`, and `Deflate.isValidStreamFor_deflateRaw`. | `Zip/Spec/InflateProductionCorrect.lean:19-64`, `DeflateRoundtrip.lean:1233-1240` |
| **Write-once `uset` inflate fastloop** | `inflateFastU_eq`, `inflateFastU_sound`, `inflateSized_agrees`, and `inflateRawSized_agrees` bridge the single-allocation `uset` fastloop (`goCurU`) back to `Inflate.inflate` / `Inflate.inflateRaw` under `data.size < USize.size` and `maxOut < USize.size`. | `Zip/Spec/InflateFastCorrect.lean:3890-4053` |
| **Zlib & Gzip framing** | `zlib_decompressSingle_compress` and `gzip_decompressSingle_compress` prove round-trip on pure single-member `decompressSingle` (`Inflate.inflateRawReference`), **not** the imperative `for`/`mut` production parsers `ZlibDecode.decompress` / `GzipDecode.decompress`. | `Zip/Spec/ZlibCorrect.lean:25-45, 147-149`, `GzipCorrect.lean:210-212`, `Zip/Native/Gzip.lean:47-143, 181-216` |
| **Checksums** | `Adler32.Native.{updateBytes_eq_updateList, adler32_append, adler32_combine_eq_concat}` and `Crc32.Native.{crcByteTable_eq_crcByte, updateBytes_eq_updateList, crc32_append}`. | `Zip/Native/Adler32.lean:25-151`, `Zip/Native/Crc32.lean:67-136` |
| **Axioms & reflection** | `0` `sorry`, `0` `admit`, `0` user `axiom`s, `0` `native_decide`; uses `bv_decide` (`Lean.ofReduceBool` / `Lean.trustCompiler`) and kernel `decide_cbv`. | `Zip/Spec/*.lean` |
| **C FFI (`@[extern]`)** | `4` C files (`c/copy_within_ffi.c`, `c/extend_within_ffi.c`, `c/bytearray_wide_ffi.c`, `c/inflate_fast_ffi.c`), `11` C implementations, `12` `@[extern]` declarations (`copyWithin`, `extendWithin`, `ugetUInt{32,64}LE`, `usetUInt{32,64}LE`, `pushUInt64LE`, `log2Clz`, `ctz64`, `presize`, `copyWithinAt`, `copyWithinAtU`). Proofs target Lean reference models, not the C implementations. | `Zip/Native/{CopyWithin,ExtendWithin,Wide,InflateFast}.lean`, `lakefile.lean:61-150` |
| **`@[implemented_by]` overrides** | `3` in `Zip/Native/Deflate.lean`: `distCodeWord` (`:346`, proved equal at `:3775-3787`) and **`2` unproved** overrides (`lz77ChainLazyIterPMergedH3` `:3159`, `lz77ChainLazyIterPMergedNoH3` `:3189`, invoked at L7 and adaptive L5 in `DeflateDynamic.lean:1759, 1762`). | `Zip/Native/Deflate.lean:346, 3159, 3189, 3775` |
| **Runtime & build TCB** | Lean `v4.35.0-rc2` kernel and C runtime (`ByteArray`/`USize` primitives), `zipCommon` (`a9ffa91f`), `clang`/`lld` with `-flto -fno-semantic-interposition -O3`; `0` `IO` in `Zip/Native/` or `Zip/Spec/`. | `lakefile.lean:29-55`, `lake-manifest.json` |

### 2. Anneal `Profile v1` (`f8f13a17d3`) Capabilities vs. DEFLATE Verification Gaps

`Basis: source + execution`

Auditing `google/zerocopy:anneal/` at `f8f13a17d398ae688f0a4bbd24595e09e358eda7` alongside live `cargo-anneal` verification probes (`rustc 1.98.0-nightly`, Lean `v4.34.1`, Linux `bwrap`) isolates a sharp divide between **end-to-end admitted MIR (`Profile v1`)** and **in-tree unbundled `theory/` / pre-allocated `Trusted.MirAst` substrates**:

1. **What Verifies End-to-End Today (`Profile v1`):**
   - Dependency-free, feature-free Rust library crates containing non-generic functions over `bool`, `char`, `()`, `!`, `i8..i128`, `isize`, `u8..u128`, `usize`, `core::cmp::Ordering`, `(IntTy, bool)` overflow pairs, and crate-local non-generic inhabited fieldless enums (`trusted/rustc-capture/src/extract.rs:110-196`, `docs/alpha.md:78-81`).
   - **Control-flow loops over scalar locals already verify E2E:** Because `capture` compiles with `-Copt-level=0 -Coverflow-checks=no`, ordinary `+`, `-`, and `*` lower to wrapping `BinOp` statements, and `goto`/`switchInt` back-edges are discharged via bundled `Anneal.LoopInv` (`wpLoop_countdown`, `wpLoop_nat`, `wpUntil`, `wpSim_det`). A probe function `adler_scalar_step_loop(mut a: u32, mut b: u32, count: u32) -> u32` verified total correctness across all $2^{96}$ inputs in **`35,682 ms`** (`exit = 0`, `axioms = ["propext"]`, `linux_bwrap`). By contrast, calling `u32::wrapping_add` inside a loop emits `TerminatorKind::Call` at `-O0` and fails capture.
   - `SpecPreflight` (`trusted/audit/TrustedBoundary.lean:40-50`) rejects non-allowlisted identifiers such as `_root_.String.ofList` in `Spec.lean`.
2. **Exact `file:line` Blockers for Real DEFLATE/zlib Hot Loops:**
   - **Diagnostic ordering (`extract.rs:821` vs. `881`):** `extract::body` checks `body.required_consts` (`L821`) and `codegen_attrs` (`L859`, e.g., `#[target_feature]`) *before* `local_decls` (`L881`) and `basic_blocks` (`L886`), so functions containing panic formatting or constant asserts report `"required constants are unavailable in the scalar model"` ahead of slice/pointer/SIMD type refusals.
   - **Endianness lock (`Trusted/MirSemantics/Layout.lean:55`):** `profileTargetEndian : TargetEndian := .big` is hardcoded `.big` (safe only while `Profile v1` forbids byte-observing casts, slices, or unions); any byte-level extension must parameterize endianness from `CaptureManifest`.
   - **Unbundled `theory/Anneal/` gap (`theory/bundle-manifest.json:1-77` vs. `Anneal.lean:1-52`):** `PureLift` (borrow DAGs + `SpatialPin`), `ByteSubLens` (byte-slice lenses + `MutSummaryCut`), `F2Simd` (`clmul`/`vpshufb128` $\mathbb{F}_2$-linearity), `CnfOrd` (`< ω^ω` ordinal termination), `Core`, and `MirTotal` exist in-tree with zero `sorry`, yet are excluded from the `18`-module `bundle-manifest.json` available to `cargo-anneal verify`.
   - **Unwired AST & Memory substrates:** `MirAst` already defines `.ref`/`.rawPtr` (`Types.lean:275-276`), `.deref`/`.field` (`Places.lean:49-50`), `.addressOf`/`.aggregateTuple` (`Rvalues.lean:209-211`), and `.call`/`.assert` (`Terminators.lean:152-156`), and `Memory.lean:43-261` models `AllocByte.uninit` allocations—but `ProjectionElem` lacks `Index`/`ConstantIndex`/`Subslice`, `Boundary.lean:209-219` + `State.lean:222-261` + `Step.lean:375, 741-742, 772-773` gate execution to single-frame Profile v1 scalars with empty `callerMem`, and `MirAst`/`MirSemantics` have zero `#[repr(simd)]` or `core::arch` intrinsic nodes.

### 3. Why Scalar-Only Proof Boundaries Miss Real Bugs (and the Certified-Ratchet Cure)

`Basis: source + execution (support/verify_deflate_verification_boundaries.py) + derived`

When formal verification covers only scalar leaf helpers (table packing, chunk-length clamping, slack-threshold predicates) while leaving outer loops and buffer glue to unit tests:

1. **Escape Pattern 1 (Match-Extension Tail Omission `256..258`):** An unrolled `32 × 8`-byte XOR match-extension loop checks bytes `0..256` and returns `min(max_match_len, 258)` without comparing bytes `256` and `257`. Every scalar helper proof passes, and small unit tests without `256`- or `257`-byte near-matches pass, yet real corpus streams with 256-byte prefixes corrupt output silently (`probe_escape1_match_tail_256_258`).
2. **Escape Pattern 2 (Caller-vs-Helper Wild-Copy Slack & `MaybeUninit` Straddle):** Proving `out_rem >= 266` (`258 + 8`) inside a helper fails when the unverified outer loop emits `3` leading literal bytes before an `8`-byte-rounded `258`-byte match (`3 + 33 * 8 = 267 > 266`, 1-byte OOB write; or `4 + 288 = 292 <= 304` for `32`-byte AVX2 stores). Additionally, on `MaybeUninit<u8>` output buffers where `[0..out_pos)` is initialized, reading `width` bytes at `out_pos - dist` straddles uninitialized memory whenever `dist < width` (`probe_escape2_wild_copy_and_maybeuninit`), requiring `dist >= width` or initialized-window shuffles (`[out_pos - 16 .. out_pos)` via SSSE3 `pshufb`).
3. **Decoupled Certified-Token-Replay + Stored-Block Ratchet Architecture:** Rather than proving thousands of lines of hash-table, binary-tree, JSD block-splitting, and DP matchfinding logic functionally equivalent to an encoder spec, an end-to-end Rust round-trip theorem splits into four tractable verified components (`probe_certified_token_ratchet`):
   - **Untrusted Heuristic Matchfinder / DP Parser** $\to$ produces LZ77 `Seq` / `Token` buffer (requiring only UB/panic-freedom if written in safe Rust or memory-safety verification if `unsafe`).
   - **Verified Token-Stream Replay Checker** $\to$ checks every literal and `(len ∈ 3..=258, dist ∈ 1..=32768)` back-reference against `input` in linear time (`replay_tokens(tokens) == Some(input)`).
   - **Verified Canonical Huffman Emitter + BitWriter + `BTYPE=00` Stored-Block Ratchet** $\to$ proved to invert RFC 1951 decoding on validated tokens, falling back unconditionally to verified multi-chunk stored blocks (`<= 65535` bytes/block) if token replay fails or dynamic/fixed encoding is not strictly smaller.
   - **Verified RFC 1951 Decoder + Adler-32** $\to$ proved sound and complete against `DecodesTo`, with Adler-32 lane ceilings (`5552` scalar, `K = 16` nested `u16 -> u32`, `2048 × 128 B` AVX-512 VNNI) bound directly to the loop code.

### 4. Competitive Headroom (`libdeflate`, `zlib-rs`, `zlib-ng`) and Reproducible Silesia Baseline

`Basis: source + execution (lean-zip-benchmark results/latest.json + fetch_corpora.sh)`

Multi-codec full-Silesia measurements (`211,938,580` bytes across 12 files) recorded in `kim-em/lean-zip-benchmark` (`c0a63550`, `results/latest.json`, `chungus2` `x86_64`) establish the competitive performance targets beyond `miniz_oxide 0.9.1`:

| Comparator | L1 Ratio @ Comp (Decomp) | L6 Ratio @ Comp (Decomp) | L9 Ratio @ Comp (Decomp) | Notes from Source (`comparators/`) |
| :--- | :--- | :--- | :--- | :--- |
| **`libdeflate`** | `0.3549 @ 271.5 (897.4)` | `0.3201 @ 116.9 (938.6)` | `0.3146 @ 49.3 (944.6)` | Whole-buffer C + SIMD/BMI2; dominates mid/high compress and inflate |
| **`zlib_rs`** (`flate2`) | `0.4610 @ 358.5 (748.8)` | `0.3251 @ 89.0 (857.2)` | `0.3182 @ 42.6 (859.2)` | Pure Rust + SIMD via `flate2` streaming wrapper (`comparators/rust_codecs/src/main.rs`) |
| **`zlib_ng`** (`flate2`) | `0.4610 @ 329.6 (722.4)` | `0.3251 @ 91.9 (828.4)` | `0.3182 @ 39.1 (833.3)` | SIMD-accelerated C zlib |
| **`lean-zip`** (`native`) | `0.3928 @ 267.3 (329.1)` | `0.3220 @ 46.4 (361.4)` | `0.3139 @ 4.5 (348.9)` | Lean `v4.33.0-rc1` in `latest.json` (`2f7a63f3` pins `v4.35.0-rc2`) |
| **`miniz_oxide`** (`flate2`) | `0.4305 @ 232.1 (472.9)` | `0.3216 @ 35.5 (545.2)` | `0.3194 @ 22.2 (551.0)` | Upstream pure-Rust baseline |

Key verified architectural levers separating `miniz_oxide`-class Rust codecs from `libdeflate` / `zlib-rs` throughput:
- **Inflate:** multi-literal root-table packing + BMI2 `shrx`/`bzhi` bitfield extraction + mask-free 56-bit refill + eliminating `vec![0; ...]` zero-init (either via `MaybeUninit<u8>` in `unsafe` or caller-reusable `&mut [u8]` slice APIs in safe Rust) + fusing Adler-32 updates rather than a separate second buffer pass with 64-bit `% 65521`.
- **Deflate:** batched 4-literal 64-bit `BitWriter` flushes (instead of per-literal flushes), reusable epoch-tagged scratch state (avoiding per-call `256 KiB`+ table zeroing), 4-way cache-line associative `ht` matchfinders at L2–L4, bounded-depth `bt` at L6–L7 (instead of restricting `bt` to L8–L9), and 1-pass / bounded-pass near-optimal DP at L8–L9.
- **SIMD verification seam:** As established in `zero-tcb-verified-asm-macros-and-core-arch-mir-equivalence-stability`, `Runtime(PostCleanup)` MIR retains `core::arch::x86_64::_mm*` calls with `0%` drift across `rustc 1.98`–`1.102`, and `24` curated `stdarch` leaf primitives cover `98.94%` of real SIMD call sites—making MIR-level verified SIMD checksums and copies tractable without `.o` lifting churn.

## Boundaries

- **[not examined]** `rustc-capture` behavior on open non-merged PRs (`#4135`, `#4147`, `#4156`, `#4162`, `#4163`) was inspected by PR metadata/diffs rather than merged and benchmarked on `f8f13a17d3`.
- **[unsupported]** Under `google/zerocopy:anneal/` `f8f13a17d3`, verifying real slice-taking, struct-taking, `MaybeUninit`, `#[target_feature]`, or `Call`-containing DEFLATE/Adler-32 Rust bodies directly is explicitly unsupported (`fail closed` at `extract.rs` / `Boundary.lean` / `State.lean` / `Step.lean`).
- **[known not to apply]** `lean-zip` `ZlibCorrect.zlib_decompressSingle_compress` and `GzipCorrect.gzip_decompressSingle_compress` apply only to `decompressSingle`, not to production `ZlibDecode.decompress` / `GzipDecode.decompress`. Similarly, standalone mathematical theorems (such as Adler-32 `u32` bounds) do not automatically apply to a SIMD implementation unless bound to its actual lane widths (e.g., accumulating `prev_a`/`prev_b` in `u64` vs `u32`).
- **[not examined]** Raw non-`flate2` `zlib-rs` (`libz_rs_sys::uncompress`) single-buffer throughput on Intel Ice Lake vs `libdeflate` was not re-measured directly in this investigation; `latest.json` reflects `flate2` streaming adapters on `chungus2`.

## Evidence

- **`kim-em/lean-zip` (`2f7a63f38195bc667a926881b55d10c9f8a88eeb`):** `Zip/Spec/DeflateRoundtripProduction.lean:28-32`, `Zip/Spec/DeflateRoundtrip.lean:211-213, 535-538, 1233-1240`, `Zip/Spec/InflateProductionCorrect.lean:19-64`, `Zip/Spec/InflateTreeFreeCorrect.lean:3878-3954`, `Zip/Spec/InflateFastCorrect.lean:3890-4053`, `Zip/Spec/ZlibCorrect.lean:25-45, 147-149`, `Zip/Spec/GzipCorrect.lean:174-212`, `Zip/Native/Gzip.lean:47-216`, `Zip/Native/Deflate.lean:346, 3159, 3189, 3775`, `Zip/Native/{CopyWithin,ExtendWithin,Wide,InflateFast,Adler32,Crc32}.lean`, `c/{copy_within,extend_within,bytearray_wide,inflate_fast}_ffi.c`, `lakefile.lean:29-157`.
- **`kim-em/lean-zip-benchmark` (`c0a635509312a94642fe616f8a750cae8ead3052`):** `fetch_corpora.sh:19-97` (12 Silesia SHA-256 checksums, `211,938,580` B total), `results/latest.json`, `comparators/rust_codecs/src/main.rs:1-120`, `whole_tar_l6.sh`.
- **`google/zerocopy` `anneal/` (`f8f13a17d398ae688f0a4bbd24595e09e358eda7`):** `docs/alpha.md:78-81`, `trusted/rustc-capture/src/extract.rs:110-207, 301-360, 449-490, 626-628, 766, 821-886`, `trusted/lean/Trusted/MirAst/{Types,Places,Rvalues,Terminators}.lean`, `trusted/lean/Trusted/MirSemantics/{Layout.lean:55, Memory.lean:22-261, State.lean:222-261, Step.lean:375,741-742,772-773, Boundary.lean:209-250}`, `trusted/audit/TrustedBoundary.lean:40-50`, `theory/bundle-manifest.json:1-77`, `theory/Anneal.lean:1-52`, `theory/Anneal/LoopInv.lean:1-80`.
- **Preserved standalone probe:** [`support/verify_deflate_verification_boundaries.py`](support/verify_deflate_verification_boundaries.py) — deterministic Python 3.10+ probe verifying Escape 1 (`256..258` tail corruption vs. fixed check), Escape 2 (`3 + 264 = 267 > 266` overshoot and `dist < width` `MaybeUninit` straddle), Adler-32 `5552`/`K=16`/`K=24`/`2048`-block bounds, certified token-replay + `BTYPE=00` stored-block ratchet rejection of Escape 1, and Silesia canonical sizes (`211,938,580` B). Executed cleanly under `PYTHONHASHSEED=1` and `PYTHONHASHSEED=2`.

## Revalidation

Run the standalone boundary verification probe cleanly with deterministic hash seeds:

```console
PYTHONHASHSEED=1 python3 reports/lean-zip-verification-boundary-and-rust-deflate-mir-audit/support/verify_deflate_verification_boundaries.py
PYTHONHASHSEED=2 python3 reports/lean-zip-verification-boundary-and-rust-deflate-mir-audit/support/verify_deflate_verification_boundaries.py
```

To re-verify Silesia corpus integrity on demand, fetch the 12 files per `kim-em/lean-zip-benchmark`'s `fetch_corpora.sh` SHA-256 manifest, and to re-probe Anneal `Profile v1` loop support, run `cargo anneal verify` on a standalone scalar `while` loop compiled with plain wrapping `+` (under `-Coverflow-checks=no`) imported against `Anneal.LoopInv`.
