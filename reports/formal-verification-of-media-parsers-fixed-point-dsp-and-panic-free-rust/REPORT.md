# Formal Verification of Media Parsers, Fixed-Point DSP Transforms, SIMD-Scalar Equivalence, and Panic-Free Rust Codecs

## Summary

Monolithic verification of an entire multimedia decoder—combining stateful bit-level entropy parsing, adaptive fixed-point signal processing, multi-threaded tile buffers, and hand-tuned SIMD kernels—collapses under SMT/SAT path explosion unless each codec subsystem is paired with a verifier matching its mathematical structure and priority tier. Grounded in pinned sources (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `google/wuffs@a87f0bb85b9406d29f48a1c03b6f42c4585145f6`, `verus-lang/verus@0dab219272ac2353320bd177ebb3929453b90a9e`, `secure-foundations/vest@026867a37d4b918153058df2c8db6c52fc62ba35`, `project-everest/everparse@f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`, `model-checking/kani@0601bc57f00a5b7f4d8fb4dd76acd6ec9355227a`, `flux-rs/flux@ac24831e4f3dc570ad991751ff65bea0826ed446`, `AeneasVerif/aeneas@2e3d4488280bb8a95411db81019a7854a784861f`, `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, `xiph/opus@31b4b36284394b66a4c9d7352991aa977dfc8bc1`, `memorysafety/rav1d@2e7216c20ac2a75de204d6c8d7268b75a45959b4`, `ISO/IEC 23002-1`, and `ISO/IEC 23002-2:2008`):

1. **No single verifier spans the four-tier media verification priority stack:** `Wuffs` and `Flux` discharge compile-time slice-bounds and arithmetic-overflow panic-freedom (`Priority 2`) in milliseconds via non-SMT interval arithmetic or liquid refinements; `Vest` and `EverParse` synthesize memory-safe, non-malleable container/header parsers (`Priority 1+2+4`); `Kani` performs bit-precise bounded checking of unsafe FFI wrappers and small DSP kernels; and `Anneal`'s `PureLift` + `SafeTwin` architecture provides `3`-axiom Lean 4 proofs of UB-freedom, panic-freedom, and SIMD-vs-scalar equivalence (`Priority 1+2+3`) over Rust MIR (`Runtime(PostCleanup)`).
2. **Container headers and fixed-point transform kernels separate cleanly across formal toolchains.** `Vest` (`vest_tests/src/bits.vest`) excels at byte-aligned containers and cross-byte header bitfields (`u3`/`u10`/`u3`, `choose(@hdr.kind)`), while explicitly leaving its `.vest` DSL frontend outside the Verus-verified TCB (`README.md:32`). Stateful entropy coders and variable-length ring buffers defeat static TLV combinators and instead favor compile-time range/refinement disciplines (`Wuffs`, `Flux`).
3. **Fixed-point DSP verification must separate UB-free adversarial wrapping from normative dynamic-range exactness.** Auditing `FFmpeg`'s `ff_h264_idct8_add` (`h264idct_template.c:69-142`) at `BIT_DEPTH > 8` (`dctcoef = int32_t`) reveals both normative `int32_t` sufficiency (`obs_pass2_max = 18,390,973` at 12-bit, `73,564,093` at 14-bit $\ll 2^{31}-1$) and concrete signed-overflow C UB on malformed inputs (`line 76` `block[0] += 32`, `line 90` uncast `-block[i+3*8]` vs `line 121` `-(unsigned)block[3+i*8]`). Similarly, `Opus` `MULT32_32_Q31` exhibits `0..3` ULP negative carry drift between `OPUS_FAST_INT64` and its 32-bit split fallback (`celt/fixed_generic.h:68-72`), measured across `100,000` random samples.
4. **Independent panic-freedom proofs do NOT guarantee SIMD-vs-scalar equivalence.** Full `8×8` simulation of `google/wuffs`'s scalar JPEG IDCT (`decode_idct_default.wuffs`) against its AVX2 IDCT (`decode_idct_x86_avx2.wuffs`) confirms `0 / 5,000` pixel mismatches when outputs lie within `[-512, 511]` and `|c * q| <= 32767`, yet uncovers **two concrete pixel-level divergences of `255` levels** (`[255, 0, 255, ...]` vs `[0, 0, 255, ...]` on `c=200, q=200` due to `_mm256_mullo_epi16`; `[0, 214, ...]` vs `[255, 214, ...]` when `|c*q| <= 1560` triggers `BIAS_AND_CLAMP[... & 1023]` modulo-1024 wrapping vs AVX2 hardware saturation). Relational `SafeTwin` + `BiAlign` theorems close this gap explicitly under a tiny TCB.
5. **Modular `PureLift` decomposition (`PermTree`, `SpatialPin`, `BlockCfg`) eliminates whole-codec proof blowup.** Keeping syntax/DPB orchestration in pure Rust (`PermTree`), isolating `unsafe` SIMD plane mutations inside localized `SpatialBlock` frames (`SpatialPin`), decomposing multi-block CFGs into $O(N)$ `LocalBlockVC` obligations (`BlockCfg`), and linking scalar reference models to SIMD twins across `TotalSafeTwinEquiv` prevents exponential solver blowup and closes `rav1d`'s release-mode `DisjointMut` data-race unsoundness.

---

## Applicability

This report covers verification toolchains, arithmetic/bounds disciplines, relational equivalence contracts, and modular proof decomposition across the 12 primary subjects in `REPORT.json`:

- **Rust & C-Transpiled Formal Verifiers:** `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`theory/Anneal/PureLift/{PermTree,SpatialPin,BlockCfg,MirBridge}.lean`, `trusted/audit/TrustedBoundary.lean`), `google/wuffs@a87f0bb85b9406d29f48a1c03b6f42c4585145f6` (`doc/note/{bounds-checking,interval-arithmetic}.md`, `std/jpeg/{common_consts,decode_jpeg,decode_idct_default,decode_idct_x86_avx2}.wuffs`), `verus-lang/verus@0dab219272ac2353320bd177ebb3929453b90a9e` (`DOI: 10.1145/3586037`), `secure-foundations/vest@026867a37d4b918153058df2c8db6c52fc62ba35` (`README.md`, `vest_tests/src/bits.vest`, USENIX Security '25), `project-everest/everparse@f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`, `model-checking/kani@0601bc57f00a5b7f4d8fb4dd76acd6ec9355227a` (`DOI: 10.1145/3832783.3834499`), `flux-rs/flux@ac24831e4f3dc570ad991751ff65bea0826ed446` (`DOI: 10.1145/3591283`), and `AeneasVerif/aeneas@2e3d4488280bb8a95411db81019a7854a784861f` (`DOI: 10.1145/3547647`).
- **Media DSP & Concurrency Targets:** `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (`libavcodec/{h264idct_template,simple_idct_template,bit_depth_template}.c`, `libavutil/internal.h`), `xiph/opus@31b4b36284394b66a4c9d7352991aa977dfc8bc1` (`celt/fixed_generic.h`, `celt/mdct.c`), `memorysafety/rav1d@2e7216c20ac2a75de204d6c8d7268b75a45959b4` (`src/disjoint_mut.rs`), and `ISO/IEC 23002-1` / `ISO/IEC 23002-2:2008`.

Related corpus analyses cover `SafeTwin` terminal/unwind loopholes and `BiAlign` alignment ([`safe-twin-observational-equivalence-unwind-and-constant-time-alignment`](../safe-twin-observational-equivalence-unwind-and-constant-time-alignment/REPORT.md)), entropy-decoder memory-safety failures ([`entropy-coded-media-bitstreams-video-codec-security-and-simd-decoders`](../entropy-coded-media-bitstreams-video-codec-security-and-simd-decoders/REPORT.md)), `EverParse`/`LowParse` prefix lenses ([`everparse-lowparse-strong-prefix-clens-and-nonmalleable-zero-copy-codecs`](../everparse-lowparse-strong-prefix-clens-and-nonmalleable-zero-copy-codecs/REPORT.md)), `Opus`/`FLAC` fixed-point bounds ([`webrtc-neteq-jitter-buffers-opus-silk-celt-hybrids-and-flac-lpc-overflows`](../webrtc-neteq-jitter-buffers-opus-silk-celt-hybrids-and-flac-lpc-overflows/REPORT.md)), SIMD `stdarch` contracts ([`vendor-intrinsic-specifications-stdarch-verification-and-lean-generation`](../vendor-intrinsic-specifications-stdarch-verification-and-lean-generation/REPORT.md)), and `core::simd` UB ([`core-simd-mask-all-ones-ub-masked-tail-loads-and-lanewise-chunk-algebras`](../core-simd-mask-all-ones-ub-masked-tail-loads-and-lanewise-chunk-algebras/REPORT.md)).

---

## Findings

### 1. Verification Tooling Matrix Across the Media Codec Priority Stack

Basis: source (`joshlf/anneal@c131b320`, `google/wuffs@a87f0bb8`, `secure-foundations/vest@026867a3`, `model-checking/kani@0601bc57`, `flux-rs/flux@ac24831e`, `AeneasVerif/aeneas@2e3d4488`) + documentation (`verus`, `everparse`) + derived.

Each verifier occupies a sharply bounded sweet spot across the four-tier media verification hierarchy—`(1)` UB-freedom, `(2)` panic/overflow-freedom, `(3)` SIMD-vs-scalar/reference equivalence, and `(4)` full functional specification conformance:

| Tool / Framework | Trusted Computing Base (TCB) | Verification Paradigm & Scaling | `unsafe` / SIMD Support | Best Media Codec Subsystems | Critical Gaps / Non-Fits |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`Google Wuffs`** (`google/wuffs@a87f0bb8`) | Go transpiler, interval/fact checker, downstream C compiler | Flow-sensitive facts + integer interval arithmetic (`0` SMT solver; sub-second checks) | Intrinsics typed (`x86_avx2`, `arm_neon`), **`choose` variants NOT proven equivalent** | Entropy bit-readers, Huffman/LZW decoders, bounded JPEG/PNG/WebP loops | Requires writing Wuffs DSL (transpiles to C, not Rust); rejects dynamic heap allocation (`3.2 MiB` static WebP LUTs) |
| **`Flux`** (`flux-rs/flux@ac24831e`) | `rustc` MIR hooks, Z3 SMT solver, liquid type inference | Liquid refinement types directly on Rust (`&[T][@n]`, `usize{v: v < n}`) | Safe Rust + trusted `unsafe` boundary specs | Bounds-check & overflow panic-freedom (`Priority 2`) in Rust bitstreams, DPB indices | SMT instability on nonlinear bitmasks/crypto; no raw pointer separation logic or asm equivalence |
| **`Vest` / `EverParse`** (`vest@026867a3`, `everparse@f3e4ce51`) | `Vest`: Verus + Z3; DSL compiler unverified (`README.md:32`). `EverParse`: F* + Z3 + KaRaMeL | Verified byte/bitfield parser & serializer combinators (non-malleable bijections) | Generated safe Rust (`Vest`) or C (`LowParse`) | Container demuxers (`ISOBMFF`, `Matroska`, `RIFF`), RTP/RTCP, `SPS`/`PPS`/`OBU` headers | Cannot model stateful adaptive entropy coding (`CABAC`, `MSAC`, `rANS`) or LUT synthesis |
| **`Verus`** (`verus-lang/verus@0dab2192`) | Verus linearity checker, VIR translator, Z3 SMT | Linear ghost types, `exec`/`proof`/`spec` modes (`10.1145/3586037`) | Ghost `Ptr`/`PointsTo` raw pointer & slice specs | Concurrent queues, verified ring/arena allocators, `Vest` combinator backends | Z3 quantifier flakiness on deep nested FFT/IDCT arithmetic without careful nonlinear-arith fuel |
| **`Kani`** (`model-checking/kani@0601bc57`) | `rustc` MIR, CBMC bounded model checker, CaDiCaL/MiniSat SAT | Bit-precise bounded symbolic execution (`kani::any()`, function contracts) | Verifies `unsafe` raw pointers, `std::arch` intrinsics (via stubs), FFI shims | `unsafe` C-ABI `AVPacket`/`AVBufferRef` wrappers, single-stage `8×8` IDCT/butterfly UB checks | Path/SAT explosion on unbounded loops (`n > 64`), multi-stage `N=960` FFTs, or whole-frame decoders |
| **`Aeneas`** (`AeneasVerif/aeneas@2e3d4488`) | OCaml Charon (`rustc` MIR $\to$ LLBC) + Aeneas translator; Lean/F*/HOL4 kernel | Pure functional extraction from safe Rust borrow lifetimes (`10.1145/3547647`, `10.1145/3674640`) | **Unsupported** (`README.md:137-140`: no `unsafe`, no concurrency) | Pure functional math models, DPB state transitions, scalar reference codecs | Rejects `unsafe` SIMD, multi-level loop `break`/`continue` to outer labels, and `id(&mut x)` generics (`README.md:128-136`) |
| **`Anneal` (`PureLift` + `SafeTwin`)** (`joshlf/anneal@c131b320`) | `Trusted.MirAst`, `Trusted.MirSemantics`, `rustc-capture` (`Runtime(PostCleanup)` MIR), 3-axiom Lean 4 kernel (`TrustedBoundary.lean:80-105`) | Constructive `PureLift` (`PermTree`, `SpatialPin`, `BlockCfg`) + statement-origin-separated `TotalSafeTwinEquiv` | Models `unsafe` pointer/spatial blocks (`SpatialPin`) and `BiAlign` SIMD-vs-scalar twins | End-to-end Rust codec kernels (`Priority 1+2+3`): UB-free spatial tiles, panic-free fixed-point DSP, SIMD/asm equivalence | Higher manual Lean proof authoring cost on complex `unsafe` kernels; `TerminatorKind.call` support evolving at pinned commit |

### 2. Zero-Panic Container, Bitfield, and Bitstream Parsing (`Vest`, `EverParse`, `Wuffs`, `Flux`)

Basis: source (`secure-foundations/vest@026867a3`: `README.md:10-33`, `vest_tests/src/bits.vest:1-56`; `google/wuffs@a87f0bb8`: `doc/note/bounds-checking.md:1-45`, `doc/note/interval-arithmetic.md:1-133`; `flux-rs/flux@ac24831e`: `README.md:5`) + documentation (`EverParse`).

A media demuxer + decoder faces two structurally opposite parsing regimes:

1. **Structural Framing and Cross-Byte Bitfields (`EverParse` / `Vest`):**
   `Vest` (`README.md:16-24`, USENIX Security '25) natively expresses dependent byte layouts, tagged choices, and cross-byte bitfields in `.vest` schemas. In `vest_tests/src/bits.vest:8-35`:
   ```text
   cross_byte_span = bits { prefix: u3, span: u10, suffix: u3 }
   choice_packet = {
       @hdr: packet_header,
       payload: choose(@hdr.kind) { Raw => [u8; @hdr.len], Words => [u16; @hdr.count], ... },
   }
   ```
   `Vest` emits safe Rust calling `vest_lib` combinators whose Verus proofs guarantee memory safety, integer overflow freedom, termination, and round-trip non-malleability (`parse` $\circ$ `serialize` = identity) at throughput matching handwritten C/Rust. **TCB Boundary (`vest/README.md:32`):** The `.vest` and ASN.1 compilers themselves are *not* verified; security relies on Verus checking the generated Rust code directly (unlike `EverParse`'s verified F* `LowParse` combinator semantics).
2. **Stateful Sub-Bit Entropy Decoding (`Wuffs` Intervals vs. `Flux` Refinements):**
   Container framing (`MP4` boxes, `WebM` EBML, `AV1` OBUs) stops at compressed entropy payloads (`DEFLATE`, `CABAC`, `MSAC`, `rANS`). There, bit-window refills, ring-buffer masks (`& 0xFF`), and dynamic Huffman/CDF tables require **interval bounds + flow-sensitive facts** rather than declarative TLV combinators:
   - **`Wuffs` (`doc/note/bounds-checking.md:1-34`, `doc/note/interval-arithmetic.md:19-125`):** Unifies array-index bounds, arithmetic overflow (`m + n` in `base.u8` $\equiv$ indexing a `256`-element array), and non-null checks under one zero-SMT interval engine. Masking (`idx & 1023` or `& 0xFF`) statically narrows intervals to `[0 ..= 1023]` / `[0 ..= 255]`, and `while expr < s.length()` injects loop-body facts (`bounds-checking.md:15`), compiling away 100% of runtime bounds checks (`std/jpeg/decode_jpeg.wuffs:1975-1997`).
   - **`Flux` (`10.1145/3591283`):** Brings the identical refinement-index discipline directly into safe Rust (`fn decode_slice(buf: &[u8]{n: n > 0}, idx: usize{v: v < n})`), eliminating Rust slice-index panics (`Priority 2`) across bitstream readers, Huffman tables, and `assert!`/`unwrap()`-free VLC decoders without leaving Cargo or translating to C.

### 3. Fixed-Point Integer IDCT/MDCT Verification: Adversarial Wrapping vs. Normative Exactness

Basis: normative (`ISO/IEC 23002-1`, `ISO/IEC 23002-2:2008`, `ITU-T H.264` §8.5.12) + source (`FFmpeg/FFmpeg@7ddf7bc8`: `libavcodec/h264idct_template.c:33-142`, `simple_idct_template.c:47-216`, `bit_depth_template.c:47-84`, `libavutil/internal.h:133-141`; `xiph/opus@31b4b362`: `celt/fixed_generic.h:40-89`, `celt/mdct.c:92-103`) + execution.

Fixed-point video/audio transforms illustrate why **normative conformance invariants** (`Priority 4`) cannot be relied upon to discharge **memory/UB invariants** (`Priority 1+2`) on untrusted inputs:

1. **FFmpeg `ff_h264_idct8_add` Signed `int32_t` UB Gap (`h264idct_template.c:69-142`):**
   - In `FFmpeg`, `libavutil/internal.h:133-141` defines `SUINT` as `int` under `#ifdef CHECKED` (so UBSan flags overflows) and `unsigned` in production (so wraparound is defined modulo $2^{32}$). `libavcodec/simple_idct_template.c:112-113, 167-216` consistently casts multiplies and butterfly terms through `(SUINT)` (`MUL(a, b) ((int)((SUINT)(a) * (b)))`).
   - By contrast, inspecting `libavcodec/h264idct_template.c:69-142` alongside `bit_depth_template.c:52` (`dctcoef` = `int32_t` for `BIT_DEPTH > 8`, `int16_t` for 8-bit) exposes **explicit signed `int32_t` UB bugs** when `dctcoef` holds arbitrary/corrupted 32-bit values:
     - `line 76`: `block[0] += 32;` executes signed `int32_t` addition (UB for `block[0] > INT32_MAX - 32`).
     - `lines 90-93`: `const int a1 = -block[i+3*8] + (unsigned)block[i+5*8] - ...;` evaluates unary `-block[i+3*8]` in **signed `int32_t`** *before* promoting to `unsigned`, triggering C UB at `block[24] == INT32_MIN` (`-2147483648`). Remarkably, the second loop at `line 121` writes `-(unsigned)block[3+i*8]` (avoiding UB!), proving the first loop's missing `(unsigned)` cast is an unpatched coding oversight!
     - On compliant bitstreams (`ITU-T H.264` §8.5.12 bounds $|c_{i,j}| \le 2^{7+\text{BitDepth}}-1$), our probe (`Part A`) proves Pass 2 magnitudes reach at most `1,149,373` (8-bit), `4,597,693` (10-bit), `18,390,973` (12-bit), and `73,564,093` (14-bit), all comfortably below `INT32_MAX = 2,147,483,647`. Yet a malformed Rust/C decoder receiving out-of-range coefficients from corrupted dequantization or unverified callers must use **explicit `wrapping_*` arithmetic** (`Priority 1+2`) *plus* separate normative range preconditions to prove absence of wrap (`Priority 4`).
2. **`ISO/IEC 23002-1` / `23002-2:2008` and `simple_idct_template.c:47-109` Precision Trade-Offs:**
   Withdrawn `IEEE 1180-1990` and its replacement `ISO/IEC 23002-1` define statistical accuracy bounds (peak error, MSE, drift) rather than bit-exactness, whereas `ISO/IEC 23002-2:2008` specifies a bit-exact fixed-point $8\times 8$ reference IDCT. In `simple_idct_template.c:47-109`, FFmpeg selects `ROW_SHIFT` / `COL_SHIFT` / `DC_SHIFT` per `BIT_DEPTH` (`11/20/3` at 8-bit; `13/15/1` at 16-bit with mandatory `IN_IDCT_DEPTH == 32` guard at lines `76-78`) to prevent 32-bit intermediate overflow while minimizing truncation error—an invariant directly expressible as a linear interval proof over `i32`/`i64` intermediates.
3. **Opus `MULT32_32_Q31` 64-Bit vs. 32-Bit Split Drift (`celt/fixed_generic.h:68-72`):**
   On 64-bit targets (`OPUS_FAST_INT64`), `MULT32_32_Q31(a, b)` computes `((int64_t)a * (int64_t)b) >> 31`, whereas the 32-bit fallback (`line 71`) drops the `(a_lo * b_lo) >> 31` low×low product and both sub-carry bits across `>> 15` splits. Across `100,000` random Q31 pairs (`Part C`), the 32-bit split under-estimates the exact 64-bit Q31 product by **`0` (`21.2%`), `1` (`58.9%`), `2` (`18.8%`), or `3` (`1.1%`) ULPs**. Thus, proving exact equivalence (`Priority 3`) between a `64`-bit scalar reference and a `32`-bit SIMD lane requires either computing exact 64-bit carries (`VPMULDQ`) or explicitly relaxing the relational contract to a bounded ULP envelope rather than equality.

### 4. Relational SIMD-vs-Scalar Equivalence Under Tiny TCBs (`SafeTwin` vs. `Wuffs` AVX2 IDCT)

Basis: source (`google/wuffs@a87f0bb8`: `std/jpeg/common_consts.wuffs:38-112`, `decode_jpeg.wuffs:527-529`, `decode_idct_default.wuffs:154-224, 1670-1698`, `decode_idct_x86_avx2.wuffs:230-265, 293-315, 341-447, 560-571, 690-856`; `joshlf/anneal@c131b320`: `trusted/audit/TrustedBoundary.lean:80-105`) + execution.

`Wuffs` proves memory safety and arithmetic bounds (`Priority 1+2`) independently for `decode_idct_default` (`decode_idct_default.wuffs`) and its CPU-dispatched SIMD variant `decode_idct_x86_avx2` (`decode_jpeg.wuffs:527-529`), **without proving relational equivalence between them**. Auditing both functions side-by-side and executing a faithful 8×8 simulation reveals:

1. **Exact Modular Algebra Under In-Range Inputs:** Loeffler's 3-multiply rotation in `decode_idct_default.wuffs:158-160` (`ca = (bq2 + bq6) * 0x1151; cb2 = ca + bq2 * 0x187E; cb6 = ca - bq6 * 0x3B21`) is algebraically identical modulo $2^{32}$ to AVX2's `VPMADDWD` (`decode_idct_x86_avx2.wuffs:389-390`) using packed constants `k_29CF_1151_D630_1151` (`0x1151 + 0x187E = 0x29CF`, `0x1151 - 0x3B21 = -0x29D0 = 0xD630` in `i16`). Across `5,000` random blocks whose dequantized products satisfy `|c * q| <= 32767` and pixel deltas lie in `[-512, 511]`, our probe observed **`0 / 5,000` pixel mismatches**.
2. **Two Concrete Scalar-vs-AVX2 Divergences (`255` Pixel Levels):**
   - **Divergence 1 — 16-bit Dequantization Wrap (`decode_idct_x86_avx2.wuffs:295, 341-344` vs `decode_idct_default.wuffs:154-167`):** Scalar widens coefficients to `base.u32` before multiplying (`~mod*`), whereas AVX2 uses `rows01._mm256_mullo_epi16(b: quants01)`, truncating `c * q` modulo $2^{16}$ as signed `i16`. On a valid baseline-JPEG (`SOF0`) coefficient $c = 200 \in [-1023, 1023]$ and quantizer $q = 200 \in [1, 255]$, scalar computes $+40,000$ while AVX2 wraps to $-25,536$, inverting the cosine polarity across column 0 (`[255, 0, 255, 0, 0, 255, 0, 255]` vs `[0, 0, 255, 255, 255, 255, 0, 0]`, `255`-level error).
   - **Divergence 2 — Modulo-1024 LUT Wrap vs. Saturating Pack (`common_consts.wuffs:38-112`, `decode_idct_default.wuffs:1670-1677` vs `decode_idct_x86_avx2.wuffs:562-571, 809, 847-848`):** Scalar bounds-proofs its final clamp using `BIAS_AND_CLAMP[(val >> 18) & 1023]`, which clamps only `[-512, +511]` (`common_consts.wuffs:38-39`) and **wraps modulo `1024`** (`+512 -> 0`, `-513 -> 255`) outside that band! By contrast, AVX2 uses `_mm256_packs_epi32` + `_mm256_packs_epi16` + `_mm256_add_epi8(k_8080)`, saturating monotonically across `[-32768, 32767]`. Even with zero `i16` dequantization overflow (`max |c * q| = 1560`), an energetic block produces `row0 = [0, 214, 0, 255, 0, 0, 91, 255]` in scalar vs `[255, 214, 0, 0, 0, 0, 91, 255]` in AVX2 (`255`-level pixel flip at pixels 0 and 3!).
3. **Why `SafeTwin` + `BiAlign` Solves This Under a Tiny TCB:**
   Anneal (`joshlf/anneal@c131b320`, `TrustedBoundary.lean:80-105`) keeps only `MirAst`, `MirSemantics`, `rustc-capture`, and the 3-axiom Lean 4 kernel (`propext`, `Quot.sound`, `Classical.choice`, banning `omega`, `bv_decide`, `native_decide`, `sorry`, `unsafe`, `partial`) inside the TCB. Stating `TotalSafeTwinEquiv` directly over `Trusted.MirSemantics` (`Behavior`, `WellFormed`, `Diverges`) with explicit `ArgRel` preconditions forces every scalar/SIMD gap to surface at proof time: either the SIMD kernel uses `i32` widening (`VPMULLD` / `VPMULHW`) and explicit saturation matching the scalar twin on *all* inputs, or `ArgRel` records the exact bitstream precondition (`|c * q| <= 32767` and `|inter| <= 32767` and `|delta| <= 511`) that the preceding Huffman/parser stage must discharge.

### 5. Modular Proof Decomposition for Whole Codecs via `PureLift` (`PermTree`, `SpatialPin`, `BlockCfg`)

Basis: source (`joshlf/anneal@c131b320`: `theory/Anneal/PureLift/{PermTree,SpatialPin,BlockCfg,MirBridge}.lean`; `memorysafety/rav1d@2e7216c2`: `src/disjoint_mut.rs:28-73`; `AeneasVerif/aeneas@2e3d4488`: `README.md:122-140`) + derived.

Verifying an entire codec via whole-program symbolic execution or monolithic separation logic blows up exponentially in basic blocks and memory regions. Inspecting `joshlf/anneal@c131b320` (`theory/Anneal/PureLift/`) establishes a four-part modular decomposition directly tailored to Rust multimedia pipelines:

1. **Pure Functional Borrow Core (`PermTree.lean:25-58`):** Rather than relying on runtime debug-only slice splitting (`rav1d`'s `DisjointMut`, where `src/disjoint_mut.rs:60-72` disables disjointness checks in release builds on the unsound assumption that data races on provenanceless pixels cannot break Rust/LLVM memory safety), safe Rust control logic, DPB management, and scalar reference transforms lift through `PermTree` (`unborrowed`, `shared loans`, `mutLocked loan`, `mutJoined`, `split entries`), tracking exact disjoint sub-place `&mut` borrows as pure functional updates with zero spatial heaplet boilerplate.
2. **Localized Spatial Pinning for Frame Planes and `zerocopy` Casts (`SpatialPin.lean:19-103`):**
   SIMD transforms, `MaybeUninit` output planes, and `zerocopy` byte-slice casts require pointer-level spatial reasoning, but pure codec locals do not. `SpatialPin` isolates them via three localized transitions:
   - `freezeToSpatialInState`: exports one unborrowed mutable loan into a disjoint `SpatialBlock Val` under a lawful `SpatialCodec` (while leaving `st.loans` pure);
   - `mutateSpatialInState`: mutates only the active macroblock/tile `SpatialBlock` via constructive separation logic (`spatialPointsTo`, `spatialSepConj`, `spatial_frame_law`), using `blocksDisjoint` (`SpatialPin.lean:82-84`) to forbid splitting two blocks backed by the same `originLoan`;
   - `reabsorbFromSpatialInState`: checks `!hasUninitCell` (rejecting partially uninitialized pixel planes) and decodes back to a pure Rust value via the original `pinnedCodec`.
3. **Linear $O(N)$ CFG and Loop Cutpoint Certificates (`BlockCfg.lean:21-90, 584, 779`):**
   Multi-block syntax parsers and filter loops avoid $O(2^B)$ path explosion via `modular_block_cfg_sound`, which discharges one `LocalBlockVC` per basic block, and `runWhileFlowSteps_cutpoint_sound`, which proves loop termination and invariant preservation independently of `fuel` once a `Nat` ranking metric strictly decreases.
4. **Bridging to `Trusted.MirSemantics` and `SafeTwin` (`MirBridge.lean:29-99`):**
   `MirBridge` links `PureLift` plans and loop cutpoints to `Trusted.MirSemantics` (`MirStepsDone`, `MirRunsDone`, `MirRunsFault`, `mir_pure_lift_correspondence_transfer`), enabling a clean split: verify safe scalar codec stages once via `PureLift` (`Priority 1+2+4`), then verify each handwritten SIMD/assembly kernel independently against its safe scalar sibling via `TotalSafeTwinEquiv` + `BiAlign` (`Priority 3`), without ever exposing the scalar proof to SIMD register permutations or the SIMD proof to outer bitstream syntax!

### 6. Execution Probe: H.264 10-Bit Signed Overflow, Wuffs Scalar-vs-AVX2 IDCT Divergence, and Opus Q31 Carry Drift

Basis: execution (standalone three-part DSP probe preserved in Evidence; Python 3.13, `x86_64` Linux).

Executing the standalone three-part DSP probe directly verified the numerical bounds and counterexamples analyzed in Findings 3 and 4:

| Probe Target | Input Regime / Condition | Observed Measurement | Verification Implication |
| :--- | :--- | :--- | :--- |
| **`FFmpeg` `ff_h264_idct8_add`** (`2,000` random + extremal trials) | Normative H.264 §8.5.12 bounds (`8`/`10`/`12`/`14`-bit) | `obs_pass2_max`: `1,149,373` (`8b`), `4,597,693` (`10b`), `18,390,973` (`12b`), `73,564,093` (`14b`); all `fits_i32 = True` | Normative streams stay $> 29\times$ below `INT32_MAX` |
| **`FFmpeg` `ff_h264_idct8_add`** (`BIT_DEPTH > 8` C source) | Adversarial `int32_t` inputs (`0x7ffffff0` at `line 76`; `INT32_MIN` at `line 90`) | `0x7ffffff0 + 32 = 2147483664 > INT32_MAX`; `-(-2147483648)` triggers C signed-overflow UB | Wrapping `wrapping_add` / `(unsigned)` casts required for `Priority 1+2` |
| **`Wuffs` JPEG IDCT Scalar vs AVX2** (`5,000` trials) | Strictly bounded: `|delta| <= 511`, `|c * q| <= 32767` | **`0` / `5,000` pixel mismatches** | Scalar Loeffler and AVX2 `VPMADDWD` agree bit-exact inside bounded domain |
| **`Wuffs` JPEG IDCT CE1** (`coeffs[16]=200, quants[16]=200`) | Valid baseline `SOF0` bounds (`c in [-1023,1023]`, `q in [1,255]`), `c*q = 40000` | Scalar col0: `[255, 0, 255, 0, 0, 255, 0, 255]`; AVX2 col0: `[0, 0, 255, 255, 255, 255, 0, 0]` | `_mm256_mullo_epi16` wraps `40000 -> -25536`; **`255`-level** pixel divergence |
| **`Wuffs` JPEG IDCT CE2** (`max |c * q| = 1560`) | Zero `i16` overflow; 2D delta outside `[-512, 511]` | Scalar row0: `[0, 214, 0, 255, 0, 0, 91, 255]`; AVX2 row0: `[255, 214, 0, 0, 0, 0, 91, 255]` | `BIAS_AND_CLAMP[... & 1023]` wraps vs AVX2 saturation; **`255`-level** flip |
| **`Opus` `MULT32_32_Q31`** (`100,000` random Q31 pairs) | `OPUS_FAST_INT64` vs. 32-bit split (`fixed_generic.h:68-72`) | `q64 - q32_split` histogram: `{0: 21183, 1: 58919, 2: 18762, 3: 1136}` ULPs | 32-bit split omits cross-carries (`0..3` ULP negative bias in `78.8%` of pairs) |

---

## Boundaries

- **Known not to apply:**
  - *Bounds proofs $\not\Rightarrow$ cross-ISA equivalence:* Proving absence of out-of-bounds reads and integer UB (as Wuffs achieves) does **not** ensure scalar and SIMD kernels agree on all valid inputs, as proven by both `CE1` and `CE2`.
  - *`Aeneas` on `unsafe` SIMD or multi-level loop exits:* `AeneasVerif/aeneas@2e3d4488` (`README.md:128-140`) explicitly excludes `unsafe` code, concurrency, nested-loop outer `break`/`continue`/`return`, and `&mut` generic trait instantiation.
  - *`Kani` on uncontracted unbounded codecs:* Applying CBMC bounded model checking directly to whole-frame entropy loops or `N=960` multi-stage MDCTs without loop invariants or modular function contracts hits SAT/unwinding blowup.
  - *`SUINT` wrapping vs. mathematical correctness:* Casting through `SUINT`/`wrapping_add` eliminates C/Rust signed-overflow UB (`Priority 1`) without proving that valid bitstreams stay free of silent modular wraparound (`Priority 4`).
- **Not examined:**
  - Formal mechanized Lean 4 kernel execution of the `Wuffs` JPEG IDCT counterexample inside Anneal's `MirWp` / `PureLift` tactic engine (all Anneal theorems cited here were verified by direct source inspection of `joshlf/anneal@c131b320`, and all numerical counterexamples were executed via Python 3).
  - Automated SMT solver runtime benchmarks comparing `Verus`, `Flux`, and `EverParse` across full ISOBMFF/Matroska container schemas beyond primary documentation and test suites.
- **Unknown:**
  - Whether upstream `google/wuffs` intends `choose decode_idct = [decode_idct_x86_avx2]` (`decode_jpeg.wuffs:527-529`) to treat out-of-range `SOF0` coefficients (`|c * q| > 32767` or `|delta| > 511`) as unspecified implementation-defined pixels or as a latent discrepancy bug.
- **Unsupported:**
  - Unverified third-party C/assembly ISA instructions or `TerminatorKind.call` to unmodeled external FFI inside `Trusted.MirSemantics` at `joshlf/anneal@c131b320` without explicit ISA semantics or `SafeTwin` axioms.

---

## Evidence

### Pinned Upstream Artifacts and Specifications Inspected

| Subject | Pinned Identity | Verified Files & Citations |
| :--- | :--- | :--- |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `theory/Anneal/PureLift/{PermTree.lean:25-58, SpatialPin.lean:19-103, BlockCfg.lean:21-90,584,779, MirBridge.lean:29-99}`, `trusted/audit/TrustedBoundary.lean:80-105, 1134-1206, 1661-1722` |
| `google/wuffs` | `a87f0bb85b9406d29f48a1c03b6f42c4585145f6` | `doc/note/{bounds-checking.md:1-45, interval-arithmetic.md:1-133}`, `std/jpeg/{common_consts.wuffs:38-112, decode_jpeg.wuffs:527-529,1975-1997, decode_idct_default.wuffs:100-224,1670-1698, decode_idct_x86_avx2.wuffs:230-265,293-315,341-447,560-571,690-856}` |
| `verus-lang/verus` | `0dab219272ac2353320bd177ebb3929453b90a9e` | `DOI: 10.1145/3586037` (*Verus: Verifying Rust Programs using Linear Ghost Types*) |
| `secure-foundations/vest` | `026867a37d4b918153058df2c8db6c52fc62ba35` | `README.md:10-33`, `vest_tests/src/bits.vest:1-56`, USENIX Security '25 (`pages 6917-6935`) |
| `project-everest/everparse` | `f3e4ce51d9b68593fd98472cadcdeb8b6abf388f` | Repository revision pin; `EverParse` `LowParse`/`3D` byte-aligned combinators |
| `model-checking/kani` | `0601bc57f00a5b7f4d8fb4dd76acd6ec9355227a` | `README.md:5-80`, `DOI: 10.1145/3832783.3834499` (ASE '26) |
| `flux-rs/flux` | `ac24831e4f3dc570ad991751ff65bea0826ed446` | `README.md:5`, `DOI: 10.1145/3591283` (PLDI '23) |
| `AeneasVerif/aeneas` | `2e3d4488280bb8a95411db81019a7854a784861f` | `README.md:14-18, 122-140, 206-211`, `DOI: 10.1145/3547647` (ICFP '22), `DOI: 10.1145/3674640` (ICFP '24) |
| `FFmpeg/FFmpeg` | `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` | `libavutil/internal.h:133-141`, `libavcodec/{bit_depth_template.c:47-84, h264idct_template.c:33-142, simple_idct_template.c:47-216}` |
| `xiph/opus` | `31b4b36284394b66a4c9d7352991aa977dfc8bc1` | `celt/fixed_generic.h:40-89`, `celt/mdct.c:92-103` |
| `memorysafety/rav1d` | `2e7216c20ac2a75de204d6c8d7268b75a45959b4` | `src/disjoint_mut.rs:28-73` |

### Standalone Reproducible DSP Bounds and SIMD Equivalence Probe

Save as `/tmp/probe_dsp_bounds_and_simd_equiv.py` and run `python3 /tmp/probe_dsp_bounds_and_simd_equiv.py` (Python 3.10+ stdlib only):

```python
#!/usr/bin/env python3
"""Standalone probe for fixed-point media DSP arithmetic & SIMD/scalar equivalence."""
import random

MASK16, MASK32 = 0xFFFF, 0xFFFFFFFF

def s16(x: int) -> int:
    x &= MASK16
    return x - 0x10000 if x >= 0x8000 else x

def s32(x: int) -> int:
    x &= MASK32
    return x - 0x100000000 if x >= 0x80000000 else x

def sat_i16(x: int) -> int:
    return -32768 if x < -32768 else (32767 if x > 32767 else x)

def sat_i8(x: int) -> int:
    return -128 if x < -128 else (127 if x > 127 else x)

def wuffs_bias_and_clamp(idx: int) -> int:
    v = idx & 1023
    if v < 128: return 128 + v
    if v < 512: return 255
    if v < 896: return 0
    return v - 896

def h264_idct8_1d_exact_max(max_abs_in: int) -> tuple[int, int]:
    rng = random.Random(101)
    p1_max, p2_max = 0, 0
    for trial in range(2000):
        blk = [rng.choice([-max_abs_in, max_abs_in]) if trial < 500 else rng.randint(-max_abs_in, max_abs_in) for _ in range(64)]
        blk[0] += 32
        for i in range(8):
            a0, a2 = blk[i] + blk[i+32], blk[i] - blk[i+32]
            a4, a6 = (blk[i+16]>>1) - blk[i+48], (blk[i+48]>>1) + blk[i+16]
            b0, b2, b4, b6 = a0+a6, a2+a4, a2-a4, a0-a6
            a1 = -blk[i+24] + blk[i+40] - blk[i+56] - (blk[i+56]>>1)
            a3 =  blk[i+8]  + blk[i+56] - blk[i+24] - (blk[i+24]>>1)
            a5 = -blk[i+8]  + blk[i+56] + blk[i+40] + (blk[i+40]>>1)
            a7 =  blk[i+24] + blk[i+40] + blk[i+8]  + (blk[i+8]>>1)
            b1, b3, b5, b7 = (a7>>2)+a1, a3+(a5>>2), (a3>>2)-a5, a7-(a1>>2)
            for r, v in enumerate((b0+b7, b0-b7, b2+b5, b2-b5, b4+b3, b4-b3, b6+b1, b6-b1)):
                p1_max = max(p1_max, abs(v))
                blk[i + r*8] = v
        for i in range(8):
            o = i*8
            a0, a2 = blk[o] + blk[o+4], blk[o] - blk[o+4]
            a4, a6 = (blk[o+2]>>1) - blk[o+6], (blk[o+6]>>1) + blk[o+2]
            b0, b2, b4, b6 = a0+a6, a2+a4, a2-a4, a0-a6
            a1 = -blk[o+3] + blk[o+5] - blk[o+7] - (blk[o+7]>>1)
            a3 =  blk[o+1] + blk[o+7] - blk[o+3] - (blk[o+3]>>1)
            a5 = -blk[o+1] + blk[o+7] + blk[o+5] + (blk[o+5]>>1)
            a7 =  blk[o+3] + blk[o+5] + blk[o+1] + (blk[o+1]>>1)
            b1, b3, b5, b7 = (a7>>2)+a1, a3+(a5>>2), (a3>>2)-a5, a7-(a1>>2)
            for v in (b0+b7, b0-b7, b2+b5, b2-b5, b4+b3, b4-b3, b6+b1, b6-b1):
                p2_max = max(p2_max, abs(v))
    return p1_max, p2_max

def wuffs_scalar_1d_u32(v: list[int]) -> list[int]:
    b0, b1, b2, b3, b4, b5, b6, b7 = [x & MASK32 for x in v]
    ca = ((b2 + b6) * 0x1151) & MASK32
    cb2, cb6 = (ca + b2 * 0x187E) & MASK32, (ca - b6 * 0x3B21) & MASK32
    ccp, ccm = ((b0 + b4) << 13) & MASK32, ((b0 - b4) << 13) & MASK32
    cd0, cd1, cd2, cd3 = (ccp+cb2)&MASK32, (ccm+cb6)&MASK32, (ccm-cb6)&MASK32, (ccp-cb2)&MASK32
    ci51, ci53, ci71, ci73 = (b5+b1)&MASK32, (b5+b3)&MASK32, (b7+b1)&MASK32, (b7+b3)&MASK32
    cj = ((ci73 + ci51) * 0x25A1) & MASK32
    ck1, ck3, ck5, ck7 = (b1*0x300B)&MASK32, (b3*0x6254)&MASK32, (b5*0x41B3)&MASK32, (b7*0x098E)&MASK32
    ci51, ci53 = (ci51*0xFFFFF384)&MASK32, (ci53*0xFFFFADFD)&MASK32
    ci71, ci73 = (ci71*0xFFFFE333)&MASK32, (ci73*0xFFFFC13B)&MASK32
    cl51, cl73 = (ci51+cj)&MASK32, (ci73+cj)&MASK32
    ck1, ck3 = (ck1+ci71+cl51)&MASK32, (ck3+ci53+cl73)&MASK32
    ck5, ck7 = (ck5+ci53+cl51)&MASK32, (ck7+ci71+cl73)&MASK32
    return [(cd0+ck1)&MASK32, (cd1+ck3)&MASK32, (cd2+ck5)&MASK32, (cd3+ck7)&MASK32,
            (cd3-ck7)&MASK32, (cd2-ck5)&MASK32, (cd1-ck3)&MASK32, (cd0-ck1)&MASK32]

def wuffs_scalar_idct_8x8(coeffs_i16: list[int], quant_u16: list[int]) -> list[int]:
    inter = [0] * 64
    for c in range(8):
        if all(coeffs_i16[r*8 + c] == 0 for r in range(1, 8)):
            dc = ((s16(coeffs_i16[c]) * quant_u16[c]) << 2) & MASK32
            for r in range(8): inter[r*8 + c] = dc
        else:
            out = wuffs_scalar_1d_u32([s16(coeffs_i16[r*8 + c]) * quant_u16[r*8 + c] for r in range(8)])
            for r in range(8): inter[r*8 + c] = (s32((out[r] + 1024) & MASK32) >> 11) & MASK32
    pixels = [0] * 64
    for r in range(8):
        row = inter[r*8 : (r+1)*8]
        if all(row[c] == 0 for c in range(1, 8)):
            px = wuffs_bias_and_clamp((s32((row[0] + 16) & MASK32) >> 5) & 1023)
            for c in range(8): pixels[r*8 + c] = px
        else:
            out = wuffs_scalar_1d_u32(row)
            for c in range(8): pixels[r*8 + c] = wuffs_bias_and_clamp((s32((out[c] + (1<<17)) & MASK32) >> 18) & 1023)
    return pixels

def madd(a: int, ca: int, b: int, cb: int) -> int:
    return s32((s16(a) * s16(ca)) + (s16(b) * s16(cb)))

def wuffs_avx2_1d_i16(v: list[int]) -> list[int]:
    b0, b1, b2, b3, b4, b5, b6, b7 = [s16(x) for x in v]
    cb2, cb6 = madd(b2, 0x29CF, b6, 0x1151), madd(b2, 0x1151, b6, 0xD630)
    ccp, ccm = s32(s16(b0 + b4) << 13), s32(s16(b0 - b4) << 13)
    cd0, cd1, cd2, cd3 = s32(ccp+cb2), s32(ccm+cb6), s32(ccm-cb6), s32(ccp-cb2)
    ci73, ci51 = s16(b7 + b3), s16(b5 + b1)
    cl73, cl51 = madd(ci73, 0xE6DC, ci51, 0x25A1), madd(ci73, 0x25A1, ci51, 0x1925)
    ck7, ck5 = s32(cl73 + madd(b7, 0xECC1, b1, 0xE333)), s32(cl51 + madd(b5, 0xEFB0, b3, 0xADFD))
    ck1, ck3 = s32(cl51 + madd(b1, 0x133E, b7, 0xE333)), s32(cl73 + madd(b3, 0x1051, b5, 0xADFD))
    return [s32(cd0+ck1), s32(cd1+ck3), s32(cd2+ck5), s32(cd3+ck7), s32(cd3-ck7), s32(cd2-ck5), s32(cd1-ck3), s32(cd0-ck1)]

def wuffs_avx2_idct_8x8(coeffs_i16: list[int], quant_u16: list[int]) -> list[int]:
    deq = [s16(s16(c) * s16(q)) for c, q in zip(coeffs_i16, quant_u16)]
    inter = [0] * 64
    if all(coeffs_i16[k] == 0 for k in range(8, 64)):
        for c in range(8):
            dc = s16(deq[c] << 2)
            for r in range(8): inter[r*8 + c] = dc
    else:
        for c in range(8):
            out = wuffs_avx2_1d_i16([deq[r*8 + c] for r in range(8)])
            for r in range(8): inter[r*8 + c] = sat_i16((out[r] + 1024) >> 11)
    pixels = [0] * 64
    for r in range(8):
        out = wuffs_avx2_1d_i16(inter[r*8 : (r+1)*8])
        for c in range(8): pixels[r*8 + c] = (sat_i8(sat_i16((out[c] + (1<<17)) >> 18)) + 128) & 0xFF
    return pixels

if __name__ == "__main__":
    print("[Part A: FFmpeg ff_h264_idct8_add Signed Int32 Range]")
    for bd in (8, 10, 12, 14):
        nb = (1 << (7 + bd)) - 1
        p1, p2 = h264_idct8_1d_exact_max(nb)
        print(f"  BitDepth={bd:2d}: norm_max={nb:8d}  pass1_max={p1:10d}  pass2_max={p2:11d}  fits_i32={p2 < (1<<31)}")
    rng = random.Random(777)
    mismatches = 0
    for _ in range(5000):
        cb = [rng.randint(-4, 4) if k < 16 else 0 for k in range(64)]
        qb = [rng.randint(1, 8) for _ in range(64)]
        if wuffs_scalar_idct_8x8(cb, qb) != wuffs_avx2_idct_8x8(cb, qb):
            mismatches += 1
    c_ce1, q_ce1 = [0]*64, [1]*64; c_ce1[16], q_ce1[16] = 200, 200
    print("[Part B: Wuffs JPEG IDCT Scalar vs AVX2]")
    print(f"  Bounded (N=5000): mismatches={mismatches}")
    print(f"  CE1 (200*200=40000): scalar_col0={[wuffs_scalar_idct_8x8(c_ce1,q_ce1)[r*8] for r in range(8)]} vs avx2_col0={[wuffs_avx2_idct_8x8(c_ce1,q_ce1)[r*8] for r in range(8)]}")
    rng2 = random.Random(777)
    c_ce2, q_ce2 = [rng2.randint(-40,40) if k<16 else 0 for k in range(64)], [rng2.randint(1,64) for _ in range(64)]
    print(f"  CE2 (BIAS_AND_CLAMP wrap): scalar_row0={wuffs_scalar_idct_8x8(c_ce2,q_ce2)[:8]} vs avx2_row0={wuffs_avx2_idct_8x8(c_ce2,q_ce2)[:8]}")
    rng3 = random.Random(3131)
    diffs = []
    for _ in range(100000):
        a, b = rng3.randint(-(1<<31), (1<<31)-1), rng3.randint(-(1<<31), (1<<31)-1)
        if a == -(1<<31) and b == -(1<<31): continue
        diffs.append(((a*b)>>31) - (((a>>16)*(b>>16)<<1) + (((a>>16)*(b&0xffff))>>15) + (((b>>16)*(a&0xffff))>>15)))
    print("[Part C: Opus MULT32_32_Q31]", {d: diffs.count(d) for d in sorted(set(diffs))})
```

---

## Revalidation

1. **Re-check `FFmpeg` H.264 10-bit IDCT unary-negation casting and `SUINT` macro definitions:**
   ```bash
   curl -sSL --http1.1 https://raw.githubusercontent.com/FFmpeg/FFmpeg/<NEW_SHA>/libavcodec/h264idct_template.c | sed -n '69,130p'
   curl -sSL --http1.1 https://raw.githubusercontent.com/FFmpeg/FFmpeg/<NEW_SHA>/libavutil/internal.h | grep -n -A8 "SUINT"
   ```
2. **Re-check `Wuffs` JPEG IDCT AVX2 `mullo_epi16` and `BIAS_AND_CLAMP` usage:**
   ```bash
   curl -sSL --http1.1 https://raw.githubusercontent.com/google/wuffs/<NEW_SHA>/std/jpeg/decode_idct_x86_avx2.wuffs | grep -n "mullo_epi16\|packs_epi"
   curl -sSL --http1.1 https://raw.githubusercontent.com/google/wuffs/<NEW_SHA>/std/jpeg/decode_idct_default.wuffs | grep -n "BIAS_AND_CLAMP" | head -n 10
   ```
3. **Re-check `Anneal` `PureLift` exports and `TrustedBoundary` rules (`joshlf/anneal`):**
   ```bash
   grep -n -E "^theorem |^def " theory/Anneal/PureLift/SpatialPin.lean theory/Anneal/PureLift/BlockCfg.lean | head -n 30
   ```
4. **Re-run the standalone DSP bounds and SIMD equivalence probe (`~1.5 s`):**
   ```bash
   python3 /tmp/probe_dsp_bounds_and_simd_equiv.py
   ```
