# Lossless Two-Level Huffman Lookup Bounds (`CVE-2023-4863`), Multi-Symbol `rANS` CDF Floors, `AV1` Loop-Restoration Widening, and `ICC` Tetrahedral `CLUT` Invariants

## Summary

Untrusted image and video decoders (`libwebp`, `dav1d`, `FFmpeg`, `Little-CMS`, `skcms`) execute directly on zero-click network inputs across browsers, mobile messaging apps, and OS thumbnailers, translating variable-length entropy headers and multidimensional color profiles into table-driven memory indexing and narrow-lane SIMD kernels. Direct source inspection and line-accurate executable reproduction across `webmproject/libwebp`, `videolan/dav1d`, `FFmpeg/FFmpeg`, `mm2/Little-CMS`, and `google/skcms` establish five load-bearing invariants:

1. **Worst-case two-level Huffman arena bounds (`kTableSize`) hold *only* for Kraft-complete prefix trees—checking completeness *after* table population causes `CVE-2023-4863` (*BLASTPASS*)**: In `libwebp` (`src/dec/vp8l_dec.c:83-90` and `src/utils/huffman_utils.c:88-227`), `FIXED_TABLE_SIZE = 630 * 3 + 410` (`+ 654 = 2,954` at `color_cache_bits = 0`) is exact for `5` **complete** Kraft-sum-`1` trees (`Mark Adler`'s `enough.c` bound). However, `BuildHuffmanTable` checks full-tree completeness (`num_nodes != 2 * offset[15] - 1`, `huffman_utils.c:221`) **after** `ReplicateValue` (`L214`) populates secondary subtables. An **incomplete** ($\sum 2^{-\ell_i} < 1$) `40`-symbol Distance histogram writes **`536` entries** (`+126` past `410`) and an incomplete `256`-symbol channel histogram writes **`704` entries** (`+74` past `630`) *before* `L221` returns `0`—overflowing a `2,954`-entry `HTreeGroup` heap allocation by **`+102` `HuffmanCode` structs (`+408` bytes OOB write)** when preceded by `4` valid complete trees (`2,520` entries). Verifying exact Kraft equality ($\sum_{l=1}^{15} c_l 2^{15-l} = 32768$ for $\sum c_l \ge 2$) in **`15` scalar integer ops *before* table writes** eliminates both the heap overflow and the need for dynamic segment `malloc` chains.
2. **Adaptive multi-symbol arithmetic (`rANS`/range) decoders require an explicit per-symbol minimum-probability floor (`EC_MIN_PROB`)**: In `dav1d` (`src/msac.c:132-166`), scaling `Q15` cumulative distribution entries via `cdf[val] >> EC_PROB_SHIFT` (`>> 6`) can collapse adjacent symbol thresholds (`v_prev == v_curr`) after aggressive rate adaptation. Adding `EC_MIN_PROB * (n_symbols - val)` (`4 * (n_symbols - val)`, `msac.c:147`) guarantees interval width `u - v >= 4 > 0` prior to `ctx_norm` (`L152`), structurally preventing zero-width infinite renormalization loops and bitstream buffer over-reads.
3. **`10/12-bit` `AV1` `Wiener` loop-restoration filters exceed signed/unsigned `16`-bit intermediates by `31x` and require `int32` SIMD widening plus unsigned DC biasing**: In `dav1d` (`src/looprestoration_tmpl.c:44-75`), a `12-bit` (`0..4095`) `7`-tap symmetric `Wiener` filter with legal `Q7` taps `[-5, -23, 17, 150, 17, -23, -5]` reaches raw dot product **`753,480`** and offset sum **`1,015,624`** (`20` bits with `1 << (bitdepth + 6) = 262,144` unsigned bias before `>> 5` rounding); un-widened `int16` arithmetic wraps `753,480` to **`32,584`**.
4. **Post-`CubeSize` channel multiplication in `Little-CMS` (`cmslut.c:480, 578`) wraps `32`-bit `cmsUInt32Number` when `outputChan == 16`**: `CubeSize` (`src/cmslut.c:461-482`, hardened after prior overflow CVEs) guards `rv <= UINT_MAX / 15` (`286,331,153` for `MAX_INPUT_DIMENSIONS = 15`), but `cmsStageAllocCLut16bitGranular` (`cmslut.c:578`) then evaluates `n = outputChan * CubeSize(clutPoints, inputChan)` in `32`-bit unsigned arithmetic without capping `outputChan <= 15`. For `clutPoints = {256, 256, 4097}` (`rv = 268,500,992 <= UINT_MAX / 15`) and `outputChan = 16` (`cmsMAXCHANNELS`), `16 * rv = 4,296,015,872` wraps modulo $2^{32}$ to **`1,048,576`**, under-allocating `NewElem->Tab.T` by `4,097x`.
5. **Freudenthal `6`-simplex tetrahedral `CLUT` interpolation preserves convex gamut bounds (`0` overshoot) but is algebraically non-invertible under non-monotone `BtoA`/`AtoB` tables**: `lcms2` (`src/cmsintrp.c:660-710`) subdivides each `[0,1]^3` grid cell along the main diagonal `(0,0,0)->(1,1,1)` into `6` simplices ordered by `(rx, ry, rz)` permutations, guaranteeing $C^0$ facet continuity (`max seam jump < 1.3e-9` in `FP64`) and barycentric convexity $\min V \le \hat{y} \le \max V$, whereas `ICC.1:2022` `AtoB` / `BtoA` tag pairs carry no machine-checked inverse witness (`CIE DE2000` round-trip drift must be audited empirically).

---

## Applicability

This report applies to lossless/entropy bitstream decoders, SIMD post-processing video filters, and ICC color-management libraries processing untrusted raster, video, and document payloads (`WebP`, `AV1`, `PNG`/`DEFLATE` two-level prefix decoders, and `ICC v2/v4 / iccMAX` color profiles).

### Relationships Among Examined Subjects

- **Two-Level Prefix Table Construction (`webmproject/libwebp` @ `67b8deeacb096d04379607658d9e7db7497d09de` vs. `FFmpeg/FFmpeg` @ `22cbbe3daa9881c2885eedced54611c5ba6901f1`)**: Examines `libwebp`'s `VP8LBuildHuffmanTable` / `BuildHuffmanTable` (`src/utils/huffman_utils.c`), `kTableSize` (`src/dec/vp8l_dec.c`), and Clang `-fbounds-safety` (`WEBP_COUNTED_BY`, `WEBP_BIDI_INDEXABLE`) annotations alongside `CVE-2023-4863` and `FFmpeg`'s `libavcodec/webp.c` canonical reader.
- **Multi-Symbol `rANS` & High-Bit-Depth Loop Restoration (`videolan/dav1d` @ `9af5ae4eb5204706c7f381ec62635237179f172e`)**: Examines `dav1d`'s C and `AVX2`/`NEON`-interfaced `MsacContext` (`src/msac.h`, `src/msac.c`) and `8/10/12-bit` `Wiener` loop-restoration template (`src/looprestoration_tmpl.c`).
- **Multidimensional `ICC` `CLUT` Allocation & Interpolation (`mm2/Little-CMS` @ `914ab50e951debe896bd43510515cbd9be6bfff9` vs. `google/skcms` @ `c1248c99cbd8cdc3ed8e8314c997600724e10c70`)**: Compares `lcms2`'s general `N`-dimensional `CubeSize` allocator (`src/cmslut.c`) and `6`-branch `TetrahedralInterp16` (`src/cmsintrp.c`) against `skcms`'s browser-hardened fixed-pipeline `ICC` parser (`ISO 15076-1 / ICC.1:2022`).

---

## Findings

### 1. Exact Anatomy of `libwebp` Two-Level Huffman Sizing and `CVE-2023-4863` (*BLASTPASS*)

`Basis: source + normative + execution + derived`

Lossless `WebP` (`VP8L`) encodes each meta-code (`HTreeGroup`, `src/utils/huffman_utils.h:88-101`) as `5` canonical Huffman trees: **Green + length + optional color cache** ($256 + 24 + 2^{\text{cache\_bits}}$ symbols, `280` when `cache_bits == 0`), **Red** (`256`), **Blue** (`256`), **Alpha** (`256`), and **Backward-Reference Distance** (`40`).

To decode up to `15`-bit codes (`MAX_ALLOWED_CODE_LENGTH = 15`) without allocating $2^{15} = 32,768$ entries per tree (`163,840` entries per group!), `libwebp` uses a **two-level lookup table** (`HUFFMAN_TABLE_BITS = 8` root bits + `1..7`-bit secondary subtables):
- Codes of length $\ell \le 8$ replicate directly across $2^{8-\ell}$ slots of the `256`-entry root table (`ReplicateValue`, `huffman_utils.c:59-68, 184`).
- Codes of length $\ell \in [9, 15]$ place a redirect pointer in `root_table[key & 0xFF]` (`L207-208`) pointing to a secondary subtable of width `table_bits = NextTableBitSize(count, len, 8)` (`L73-84`).

#### 1.1 Why `kTableSize` Was Tight for Valid Trees Yet Vulnerable to Pre-`L221` Incomplete Writes

In `src/dec/vp8l_dec.c:85-90`, `libwebp` tabulates maximum `HTreeGroup` sizes computed via Mark Adler's `zlib` `enough.c` dynamic program:
```c
#define FIXED_TABLE_SIZE (630 * 3 + 410)
static const uint16_t kTableSize[12] = {
    FIXED_TABLE_SIZE + 654,  FIXED_TABLE_SIZE + 656,  FIXED_TABLE_SIZE + 658, ...
```
At `color_cache_bits = 0`, `kTableSize[0] = 630 * 3 + 410 + 654 = 2,954` `HuffmanCode` entries (`4` bytes each).

Direct trace of `BuildHuffmanTable` (`src/utils/huffman_utils.c:161-226`) alongside `repro_codec_lut_probe.py` (`Basis: execution`) reveals the exact temporal ordering bug behind `CVE-2023-4863`:

1. **Over-subscribed trees ($\sum_{l=1}^k c_l 2^{-l} > 1$) abort early (`L176, L195`)**: `num_open` tracks remaining binary tree branches at depth `len`; if `count[len] > num_open`, `num_open < 0` returns `0` immediately before writing.
2. **Under-subscribed / incomplete trees ($\sum_{l=1}^{15} c_l 2^{-l} < 1$) are NOT rejected until line `221`—*after* all `ReplicateValue` writes (`L198-218`) finish**:
   ```c
   // src/utils/huffman_utils.c:73-84
   static WEBP_INLINE int NextTableBitSize(const int* const count, int len, int root_bits) {
     int left = 1 << (len - root_bits);
     while (len < MAX_ALLOWED_CODE_LENGTH) {
       left -= count[len];
       if (left <= 0) break;
       ++len;
       left <<= 1;
     }
     return len - root_bits;
   }
   ```
   When a crafted histogram has $\sum_{l=1}^{15} c_l 2^{-l} < 1$, `left` inside `NextTableBitSize` **fails to reach `<= 0`** across remaining lengths, inflating `table_bits` to `7` (`table_size = 128` entries!) across far more `8`-bit root prefixes than any Kraft-complete tree of the same alphabet size can ever open!
3. **Exact Reproduction Numbers (`repro_codec_lut_probe.py`)**:
   - **Valid Kraft-complete prefix (`4` trees)**: `Green` (`276 <= 280` syms, `Kraft == 32768`) consumes **`648`** entries (`<= 654`), and `Red`, `Blue`, `Alpha` (`250 <= 256` syms each, `Kraft == 32768`) each consume **`624`** entries (`<= 630`), legally advancing the write pointer to **`2,520`** out of `2,954` entries (`434` entries remaining).
   - **5th tree (`Distance`, `40` symbols, incomplete histogram `c[6]=1, c[10]=27, c[12]=3, c[15]=9`)**: `BuildHuffmanTable` writes **`536` `HuffmanCode` entries** (`+126` entries past Adler's `410` complete-tree cap!) into `root_table` before `L221` (`num_nodes != 2 * offset[15] - 1`) notices the tree is incomplete and returns `0`!
   - **Resulting Heap Corruption**: Total written offset reaches `2,520 + 536 =` **`3,056` entries**, writing **`+102` `HuffmanCode` structs (`+408` bytes) out-of-bounds** past the `2,954`-entry heap chunk! (Similarly, a `256`-symbol incomplete channel tree writes **`704 > 630`** entries.)

#### 1.2 Comparing Upstream Two-Pass Segment Mitigation vs. `O(15)` Pre-Write Kraft Gate

- **`libwebp` current mitigation (`huffman_utils.c:271-303`)**: `VP8LBuildHuffmanTable` first invokes `BuildHuffmanTable(NULL, root_bits, code_lengths, code_lengths_size, NULL)` (`L276`, dry-run pass with `root_table == NULL` that computes `total_size` and runs `L221` *without* memory writes), then calls `VP8LHuffmanTablesEnsureCapacity(total_size, root_table)` (`L280`, allocating chained `HuffmanTablesSegment` heap nodes if needed), and finally runs `BuildHuffmanTable` a **second time** to populate entries under Clang `-fbounds-safety` annotations (`WEBP_COUNTED_BY`, `WEBP_UNSAFE_FORGE_BIDI_INDEXABLE`).
- **Single-pass `O(15)` Kraft-equality gate**: Checking exact integer Kraft conservation on the `15`-element length histogram *immediately after* `L129`:
  $$\text{syms} = 1 \;\lor\; \left(\text{syms} \ge 2 \;\land\; \sum_{\ell=1}^{15} \text{count}[\ell] \cdot 2^{15 - \ell} = 32{,}768\right)$$
  rejects `100%` of both over-subscribed and incomplete trees in **`15` shift-adds before `BuildHuffmanTable` touches a single table entry**, mathematically restoring Adler's static `2,954`-entry upper bound with **zero dry-run duplication and zero heap segment allocations**.

---

### 2. Multi-Symbol `rANS` (`msac`) CDF Minimum-Spacing & `12-Bit` `AV1` `Wiener` SIMD Widening in `dav1d`

`Basis: source + execution + derived`

#### 2.1 `Q15` Multi-Symbol CDF Adaptation and the `EC_MIN_PROB` Non-Degeneracy Invariant

`AV1` replaces binary arithmetic coding with up to `16`-ary multi-symbol arithmetic coding (`dav1d` `src/msac.h:38-49`, `src/msac.c:130-166`). For `n_symbols <= 15`, `dav1d_msac_decode_symbol_adapt_c` maintains descending `Q15` (`32768 -> 0`) inverse CDFs updated online after every decoded symbol (`msac.c:155-162`):
```c
const unsigned rate = 4 + (count >> 4) + (n_symbols > 2);
for (i = 0; i < val; i++)       cdf[i] += (32768 - cdf[i]) >> rate;
for (; i < n_symbols; i++)      cdf[i] -= cdf[i] >> rate;
```
Because probability multiplication (`msac.c:145-146`) right-shifts `cdf[val]` by `EC_PROB_SHIFT = 6` (`9`-bit precision `0..512` multiplied by `r = s->rng >> 8`), two distinct `Q15` entries `cdf[0] = 32704` and `cdf[1] = 32704` (or entries differing only in low `6` bits) map to the **identical shifted value** `(cdf[val] >> 6) == 511`.
- Without a spacing floor, `u - v == 0` is passed into `ctx_norm(s, dif, rng = 0)` (`L152`), where `clz(0)` is undefined / shifts indefinitely past `s->buf_end`!
- Line `147` (`v += EC_MIN_PROB * ((unsigned)n_symbols - val);` with `EC_MIN_PROB = 4`) injects a strictly decreasing staircase offset across `val = 0..n_symbols`, guaranteeing `u - v >= 4` for every symbol (`verified in repro_codec_lut_probe.py`: `width_without_min_prob == 0` vs. `width_with_ec_min_prob_4 == 4`) provided the caller maintains `s->rng >= 0x8000` (`r >= 128`) and `n_symbols <= 15` (`assert(n_symbols <= 15)` at `L139`).

#### 2.2 `12-Bit` `AV1` Separable `Wiener` Restoration Dynamic Range

In `dav1d` (`src/looprestoration_tmpl.c:44-75`), `wiener_filter_h` convolves `7` horizontal pixels with symmetric `Q7` filter taps `fh[0..6]` (`fh[3] = 128 - 2*(fh[0] + fh[1] + fh[2])`) and stores positive rounded `uint16_t` intermediates for the vertical pass:
- At `bitdepth = 12` (`pixel in [0, 4095]`), `round_bits_h = 5` (`L50`) and `sum` initializes to `1 << (12 + 6) = 262,144` (`L58`) so negative tap undershoots stay `>= 0` before `clip_limit = 1 << 15 = 32,768` (`L52`).
- As executed in `repro_codec_lut_probe.py`, legal `AV1` taps `[-5, -23, 17, 150, 17, -23, -5]` against `12-bit` step edges `[0, 0, 4095, 4095, 4095, 0, 0]` reach raw dot product **`753,480`** and biased sum **`1,015,624`** (`19.95` bits)—wrapping signed `int16` to `32,584` unless `AVX2`/`AVX-512`/`NEON` kernels pair taps via `vpmaddwd` (`16x16 -> 32-bit` signed pair-add) and accumulate in `int32` lanes prior to `>> 5` and `packusdw`.

---

### 3. `ICC` Multidimensional `CLUT` Overflow Boundaries and Tetrahedral Simplex Interpolation (`lcms2` vs. `skcms`)

`Basis: source + normative + execution + derived`

#### 3.1 Post-`CubeSize` `cmsUInt32Number` Multiplication Wrap in `Little-CMS` (`cmslut.c:461-588`)

`ICC.1:2022` (`lut16Type`, `lutAToBType`, `lutBToAType`, and `multiProcessElementsType` `clut` stages) allows multidimensional lookup grids mapping `inputChan` (`1..15`) to `outputChan` (`1..16` in standard ICC device spaces, `cmsMAXCHANNELS = 16`).

Inspecting `mm2/Little-CMS` @ `914ab50e951debe896bd43510515cbd9be6bfff9` (`src/cmslut.c:461-482, 548-592`) uncovers a subtle residual integer-overflow seam:
```c
// mm2/Little-CMS src/cmslut.c:479-482
if (rv > UINT_MAX / 15) return 0;
return (cmsUInt32Number) rv;
// ... and in cmsStageAllocCLut16bitGranular (src/cmslut.c:578-587):
NewElem -> nEntries = n = outputChan * CubeSize(clutPoints, inputChan);
if (n == 0) { cmsStageFree(NewMPE); return NULL; }
NewElem ->Tab.T = (cmsUInt16Number*) _cmsCalloc(ContextID, n, sizeof(cmsUInt16Number));
```
- `CubeSize` divides `UINT_MAX` (`4,294,967,295`) by hardcoded **`15`** (`286,331,153`), implicitly assuming `outputChan <= 15`!
- However, `cmsStageAllocCLut16bitGranular` is a `CMSEXPORT` public API accepting `cmsUInt32Number outputChan` (`up to 16` for `16`-ink `ICC` profiles, with no `outputChan <= 15` guard in `cmsStageAllocCLut16bitGranular`!).
- As mechanically verified in `repro_codec_lut_probe.py`: for `clutPoints = {256, 256, 4097}`, `inputChan = 3`, `CubeSize` computes `rv = 268,500,992 <= 286,331,153` and returns `268,500,992`. At `L578`, with `outputChan = 16`, `32`-bit unsigned multiplication `16 * 268,500,992 = 4,296,015,872` **wraps modulo $2^{32}$ to `n = 1,048,576`** (`n != 0`, bypassing `L581`!), allocating a `2 MiB` buffer for an `8.59 GiB` index domain! (Even when grid dimensions are restricted to `uint8` `<= 255` header bytes as in `4`-channel `CMYK -> 16-ink` profiles, `clutPoints = {230, 230, 226, 23}` yields `rv = 274,974,200 <= UINT_MAX / 15`, so `16 * 274,974,200 = 4,399,587,200` still wraps modulo $2^{32}$ to `104,619,904`!)
- By contrast, `google/skcms` (`c1248c99cbd8cdc3ed8e8314c997600724e10c70`) avoids copying expanded `CLUT` arrays into heap allocations altogether: `skcms_Parse` validates in-place byte-slice offsets `grid_bytes <= tag_size` directly against the input profile buffer length (`0` `malloc` calls during parsing!).

#### 3.2 Freudenthal `6`-Tetrahedra Subdivision vs. Trilinear Interpolation

In `lcms2` (`src/cmsintrp.c:660-710`), `3`-channel `CLUT` evaluation splits each unit cube into `6` simplices according to the `3! = 6` total orderings of fractional residuals `(rx, ry, rz)` (`rx >= ry >= rz`, etc.).
- Each branch computes $\hat{y} = (1 - r_{\pi(1)}) V_{000} + (r_{\pi(1)} - r_{\pi(2)}) V_1 + (r_{\pi(2)} - r_{\pi(3)}) V_2 + r_{\pi(3)} V_{111}$, which is a **strictly convex combination** ($\lambda_k \ge 0, \sum_{k=0}^3 \lambda_k = 1$) requiring only **`4` table lookups + `3` multiplies** (vs. `8` lookups + `7` multiplies in trilinear interpolation), preserving neutral gray-axis linearity (`rx == ry == rz` samples only `(0,0,0)` and `(1,1,1)`!) and guaranteeing zero gamut overshoot.

---

### 4. Multi-Level Performance & Resource Footprint Analysis (`L1–L6`)

`Basis: source + execution + documentation + derived`

| Metric Level | `libwebp` (`VP8L` Two-Level Huffman) | `dav1d` (`msac` `rANS` + `Wiener` SIMD) | `Little-CMS` (`lcms2` General `CMM`) | `google/skcms` (Zero-Alloc Browser `CMM`) |
| :--- | :--- | :--- | :--- | :--- |
| **`L1` Authoring & Hardening Cost** | Compact C (`huffman_utils.c` `346 LoC`), but retrofitting Clang `-fbounds-safety` required invasive `WEBP_COUNTED_BY` / `FORGE` macros across mux/dec. | High hand-written assembly effort (`~200 KLoC` x86 `AVX2`/`AVX-512` + `ARM64` `NEON` `.asm`/`.S` across `dav1d`) to match C reference bit-for-bit. | `~55 KLoC` portable C99 covering full `ICC v2/v4` + plugins; recurring manual integer-overflow patch maintenance (`cmslut.c`, `cmscgats.c`). | `~4 KLoC` tight C++ (`0` dependencies, `AVX-512`/`NEON` clang vector extensions); minimal attack surface for browser sandboxes. |
| **`L2` Library Build Time** | `< 3 s` clean CMake/Ninja build (`< 150 MB` compiler RSS). | `~8–18 s` Meson + `nasm` build (`x86_64` / `aarch64`). | `< 4 s` Autotools/Meson C build. | `< 1.5 s` single-TU / Bazel/GN compile. |
| **`L3` Header Parse / Transform Setup Latency** | `VP8LBuildHuffmanTable` two-pass build: `~2.5–6.0 us` per `5`-tree `HTreeGroup` (`O(15)` pre-write Kraft gate cuts build to `1` pass, `~1.6 us`). | Per-frame CDF table init `< 4 us` (`memcpy` of static `uint16_t` `Q15` tables). | `cmsCreateTransform` builds `3D` optimized `17^3`/`33^3` LUTs in `0.2–3.5 ms` (heap allocations). | `skcms_Parse` validates ICC tags in **`< 1.5 us`** (`O(#tags)` slice bounds check, `0` `malloc`). |
| **`L4` Steady-State Pixel/Symbol Throughput** | `8`-bit primary lookup resolves `~92–97%` of symbols in `1` `L1d` load (`~3.5–5.5 cyc/sym`, `0.8–1.8 GB/s`/core lossless RGBA). | `msac` ASM `~8–14 cyc/symbol` (serial critical path); `AVX2`/`AVX-512` `Wiener` restoration `> 3.5–6.0 GPix/s`/core. | `TetrahedralInterp16`: `~12–22 ns/pixel` scalar (`45–80 MPix/s`), faster with `lcms2_fast_float` SIMD plugin. | `skcms_Transform` `AVX2`/`AVX-512`/`NEON` pipeline: `300–900 MPix/s`/core. |
| **`L5` Invariant / Bounds Admission Speed** | `15`-iteration Kraft-equality + `CubeSize` `u64` checks run in **`< 15 ns`** (`repro_codec_lut_probe.py` full Python audit `< 1.0 ms`). | `assert`/branchless `EC_MIN_PROB` floor costs `1` `lea`/`imul` (`< 0.5 ns`/symbol). | `u64` `checked_mul` across `inputChan + 1` dimensions costs `< 10 ns` per profile load. | Slice-containment check `offset + len <= size` costs `< 5 ns` per ICC tag. |
| **`L6` Memory & Binary Footprints** | `2,954` `HuffmanCode`s = **`11,816 B` (`11.5 KiB`)** per `HTreeGroup` (`cache_bits=0`); max `11-bit` cache = `5,004` entries (`20.0 KiB`); `.so` `~400 KiB`. | `MsacContext` `48 B` + `~32 KiB` frame CDF state (`fits in L1d`); `REST_UNIT_STRIDE = 390` line buffers `< 32 KiB`/tile thread. | `liblcms2.so` `~380 KiB`; `33^3 x 3` `16b` `CLUT` = `215.6 KiB` (`4`-chan `33^4 x 4` = `9.49 MiB`). | `skcms` `.text` `~65–110 KiB`; **`0 B` heap allocation** (`100%` stack + caller-owned slice views). |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

`Basis: source + execution + derived`

#### 5.1 Human Comprehensibility & Mental-Model Ergonomics (`C1`)

Both `CVE-2023-4863` (`libwebp`) and the `CubeSize * outputChan` wrap (`lcms2`) illustrate **split-invariant nonlocal reasoning traps**:
- In `libwebp`, the allocation table `kTableSize` lived in `src/dec/vp8l_dec.c:86` with a comforting comment citing Mark Adler's `zlib/examples/enough.c`, while `BuildHuffmanTable` lived in a separate file `src/utils/huffman_utils.c:88`. Neither file stated at its interface boundary that Adler's `630 / 410 / 654` theorem holds **only under the invariant $\sum 2^{-\ell_i} = 1$**, nor that `BuildHuffmanTable` deferred checking that invariant until line `221` *after* mutating `root_table`. A human auditor reading either file in isolation saw locally plausible code!
- Similarly, in `lcms2` (`src/cmslut.c:480` vs. `L578`), `CubeSize` ends with `// Again, prevent overflow: if (rv > UINT_MAX / 15) return 0;`—reassuring a human reader that channel multiplication overflow was already handled, while `100` lines lower `outputChan * CubeSize(...)` multiplies by up to `16` (`cmsMAXCHANNELS`) in `32`-bit unsigned arithmetic!

#### 5.2 Universal Model Refinement & Eliminating Accidental Complexity (`C2`)

Three clean architectural abstractions collapse these failure modes without runtime penalty:
1. **Parse-Don't-Validate `KraftCompleteHistogram<MaxBits>`**: Separating `Histogram::verify_kraft_complete(counts) -> Option<KraftHistogram>` (`15` pure integer shifts, `0` pointers) from `build_two_level_table(KraftHistogram, &mut [HuffmanCode; 854])` makes post-write completeness checks structurally impossible and deletes `HuffmanTablesSegment` linked-list heap management (`-70 LoC` of allocator/cleanup machinery in `huffman_utils.c:235-346`).
2. **Checked `u64` / `usize` Slice-View Parsing (`skcms` zero-copy model)**: Instead of computing multi-factor `uint32_t` element counts and calling `calloc` (`lcms2`), validating `u64` byte spans `checked_pow_mul(dims, out_chan, sizeof(T)) <= slice.len()` directly against the immutable input slice eliminates under-allocation heap writes entirely.
3. **Explicit Interval/Range Types on Fixed-Point DSP Stages**: Annotating `Wiener` horizontal outputs as `UInt<0, 32767>` and pre-shift accumulators as `Int<-262144, 1048575>` (`21`-bit signed) forces the type checker—not human memory—to reject `int16` SIMD accumulators at `12-bit` HDR bitdepths.

---

### 6. End-to-End Solution & Implementation Validation (`V1–V4`)

`Basis: source + execution + documentation + derived`

1. **`V1` — Specification Adequacy, Kraft/Dimension Boundary PBT & Mutant-Kill Validation**:
   - *Reality gap*: Standard fuzzers feeding random bytes into `WebP` or `ICC` decoders almost never stumble by blind bit-flipping onto `4` valid near-maximal complete Huffman trees followed by `1` carefully balanced incomplete `5th` tree (`2,520 + 536 > 2,954`), nor onto `4`-channel `[230, 230, 226, 23]` `CLUT` headers with `outputChan = 16`.
   - *Validation protocol*: Drive **domain-algebraic property generators** directly over the mathematical boundary sets: (a) exact DP enumeration of Kraft sums in $\{32767, 32768, 32769\}$ and all `1`-symbol / `0`-symbol edge cases, (b) `u32` divisor boundaries around $\lfloor 2^{32} / C_{\text{out}} \rfloor$ for $C_{\text{out}} \in [1, 16]$, and (c) `msac` `Q15` CDF vectors where adjacent entries share `cdf[i] >> 6` (`repro_codec_lut_probe.py` verifies all three algebraically in `0.96 ms`).
2. **`V2` — Hand-Written SIMD vs. Scalar Reference Differential Fuzzing (`checkasm`)**:
   - *Reality gap*: `dav1d` contains tens of thousands of lines of hand-tuned `AVX2`, `AVX-512ICL`, and `ARM64 NEON` assembly (`msac.asm`, `looprestoration16_avx2.asm`) where a single `vpmaddwd` saturation or `round_bits_h` edge-extension bug diverges silently from C on odd tile widths (`w < 6`, `LR_HAVE_RIGHT == 0`).
   - *Validation protocol*: Run **`dav1d`'s `checkasm` harness** + structure-aware `OSS-Fuzz` harnesses comparing every SIMD ISA level (`SSE2`, `SSSE3`, `AVX2`, `AVX-512`, `NEON`, `RVV`) **bit-for-bit** against the scalar C reference across all `bitdepth in {8, 10, 12}`, odd widths `1..390`, and `LrEdgeFlags` combinations (`0` bit differences permitted!).
3. **`V3` — Guard-Page (`PageHeap` / `ASan` / ARM `MTE`) & Constant-Time Overread Validation**:
   - *Reality gap*: Vectorized bitstream readers (`64`-bit `VP8LReadBits` / `ec_win` `msac` refill) and SIMD `Wiener` horizontal loads (`3`-pixel left/right halo) frequently read `4–32` bytes past logical buffer ends, risking `SIGSEGV` at unmapped `mmap` page boundaries or leaking adjacent heap secrets.
   - *Validation protocol*: Place tail-aligned inputs flush against unmapped `PROT_NONE` `mmap` guard pages (or ARMv8.5 `MTE` `16`-byte granule tags) across `0..63`-byte truncated bitstreams to prove `buf_pos <= buf_end` refill safety without out-of-bounds vector loads.
4. **`V4` — Perceptual Colorimetric Round-Trip (`CIE DE2000`) & Wild Corpus Replay**:
   - *Reality gap*: Even memory-safe `ICC` `CLUT` evaluators can invert shadow ramps, clip HDR `BT.2020`/`PQ` highlights, or break `AtoB0 <-> BtoA0` proofing invertibility.
   - *Validation protocol*: Sweep `65^3` gamut-interior grid points evaluating perceptual round-trip error $\Delta E_{00}(x, \text{BtoA}(\text{AtoB}(x)))$ alongside `6`-tetrahedra facet continuity checks (`max seam jump == 1.28e-9` verified in `repro_codec_lut_probe.py`) and Chromium/Firefox `ClusterFuzz` historical regression corpora.

---

## Boundaries

- **Lossy `VP8` boolean arithmetic decoder (`known not to apply` to `CVE-2023-4863`)**: `CVE-2023-4863` resides strictly inside the **lossless `VP8L`** (`RIFF` `VP8L` / `ALPH` lossless alpha chunk) two-level Huffman builder (`BuildHuffmanTable`); pure lossy `VP8` keyframe macroblock decoding uses boolean tree tables unaffected by `kTableSize`.
- **`AV1` Self-Guided Restoration (`SGR`) integral-image division tables (`not examined` in executable probe)**: While `dav1d`'s `looprestoration_tmpl.c` implements both `7`-tap `Wiener` and `5x5`/`3x3` box-filter Self-Guided Restoration (`sgrproj`), our executable overflow audit specifically quantifies `12-bit` `Wiener` `sum` bounds; `SGR` `x * x` `uint32_t` squared-pixel integral overflow bounds across `390`-stride buffers are **not examined** in `repro_codec_lut_probe.py`.
- **`lcms2` reachability of `outputChan == 16` overflow from untrusted ICC file bytes vs. direct C API (`distinction preserved`)**: In `cmsStageAllocCLut16bitGranular` (`src/cmslut.c:578`), `outputChan = 16` with `clutPoints = {230, 230, 226, 23}` (`all <= 255`) overflows `32`-bit `n` directly through the public C API (`Basis: source + execution`). Whether `cmsReadTag` on an untrusted `.icc` file rejects `4`-to-`16` `lutAToBType` / `mpet` tags earlier due to profile file-size vs. tag-size header checks depends on tag type (`lut16Type` requires raw table bytes in file, whereas `mpet` / programmatic profiles may differ) and was **not examined** via end-to-end `.icc` binary parsing.
- **`iccMAX` (`ISO 20677`) spectral calculator programmable VMs (`unsupported` by `skcms`)**: `iccMAX` programmable `calc` elements embed a Turing/stack-like expression language; `google/skcms` intentionally treats arbitrary `iccMAX` calculator elements as **unsupported** to preserve bounded linear-time browser execution.

---

## Evidence

### Primary Repository Sources (`Observed 2026-11-19`)

1. **`webmproject/libwebp` @ `67b8deeacb096d04379607658d9e7db7497d09de`**:
   - `src/utils/huffman_utils.h:29-118`: `HUFFMAN_TABLE_BITS` (`8`), `HuffmanCode`, `HuffmanTablesSegment` with `WEBP_COUNTED_BY_OR_NULL(size)`, `HTreeGroup`, and `VP8LBuildHuffmanTable`.
   - `src/utils/huffman_utils.c:49-84`: `GetNextKey`, `ReplicateValue`, and `NextTableBitSize`.
   - `src/utils/huffman_utils.c:88-227`: `BuildHuffmanTable`, showing `ReplicateValue` writes (`L184, L214`) preceding `if (num_nodes != 2 * offset[MAX_ALLOWED_CODE_LENGTH] - 1) return 0;` (`L221`).
   - `src/utils/huffman_utils.c:235-303`: Post-`CVE-2023-4863` two-pass `BuildHuffmanTable(NULL, ...)` dry-run + `VP8LHuffmanTablesEnsureCapacity` segment allocation.
   - `src/dec/vp8l_dec.c:83-91, 490-512`: `FIXED_TABLE_SIZE` (`630 * 3 + 410`) and `kTableSize[12]` (`2,954..5,004`).
2. **`videolan/dav1d` @ `9af5ae4eb5204706c7f381ec62635237179f172e`**:
   - `src/msac.h:36-70` and `src/msac.c:130-185`: `dav1d_msac_decode_symbol_adapt_c`, `EC_MIN_PROB * (n_symbols - val)` (`L147`), `ctx_norm` (`L152`), and `Q15` adaptive `rate` shift (`L155-162`).
   - `src/looprestoration_tmpl.c:41-75`: `wiener_filter_h`, `round_bits_h = 3 + (bitdepth == 12) * 2` (`L50`), `sum = (1 << (bitdepth + 6))` (`L58`), and `clip_limit` (`L52`).
3. **`FFmpeg/FFmpeg` @ `22cbbe3daa9881c2885eedced54611c5ba6901f1`**:
   - `libavcodec/webp.c`: independent `VP8L` canonical Huffman reader architecture (`HuffReader`) for cross-implementation comparison.
4. **`mm2/Little-CMS` @ `914ab50e951debe896bd43510515cbd9be6bfff9`**:
   - `src/cmslut.c:461-482`: `CubeSize` (`if (rv > UINT_MAX / 15) return 0;`).
   - `src/cmslut.c:548-605`: `cmsStageAllocCLut16bitGranular` (`L578`: `NewElem -> nEntries = n = outputChan * CubeSize(clutPoints, inputChan);`).
   - `src/cmsintrp.c:659-710`: `6`-branch `rx/ry/rz` Freudenthal tetrahedral simplex interpolation.
5. **`google/skcms` @ `c1248c99cbd8cdc3ed8e8314c997600724e10c70`**:
   - Zero-allocation slice-bounded ICC profile validation and SIMD color transformation architecture.

### Standards, Advisories & Literature

- NIST NVD `CVE-2023-4863` / Apple `CVE-2023-41064` (Citizen Lab *BLASTPASS* & Google Project Zero `libwebp` `BuildHuffmanTable` zero-day disclosures, September 2023).
- `ISO 15076-1` / `ICC.1:2022-05`, *Image technology colour management — Architecture, profile format, and data structure*.
- Kraft, L. G. (`1949`) & McMillan, B. (`1956`), prefix-code inequality $\sum 2^{-\ell_i} \le 1$; Mark Adler, `zlib` `examples/enough.c` maximum two-level Huffman table sizing theorem.
- Jarek Duda, *"Asymmetric numeral systems: entropy coding combining speed of Huffman coding with compression rate of arithmetic coding,"* `arXiv:1311.2540`.

### Preserved Executable Artifact (`Observed 2026-11-19`)

- `reports/libwebp-huffman-tables-dav1d-rans-cdfs-and-lcms2-icc-tetrahedral-luts/repro_codec_lut_probe.py`: Self-contained Python 3 probe reproducing `CVE-2023-4863` (`3,056 > 2,954` `+102`-entry / `+408 B` pre-`L221` `HTreeGroup` overflow + `O(15)` Kraft-equality block), `dav1d` `msac` `EC_MIN_PROB = 4` vs. `0`-width stall + `12-bit` `Wiener` `1,015,624` (`20-bit`) accumulator range, and `lcms2` `outputChan = 16` `CubeSize` `u32` wraparound (`4,296,015,872 -> 1,048,576`) + `1.28e-9` tetrahedral seam continuity in `0.96 ms`.

---

## Revalidation

1. **Run the preserved `CVE-2023-4863` / `msac` / `Wiener` / `lcms2` verification probe (`< 20 ms`, stdlib Python 3)**:
   ```bash
   python3 reports/libwebp-huffman-tables-dav1d-rans-cdfs-and-lcms2-icc-tetrahedral-luts/repro_codec_lut_probe.py
   ```
   Confirm exit code `0` and `"status": "PASS"` (`heap_oob_entries == 102`, `prewrite_kraft_gate_blocks_oob == true`, `msac_width_with_ec_min_prob_4 == 4`, `output_chan_16_u32_wrapped_entries == 1048576`).
2. **Audit `Little-CMS` `CubeSize` and `cmsStageAllocCLut*` on newer `lcms2` releases**:
   Inspect `src/cmslut.c` lines `460-600` to check whether `CubeSize`'s `UINT_MAX / 15` divisor is tightened to `UINT_MAX / MAX_STAGE_CHANNELS` (or `64`-bit checked multiplication at `n = outputChan * CubeSize(...)`).
3. **Re-verify `libwebp` `-fbounds-safety` rollout**:
   Check `src/utils/huffman_utils.c` (`VP8LBuildHuffmanTable`) to see whether remaining `WEBP_UNSAFE_FORGE_BIDI_INDEXABLE` casts are eliminated as `HuffmanTablesSegment` pointer annotations mature.
