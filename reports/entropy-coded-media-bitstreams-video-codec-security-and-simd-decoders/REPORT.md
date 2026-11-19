# Stateful Entropy-Coded Media Bitstreams, Codec Memory Safety, and Verified SIMD Decoders

## Summary

Zero-click media codec exploits repeatedly originate in the gap between **stateful, sub-bit entropy decoders** and the **byte-aligned structural parsing models** targeted by mainstream verified parser generators. Five load-bearing technical findings govern the security, expressiveness, and verification boundaries of modern media decoders:

1. **Byte-aligned verified parser combinators (`EverParse`, `Vest`) cannot directly express entropy-coded media payloads.** Combinators built around byte-sliced length-prefixed TLV frames assume stateless or locally dependent byte cursors and non-malleable bijections; entropy coders instead decode fractional bits per symbol (< 1 bit/symbol), mutate cross-symbol probability state (adaptive CDF tables in H.264 CABAC and AV1 MSAC), read backward LIFO stacks (`rANS`/`tANS`), and construct dynamic prefix lookup tables from untrusted code-length histograms.
2. **`libwebp` CVE-2023-4863 (BLASTPASS) was caused by writing 2nd-level Canonical Huffman lookup tables *before* validating Kraft's equality ($\sum 2^{-l_i} = 1$).** In `webmproject/libwebp` `v1.3.1`, `ReadHuffmanCodes()` pre-allocated `kTableSize[color_cache_bits]` entries (`2954` for `color_cache_bits = 0`, `5004` for `11`) sized by Mark Adler's `enough.c` under the precondition of a **complete** canonical Huffman tree. However, `BuildHuffmanTable()` deferred its completeness check (`num_nodes != 2 * offset[MAX_ALLOWED_CODE_LENGTH] - 1`) until *after* writing all 2nd-level tables via `NextTableBitSize()`. On an under-subscribed (`sum < 1`) 40-symbol `DIST` code (`[9, 10, 11, 12, 13, 14] + [15]*34`, Kraft sum $160/32768$), `NextTableBitSize()` falls through to maximum subtable width $2^{15-8} = 128$, writing `512` entries against a `410`-entry budget (`+102` entries / `+408` bytes out-of-bounds) before returning `0`. The `v1.3.2` fix (`2af26267...`) runs a zero-write sizing/validation dry-run (`BuildHuffmanTable(NULL, ...)`) and replaces the fixed flat buffer with chained `HuffmanTablesSegment` slabs; `HEAD` (`eceabea8...`) layers Clang `-fbounds-safety` annotations on top.
3. **Asymmetric Numeral Systems (`rANS`/`tANS`) invert stream directionality (LIFO) and introduce renormalization-interval safety invariants.** `ryg_rans` encodes symbols and emits bytes in reverse order using a single integer state $x \in [L, bL)$ ($L = 2^{23}$), permitting branchless multi-lane interleaving into a shared byte stream (`1.125 bits/sym` measured in a 2-lane probe), but its reference `RansDecAdvance()` lacks an input-EOF guard inside `while (x < RANS_BYTE_L)`, causing unbounded out-of-bounds reads on a zeroed state over zero bytes. `FSE` (`tANS`) eliminates runtime multiplication via a finite-state automaton over a backward bit stream (`BIT_DStream_t`) and enforces table completeness (`position == 0`) at build time.
4. **Google `Wuffs` eliminates buffer overflows and integer arithmetic UB at compile time via non-SMT interval arithmetic and flow-sensitive facts, trading dynamic flexibility for static worst-case footprints.** In `std/deflate/decode_deflate.wuffs`, Wuffs verifies both over-subscription and under-subscription before touching its 2-level table and statically proves every write `< 1024`. In `std/webp/decode_webp.wuffs`, Wuffs eliminates 2-level lookup tables altogether in favor of static $2N - 1$ binary node arrays (`array[256] array[0x187B] base.u16` = `3,208,704` bytes), statically rejecting valid VP8L streams with $>256$ Huffman groups (vs. `65,536` in VP8L).
5. **`rav1d` demonstrates a practical safe-Rust + handwritten-SIMD hybrid, but retains two explicit verification gaps across the FFI/concurrency boundary.** `memorysafety/rav1d` moves AV1 frame parsing, MSAC reference decoding, and loop-filter orchestration into Rust (`#![deny(unsafe_op_in_unsafe_fn)]`) while dispatching `SSE2`/`AVX2`/`AVX512ICL`/`NEON` assembly via unified `wrap_fn_ptr!` + trailing `FFISafe` arguments and defensive return masking (`% 4`, `% 8`, `% 16`). However, (a) assembly safety relies on randomized `checkasm` differential testing rather than formal equivalence, and (b) `DisjointMut<T>` enforces slice-disjointness checks **only in debug mode (`#[cfg(debug_assertions)]`)** while its upstream `SAFETY` comment (`src/disjoint_mut.rs:67-72`) erroneously assumes release-mode data races on provenanceless pixel integers cannot affect memory safety—conflicting with normative Rust/LLVM data-race UB semantics.

## Applicability

This report covers primary source implementations, specifications, and standalone verification probes across five interacting layers of untrusted media bitstream decoding:

- **Canonical Huffman 2-Level Table Builders (`webmproject/libwebp`):** Examines three immutable revisions in direct comparison: vulnerable `v1.3.1` (`fd7bb21c0cb56e8a82e9bfa376164b842f433f3b`), the immediate CVE-2023-4863 security fix commit (`2af26267cdfcb63a88e5c74a85927a12d6ca1d76`, shipped in `v1.3.2`), and `HEAD` (`eceabea8c5f72920c4a4f92724ef2c38bb2d1985`, adding `-fbounds-safety` pointer annotations and `VP8LHuffmanTablesEnsureCapacity`). Applies to VP8L lossless WebP decoding (`HUFFMAN_TABLE_BITS = 8`, `MAX_ALLOWED_CODE_LENGTH = 15`, 5 Huffman trees per meta-code group); lossy VP8 boolean arithmetic decoding is not covered in the `libwebp` source audit.
- **Asymmetric Numeral Systems & Context-Adaptive Arithmetic Coders:** Covers `rygorous/ryg_rans` (`c9d162d996fd600315af9ae8eb89d832576cb32d`, byte-renormalized 32-bit `rANS`), `Cyan4973/FiniteStateEntropy` (`9f30e0918f87bd835fa040d922a208d7b219e50b`, `tANS`/`FSE` decoder), H.264/AVC CABAC (Marpe, Schwarz, Wiegand, IEEE TCSVT 2003), and AV1 Multi-Symbol Arithmetic Coding (`AOMedia AV1 Specification` §8.2 as implemented in `memorysafety/rav1d` `src/msac.rs`).
- **Verified Byte-Aligned TLV Combinators (Contrast Baseline):** Covers `project-everest/everparse` (`270f5aab699ac284d8777d4f01be20a5d91ea47c`, `LowParse`/`3D`/`EverCBOR`) and `secure-foundations/vest` (`026867a37d4b918153058df2c8db6c52fc62ba35`, Verus-verified Rust combinators) to delineate precisely where container/header parsing ends and stateful entropy decoding begins.
- **Compile-Time Interval Bounds Verification (`google/wuffs` @ `a87f0bb85b9406d29f48a1c03b6f42c4585145f6`):** Applies to Wuffs' checker (`lang/check/bounds.go`), DEFLATE 2-level Huffman decoder (`std/deflate/decode_deflate.wuffs`), and WebP/VP8L decoder (`std/webp/decode_webp.wuffs`, `decode_vp8l.wuffs`, `decode_huffman.wuffs`) transpiled to C without heap allocation or runtime panics.
- **Safe-Rust + Assembly SIMD Video Decoding (`memorysafety/rav1d` @ `2e7216c20ac2a75de204d6c8d7268b75a45959b4` vs. `videolan/dav1d` @ `6c7bee685677fd997a431302be4fea8ea4017606`):** Applies to `rav1d`'s `asm` (default) and `--no-default-features --features="bitdepth_8,bitdepth_16"` (pure-Rust fallback) builds on `x86_64` and `aarch64`, specifically auditing `src/msac.rs`, `src/loopfilter.rs`, `src/disjoint_mut.rs`, `src/ffi_safe.rs`, and `src/wrap_fn_ptr.rs`.

## Findings

### 1. Structural Mismatch Between Byte-Aligned Verified Combinators and Stateful Sub-Bit Entropy Coders

**Basis:** documentation (`everparse/README.md`, `vest/README.md`) + source (`libwebp`, `ryg_rans`, `FiniteStateEntropy`, `rav1d`) + derived.

Formally verified parser generators such as `EverParse` (`LowParse`/`3D`/`EverCDDL`, USENIX Security 2019; `project-everest/everparse` @ `270f5aab...`) and `Vest` (Verus-verified Rust combinators, USENIX Security 2025; `secure-foundations/vest` @ `026867a3...`) achieve memory safety, panic freedom, termination, and non-malleability (round-trip bijectivity) for **structured, byte-aligned protocol and container formats** (TLS, QUIC, Bitcoin, WireGuard, ASN.1 DER/BER, CBOR). In media stacks, these tools are well-suited to outer container framing (RIFF/WebP chunk headers, MP4/ISOBMFF boxes, AV1 OBU headers, PNG chunk lengths).

However, once parsing crosses into the **compressed entropy payload**, four structural properties break the core abstractions of byte-sliced TLV parser combinators:

1. **Sub-bit fractional coding and continuous state renormalization:** In arithmetic coding (`H.264 CABAC`, `AV1 MSAC`) and Asymmetric Numeral Systems (`rANS`/`tANS`), individual decoded symbols frequently consume *less than one bit* of input (e.g., a symbol with probability $p = 0.95$ contributes $-\log_2(0.95) \approx 0.074$ bits). Bytes are pulled into a wide shift/range register (`dif`/`rng` or `x`) only sporadically during renormalization, destroying any 1-to-1 correspondence between a parsed AST node and an input byte slice `&[u8]`.
2. **Mutable cross-symbol probability state:** Adaptive entropy coders (`CABAC`, `MSAC`) mutate persistent probability models (64-state LPS tables or 15-bit CDF arrays) after *every single decoded symbol*. The grammar of symbol $k+1$ depends on the exact cumulative history of all prior symbols $0 \dots k$ in the tile or slice, violating context-free / locally dependent combinator composition.
3. **Backward LIFO stream ordering (`rANS`/`tANS`):** Both `rANS` (`ryg_rans/rans_byte.h:22-26`) and `FSE` (`FiniteStateEntropy/lib/bitstream.h:53-56`) operate as last-in-first-out stacks: encoding runs in reverse over symbols or writes bits forward that must be read **backward** from the end of the compressed buffer (`BIT_DStream_t` anchored by a trailing sentinel `1`-bit), requiring random-access end-of-buffer framing rather than streaming forward consumption.
4. **Untrusted bitstream-defined decoding automata:** Dynamic Canonical Huffman (`DEFLATE`, `VP8L`) and `FSE` serialize *meta-encoded* code-length or normalized-frequency tables inside the bitstream itself (`ReadHuffmanCodeLengths`, `FSE_readNCount`), from which the decoder synthesizes an executable lookup table or finite-state automaton in memory before decoding pixels. Bugs in the table-synthesis phase yield zero-click memory corruption before a single pixel is rendered.

| Paradigm | Representative Systems | Directionality | Bits / Symbol | Mutable Decode State | Primary Memory-Safety Hazard | Verified-TLV Combinator Fit |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Byte-aligned TLV / Containers** | `EverParse` (`3D`), `Vest`, RIFF/ISOBMFF | Forward byte cursor | $\ge 8$ (or byte-packed bitfields) | Local length/tag dependencies | Integer overflow in length/offset, unvalidated tag | **Native target** (high fit) |
| **Canonical Huffman (2-level LUT)** | `libwebp` VP8L, `zlib`/`DEFLATE`, `Wuffs` | Forward bit reader (LSB/MSB) | Integer $1 \dots 15$ | Bit buffer + bitstream-built 2-level LUT | Kraft-inequality violation -> 2nd-level LUT heap OOB (`CVE-2023-4863`) | Poor (LUT synthesis & bit-window refill) |
| **Binary Arithmetic Coding (`CABAC`)** | ITU-T H.264/AVC §9.3, HEVC | Forward bit stream | Fractional ($> 0$) | `codIRange`, `codIOffset` + hundreds of adaptive context states | Context-index OOB, truncated stream stall, serial bit dependency | Unsuitable |
| **Multi-Symbol Arithmetic (`MSAC`)** | AV1 (`rav1d`/`dav1d`), Daala | Forward byte refill into `EcWin` | Fractional ($> 0$, up to 16-way) | `dif`, `rng`, `cnt` + adaptive 15-bit inverse-CDF arrays | CDF array bounds, `buf.pos` pointer drift in SIMD asm | Unsuitable |
| **Asymmetric Numeral Systems (`rANS`/`tANS`)** | `ryg_rans`, `FSE`/`Zstd`, JPEG XL | **LIFO** (encode reverse / read backward or forward) | Fractional ($> 0$) | Single integer `x` (`rANS`) or FSM state (`tANS`) | Unbounded renorm spin past EOF (`x == 0`), invalid spread table (`position != 0`) | Unsuitable |

---

### 2. Canonical Huffman Kraft's-Inequality Violations and `libwebp` CVE-2023-4863 (BLASTPASS)

**Basis:** normative (Kraft–McMillan theorem; WebP Lossless VP8L specification) + source (`webmproject/libwebp` `v1.3.1` @ `fd7bb21c...`, fix @ `2af26267...`, `HEAD` @ `eceabea8...`) + execution.

#### 2.1 Canonical Huffman Trees, Kraft's Equality, and 2-Level Lookup Tables

A canonical Huffman code of maximum length $L_{\max} = 15$ is uniquely specified by an array `code_lengths[0..N-1]` with values $l_s \in \{0, 1, \dots, 15\}$ (where $l_s = 0$ marks an unused symbol). Let $c_\ell = |\{s : l_s = \ell\}|$ be the histogram of code lengths. A valid, unambiguous prefix-free binary tree exists if and only if **Kraft's inequality** holds:
$$K = \sum_{\ell=1}^{L_{\max}} c_\ell \cdot 2^{-\ell} \le 1 \quad \Longleftrightarrow \quad \sum_{\ell=1}^{L_{\max}} c_\ell \cdot 2^{L_{\max} - \ell} \le 2^{L_{\max}} \quad (= 32768 \text{ for } L_{\max}=15).$$
- If $K > 1$ (**over-subscribed**), more leaves are requested than exist in the binary tree; canonical codes wrap/collide.
- If $K < 1$ (**under-subscribed / incomplete**, excluding degenerate 1-symbol codes), some bit patterns reach unmapped leaves; in a 2-level lookup table, an incomplete subtree forces `NextTableBitSize()` to assume deeper codes remain unfilled.
- If $K = 1$ (**complete**), the full binary tree with $M$ active symbols has exactly `num_nodes == 2*M - 1` nodes and zero open branches (`num_open == 0`) at depth $L_{\max}$.

To decode symbols in $O(1)$ without walking bit-by-bit, `libwebp` (`src/utils/huffman_utils.c`, `src/dec/vp8l_dec.c:183-197`) constructs a **2-level bit-reversed lookup table** with root width `HUFFMAN_TABLE_BITS = 8` ($2^8 = 256$ root slots). Codes of length $\ell \le 8$ are replicated directly into the root table at stride $2^\ell$. Whenever codes of length $\ell > 8$ open a new 8-bit root prefix `(key & 0xFF) != low`, `BuildHuffmanTable()` appends a 2nd-level subtable of width $2^{\text{table\_bits}}$ computed by `NextTableBitSize(count, len, 8)` (`huffman_utils.c:66-76`):
```c
static WEBP_INLINE int NextTableBitSize(const int* const count,
                                        int len, int root_bits) {
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

#### 2.2 Exact Root Cause of CVE-2023-4863 in `libwebp` `v1.3.1`

In `webmproject/libwebp` `v1.3.1` (`fd7bb21c0cb56e8a82e9bfa376164b842f433f3b`), `ReadHuffmanCodes()` (`src/dec/vp8l_dec.c:88-102, 437-484`) allocates **one flat heap buffer** of `num_htree_groups * kTableSize[color_cache_bits]` `HuffmanCode` structs (4 bytes each), storing 5 sequential Huffman tables per meta-code group: `GREEN` (alphabet $280 + 2^{\text{cc}}$), `RED` (256), `BLUE` (256), `ALPHA` (256), and `DIST` (40). The constants in `vp8l_dec.c:80-102`:
```c
#define FIXED_TABLE_SIZE (630 * 3 + 410) // 2300: RED(630) + BLUE(630) + ALPHA(630) + DIST(410)
static const uint16_t kTableSize[12] = {
  FIXED_TABLE_SIZE + 654,  // cc=0:  2954 entries (11,816 bytes)
  ...,
  FIXED_TABLE_SIZE + 2704  // cc=11: 5004 entries (20,016 bytes)
};
```
were precomputed using Mark Adler's `enough.c`, which proves worst-case 2-level table sizes **exclusively for complete ($K = 1$) canonical Huffman codes**.

**Three compounding defects in `libwebp` `v1.3.1` `src/utils/huffman_utils.c` broke that precondition:**
1. **Write-Before-Completeness-Check (`huffman_utils.c:172-203`):** `BuildHuffmanTable()` checked over-subscription (`if (num_open < 0) return 0;`) incrementally per length `len`, **but did not check completeness/under-subscription (`if (num_nodes != 2 * offset[MAX_ALLOWED_CODE_LENGTH] - 1) return 0;`) until line 200—*after* writing every 2nd-level subtable into the heap buffer via `ReplicateValue()`!**
2. **Unfilled Subtree Inflation in `NextTableBitSize()`:** On an under-subscribed ($K < 1$) code histogram, `left` in `NextTableBitSize()` never reaches $\le 0$ on open partial root slots, so the loop runs all the way to `len = MAX_ALLOWED_CODE_LENGTH` (`15`) and returns `15 - 8 = 7`, allocating a maximum-size $2^7 = 128$-entry 2nd-level subtable (`512` bytes) for each unfilled prefix! Even an *over-subscribed* code whose `num_open < 0` occurs only at `len = 15` already wrote all `len = 9..14` subtables before aborting.
3. **Broken Dry-Run Size Computation (`huffman_utils.c:180`):** Passing `root_table == NULL` hit `if (root_table == NULL) continue;` inside the 2nd-level loop, so `VP8LBuildHuffmanTable(NULL, ...)` only validated completeness and could not compute actual `total_size` beforehand.

#### 2.3 Analytical Verification of Table-Budget Overflow (Python Model of `BuildHuffmanTable`)

**Basis:** source + execution (1:1 Python model matching C post-decrement order in `huffman_utils.c:181-196`).

| VP8L Tree & Code-Length Histogram | Kraft Sum $\times 2^{15}$ (Complete $= 32768$) | `enough.c` Budget | `v1.3.1` Written Entries (`ret`) | Budget Excess (Entries / Bytes) | `v1.3.2` Dry-Run Writes (`ret`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Complete uniform `256`-sym (`[8]*256`) | `32768` (COMPLETE) | `630` | `256` (`ret=256`) | `-374` (`-1496 B`) | `0` (`ret=256`) |
| Complete mixed `256`-sym (`[1..6,8] + 135×14 + 114×15`) | `32768` (COMPLETE) | `630` | `512` (`ret=512`) | `-118` (`-472 B`) | `0` (`ret=512`) |
| Under-subscribed `DIST` (`α=40`: `[9]*39`) | `2496` (UNDER) | `410` | `422` (`ret=0`) | **`+12` (`+48 B`)** | **`0` (`ret=0`)** |
| Under-subscribed `DIST` (`α=40`: `[9..14] + [15]*34`) | `160` (UNDER) | `410` | **`512`** (`ret=0`) | **`+102` (`+408 B`)** | **`0` (`ret=0`)** |
| Under-subscribed `R/B/A` (`α=256`: `[9]*255`) | `16320` (UNDER) | `630` | `638` (`ret=0`) | **`+8` (`+32 B`)** | **`0` (`ret=0`)** |
| Under-subscribed `GREEN` (`cc=0, α=280`: `[9]*279`) | `17856` (UNDER) | `654` | `662` (`ret=0`) | **`+8` (`+32 B`)** | **`0` (`ret=0`)** |
| Over-subscribed `GREEN` (`cc=11, α=2328`: `509×9 + 1819×15`) | `34395` (OVER at `len=15`) | `2704` | `892` written before `len=15` abort (`ret=0`) | `-1812` | **`0` (`ret=0`)** |

When four valid complete trees (`GREEN`, `RED`, `BLUE`, `ALPHA`) consume near-maximal `enough.c` space inside the single `huffman_tables` allocation and the 5th tree (`DIST`, `α=40`) carries an under-subscribed `[9..14] + [15]*34` histogram, `BuildHuffmanTable()` in `v1.3.1` writes up to `102` `HuffmanCode` entries (`408` bytes) beyond the heap allocation before line 200 rejects the tree—corrupting adjacent heap chunks in zero-click image rendering paths (tracked as CVE-2023-4863 / Apple CVE-2023-41064, BLASTPASS).

#### 2.4 Evolution of Remediation Across `v1.3.2` (`2af26267...`) and `HEAD` (`eceabea8...`)

1. **Immediate Security Fix (`2af26267cdfcb63a88e5c74a85927a12d6ca1d76`, `v1.3.2`):**
   - Removed `if (root_table == NULL) continue;` from the 2nd-level loop so `BuildHuffmanTable(NULL, ...)` executes a full zero-write validation + sizing pass before any table memory is touched (`VP8LBuildHuffmanTable` lines 219-222). (Even though the root loop at line 179 still skips `key` updates when `root_table == NULL`, root codes always consume whole root slots, so `key` starts at a root-slot boundary and the dry-run `total_size` is bit-identical to the write pass—verified in the standalone Python `BuildHuffmanTable` probe with `size_match = True` across every test case.)
   - Replaced the single raw `HuffmanCode*` allocation with linked `HuffmanTablesSegment` slabs (`huffman_utils.h:46-63`) that dynamically allocate a new contiguous segment whenever `curr_table + total_size` would exceed the current segment. (Note: `2af26267...` used a conservative `>=` check at line 224, triggering an extra segment when a table fit *exactly*.)
2. **Subsequent Hardening (`eceabea8c5f72920c4a4f92724ef2c38bb2d1985`, `HEAD`):**
   - Factored segment growth into `VP8LHuffmanTablesEnsureCapacity()` (`huffman_utils.c:235-269`) with exact `>` bounds check.
   - Added Clang `-fbounds-safety` pointer annotations (`WEBP_COUNTED_BY`, `WEBP_BIDI_INDEXABLE`, `WEBP_UNSAFE_FORGE_BIDI_INDEXABLE`, `huffman_utils.c:59-95, 284-299`) and an explicit non-assert runtime guard `if (offset[symbol_code_length] >= code_lengths_size) return 0;` (`huffman_utils.c:140-142`) to prove `sorted[]` writes in-bounds even under `-DNDEBUG`.

---

### 3. Asymmetric Numeral Systems (`rANS`/`tANS`) and Context-Adaptive Arithmetic Coding (`CABAC`/`MSAC`)

**Basis:** normative (Duda `arXiv:1311.2540`; Marpe et al. `DOI: 10.1109/TCSVT.2003.815173`; AOMedia AV1 Spec §8.2) + source (`ryg_rans`, `FiniteStateEntropy`, `rav1d`) + execution.

#### 3.1 `rANS` Single-Integer LIFO State Machine and Unbounded Renormalization Hazard

In Jarek Duda's range Asymmetric Numeral Systems (`arXiv:1311.2540`) as canonically implemented in Fabian Giesen's `ryg_rans` (`rans_byte.h:50-318`), the entire coder state is a single 32-bit unsigned integer $x \in [L, b L)$ with $L = \texttt{RANS\_BYTE\_L} = 2^{23}$ and byte renormalization base $b = 2^8$ (keeping $x < 2^{31}$ so exact 32-bit unsigned Alverson reciprocals eliminate runtime division on encoding, `rans_byte.h:46-50, 174-280`). For quantized symbol frequencies $\{f_s\}$ summing to $M = 2^{\text{scale\_bits}}$ with cumulative starts $c_s = \sum_{j < s} f_j$:
- **Encode (reverse symbol order, writing bytes backward from end of buffer):**
  1. Renormalize while $x \ge x_{\max}(s) = ((L \gg \text{scale\_bits}) \ll 8) \cdot f_s$: emit `*--ptr = x & 0xFF; x >>= 8;`.
  2. Transition: $x' = \lfloor x / f_s \rfloor \cdot M + (x \bmod f_s) + c_s$.
  3. Flush final 32-bit state `x` little-endian at buffer start (`RansEncFlush`, lines 93-105).
- **Decode (forward symbol order, reading bytes forward):**
  1. Peek cumulative slot $c = x \bmod M$ (`RansDecGet`, line 127) and locate $s$ with $c_s \le c < c_s + f_s$.
  2. Inverse transition: $x' = f_s \cdot \lfloor x / M \rfloor + c - c_s$ (`RansDecAdvance`, line 139).
  3. Renormalize while $x' < L$: `x' = (x' << 8) | *ptr++` (`rans_byte.h:142-145`).

**Three Execution-Verified Properties (Standalone Python `rANS`/`MSAC` Probe):**
1. **Zero-Signaling Multi-Lane SIMD Interleaving:** Because rANS functions take the byte-stream pointer explicitly without hidden bit-buffer state, two independent states (`s0`, `s1`) can interleave into a single shared byte stream (encode `s1` then `s0` backward; decode `s0` then `s1` forward), breaking serial dependency chains on superscalar/SIMD pipelines. On a 128-symbol skewed 4-symbol stream ($p = [0.75, 0.125, 0.0625, 0.0625]$, Shannon entropy `1.186 bits/sym`), 2-lane interleaved `rANS` achieved exact round-trip decoding in `18` payload bytes (`1.125 bits/sym` excluding the 8-byte state flush).
2. **Global State-Avalanche Sensitivity:** Flipping a single bit in byte 1 (`bit 11`, crossing a frequency boundary in initial state `s0`) caused `41 / 128` downstream symbol mismatches across the interleaved stream (whereas flipping bit 0 inside a wide `0.75`-probability interval perturbed only `1 / 128` symbol).
3. **Missing Bounds Guard in Reference Renormalization (`rans_byte.h:142-145`):**
   ```c
   if (x < RANS_BYTE_L) {
       uint8_t* ptr = *pptr;
       do x = (x << 8) | *ptr++; while (x < RANS_BYTE_L);
       *pptr = ptr;
   }
   ```
   `RansDecAdvance()` performs **no end-of-buffer check** and assumes `x >= RANS_BYTE_L` initially and `freq > 0` for every decoded symbol. If an attacker crafts a malformed header leaving `x = 0` (or triggers a zero-frequency symbol) over zero-padded bytes, `x` remains `0 < 2^23` forever, spinning `*ptr++` directly past the end of the input buffer (in the standalone Python probe, an explicit EOF guard caught an unbounded spin after reading all 16 zero bytes!). Production rANS decoders (e.g., JPEG XL, Draco) must validate `x >= L` after `RansDecInit`, reject `freq == 0` in CDF lookup tables, and bound-check `ptr < end` on every renormalization byte load.

#### 3.2 `tANS` / Finite State Entropy (`FSE`) Automaton Bounds

Yann Collet's `FiniteStateEntropy` (`Cyan4973/FiniteStateEntropy` @ `9f30e091...`, used inside Zstandard) compiles ANS transitions into a cache-resident finite-state table (`FSE_decode_t { U16 newState; BYTE symbol; BYTE nbBits; }`, `fse_decompress.c:71-126`):
- **Completeness Invariant (`fse_decompress.c:103-114`):** `FSE_buildDTable()` spreads normalized frequencies across `tableSize = 1 << tableLog` slots via step `FSE_TABLESTEP(tableSize)` (coprime to `tableSize`) and verifies `if (position != 0) return ERROR(GENERIC);`, rejecting any frequency histogram that fails to sum to `1 << tableLog` before building transition entries.
- **Backward Bitstream & Dual-State Unrolling (`fse_decompress.c:188-235`, `bitstream.h:88-119`):** `BIT_initDStream()` anchors at the last byte's highest set sentinel bit and reads backward into a `size_t` bit container. Each `BIT_reloadDStream() == BIT_DStream_unfinished` guarantees at least `sizeof(size_t)*8 - 7` bits (`57` bits on 64-bit, `25` on 32-bit, `bitstream.h:45-47`), enabling 2 interleaved `FSE_DState_t` machines (`state1`, `state2`) to emit 4 symbols per loop with static compile-time reload-frequency checks (`FSE_MAX_TABLELOG*4 + 7 > sizeof(bitContainer)*8`).

#### 3.3 `H.264 CABAC` vs. `AV1 MSAC` Adaptive Multi-Symbol Range Coding

- **H.264/AVC CABAC (`Marpe, Schwarz, Wiegand, IEEE TCSVT 2003`, `DOI: 10.1109/TCSVT.2003.815173`):** Binarizes every syntax element into binary bins and updates a 9-bit `codIRange` via a 64-state LPS table (`rangeTabLPS`), renormalizing 1 bit at a time. Each bin depends serially on the previous bin's range update and state transition, creating a severe single-thread throughput ceiling (1–2 bins/cycle) that resists SIMD vectorization.
- **AV1 Multi-Symbol Arithmetic Coding (`MSAC`, AOMedia AV1 Spec §8.2; `memorysafety/rav1d` `src/msac.rs:293-680`):** Generalizes binary range coding to alphabets of up to 16 symbols (`n_symbols < 16`, `msac.rs:397`) using 15-bit inverse-CDF arrays (`cdf[0] > cdf[1] > ... > cdf[n_symbols-1] > 0`) with quantization `EC_PROB_SHIFT = 6` and minimum probability floor `EC_MIN_PROB = 4` (`msac.rs:293-295`):
  - **Clever Sentinel Aliasing (`msac.rs:398-408`):** `assert!(cdf[n_symbols] <= 32)` enforces that the trailing slot `cdf[n_symbols]` simultaneously stores the adaptation sample counter (`0..=32`) **and** acts as the zero-sentinel terminating the CDF search loop because `32 >> EC_PROB_SHIFT(6) == 0`, guaranteeing `v = 0` at `val = n_symbols` and `c >= 0` loop termination without an extra bounds branch!
  - **SIMD Parallel Thresholding (`msac.rs:14-69, 526-603`):** Because up to 16 16-bit CDF thresholds fit in a single `AVX2` (`256`-bit) or two `SSE2`/`NEON` (`128`-bit) registers, `dav1d_msac_decode_symbol_adapt16_{sse2,avx2,neon}` computes all scaled thresholds `(r * (cdf[i] >> 6)) >> 1 + 4*(N - i)` and compares against `c` in parallel, then updates all `cdf[0..n_symbols]` lanes simultaneously via vector shifts (`rate = 4 + (count >> 4) + (n_symbols > 2)`, `msac.rs:416-425`).

---

### 4. Compile-Time Interval Bounds Proofs Without Runtime Panics: Google `Wuffs`

**Basis:** documentation (`doc/note/{bounds-checking,facts,interval-arithmetic}.md`) + source (`google/wuffs` @ `a87f0bb8...`: `lang/check/bounds.go`, `std/deflate/decode_deflate.wuffs`, `std/webp/decode_{webp,vp8l,huffman}.wuffs`).

Google `Wuffs` (*Wrangling Untrusted File Formats Safely*) is a memory-safe, zero-allocation, coroutine-capable language transpiled to C that rejects **every** potential out-of-bounds array/slice access, integer overflow/underflow, division by zero, and `nullptr` dereference **at compile time**—producing C code with zero runtime bounds-check panics.

#### 4.1 Non-SMT Verification Engine (`lang/check/bounds.go`)

Rather than invoking an SMT solver (which introduces non-deterministic timeouts and fragile proof engineering), Wuffs combines three decidable, fast compile-time mechanisms:
1. **Refinement Integer Types & Exact Arbitrary-Precision Interval Arithmetic (`lang/check/bounds.go:26-84`):** Every numeric variable carries a static inclusive interval `bounds = interval.IntRange` over `math/big.Int` (e.g., `color_cache_bits : base.u32[..= 11]`, `ht_n_symbols : base.u32[..= 2328]`, `n_bits : base.u32[..= 31]`). Arithmetic (`+`, `-`, `*`, `/`, `<<`, `>>`, `&`, `|`) propagates intervals soundly; `i = i + 1` fails to compile unless the resulting interval fits inside `i`'s declared refinement, while explicit wrapping (`~mod+=`) and saturating (`~sat-=`) operators opt out of overflow proof obligations where modular arithmetic is intended.
2. **Flow-Sensitive `Facts` and Set-Intersection Reconciliation (`doc/note/facts.md:1-165`):** Branches (`if x < s.length()`) narrow variable intervals and record relational facts (`a < b`, `args.ic <> nullptr`); join points reconcile situations via pure set intersection. Transitive proofs are supplied explicitly via lightweight `via` rules (e.g., `assert i < 2048 via "a < b: a < c; c <= b"(c: n)` in `decode_vp8l.wuffs:415`).
3. **Explicit Loop Invariants (`pre`, `inv`, `post`):** To avoid fixpoint divergence, Wuffs requires programmers to annotate loop invariants explicitly (`doc/note/facts.md:118-163`), checking every entry, `continue`, loop bottom, and `break` locally.

#### 4.2 How Wuffs Prevents CVE-2023-4863 — Two Contrasting Designs

Direct source inspection reveals **two distinct Wuffs verification patterns** across `DEFLATE` and `WebP/VP8L`:

1. **Verified 2-Level Lookup Table (`std/deflate/decode_deflate.wuffs:64-65, 644-682, 845-926`):**
   - **Pre-Write Kraft Equality Enforcement (lines 645–681):** Before writing any entry into `this.huffs[2][1024]`, Wuffs tracks `remaining` from `1` through lengths `1..=15`, returning `"#bad Huffman code (over-subscribed)"` if `remaining < counts[i]` and `"#bad Huffman code (under-subscribed)"` if `remaining <> 0` (with RFC 1951 §3.2.7's single-distance-code exception explicitly handled).
   - **Defense-in-Depth Static Bounds Proof (lines 873–877, 921–925):** Even *independent* of the Kraft proof, the compiler refuses to accept any table write `this.huffs[args.which][idx] = value` without explicit proof that `idx < HUFFS_TABLE_SIZE` (`1024`), guarded by runtime checks returning `"#internal error: inconsistent Huffman decoder state"` so a bug in `enough.c` sizing math converts cleanly into a safe error status rather than heap corruption!
2. **2-Level Table Elimination via Static Binary Node Arrays (`std/webp/decode_webp.wuffs:144-182`, `std/webp/decode_huffman.wuffs:217-235`):**
   - Written in 2024–2026 after CVE-2023-4863, Wuffs' VP8L decoder abandons 2-level lookup tables altogether. It stores canonical Huffman trees directly as explicit binary trees of 16-bit nodes (`0CCC...` branch offset, `1SSS...` leaf symbol) inside a fixed static array `huffman_nodes : array[256] array[0x187B] base.u16`.
   - The per-group node count `0x187B = 6267` is derived from the exact graph-theoretic bound $2N - 1$ for full binary trees: $(2\cdot 2328 - 1) + 3(2\cdot 256 - 1) + (2\cdot 40 - 1) = 4655 + 1533 + 79 = 6267$.
   - `build_code_lengths_huffman_nodes!()` (`decode_huffman.wuffs:217-234`) computes exact integer `subscription_total` (scaled by $2^{15}$) and rejects both `> (1 << 15)` (over-subscribed) and `< (1 << 15)` (under-subscribed) before inserting nodes.
   - **Engineering Cost of Static No-Alloc Proofs:** Because Wuffs prohibits library-side `malloc`, `decode_webp.wuffs:181` reserves **`256 * 0x187B * 2 = 3,208,704` bytes (~3.06 MiB)** inside `webp.decoder` and caps `overall_n_huffman_groups : base.u32[..= 256]` (rejecting valid VP8L files with `257..65536` meta-Huffman groups via `"#unsupported number of Huffman groups"`, `decode_vp8l.wuffs:397-399`), and performs bit-by-bit tree traversal (`decode_pixels_slow?`) rather than 8-bit 2-level table jumps.

---

### 5. Safe-Rust + Handwritten SIMD Hybrid Architecture and Verification Boundaries: `rav1d`

**Basis:** source (`memorysafety/rav1d` @ `2e7216c2...`, `videolan/dav1d` @ `6c7bee68...`) + derived.

Video codecs like AV1 (`dav1d`) cannot sacrifice 5–10× SIMD speedups in entropy coding, inverse transforms, motion compensation, and 14-tap loop filtering (`loopfilter`), yet their complex bitstream/frame/tile control plane in C has historically been a primary zero-click attack surface. `memorysafety/rav1d` ports `videolan/dav1d`'s C control plane and reference DSP routines to Rust (`#![deny(unsafe_op_in_unsafe_fn)]`) while keeping handwritten `x86`/`x86_64` (`SSE2`, `SSSE3`, `AVX2`, `AVX512ICL`) and `aarch64` (`NEON`) assembly kernels behind an opt-in `asm` feature flag (`Cargo.toml`, `README.md:38-55`).

#### 5.1 Dual-ABI Function-Pointer Dispatch (`wrap_fn_ptr!` + `FFISafe`)

A central engineering challenge in incremental C-to-Rust SIMD ports is invoking either handwritten `extern "C"` assembly (which expects raw `*mut DynPixel` + `ptrdiff_t` strides) or bounds-checked safe Rust (which requires owning/borrowed slice metadata) through a single indirect DSP function table without branching on every superblock.

`rav1d` solves this cleanly in `src/loopfilter.rs:29-74, 362-480`, `src/wrap_fn_ptr.rs`, and `src/ffi_safe.rs`:
```rust
wrap_fn_ptr!(pub unsafe extern "C" fn loopfilter_sb(
    dst_ptr: *mut DynPixel,
    stride: ptrdiff_t,
    mask: &[u32; 3],
    lvl_ptr: *const [u8; 4],
    b4_stride: ptrdiff_t,
    lut: &Align16<Av1FilterLUT>,
    w: c_int,
    bitdepth_max: c_int,
    _dst: FFISafeRav1dPictureDataComponentOffset,
    _lvl: WithOffset<*const FFISafe<DisjointMut<AlignedVec2<u8>>>>,
) -> ());
```
- Leading parameters (`dst_ptr .. bitdepth_max`) match `dav1d`'s exact C/System V / AAPCS64 assembly ABI; assembly kernels ignore the trailing `_dst` and `_lvl` parameters completely.
- When `feature = "asm"` is disabled or a CPU lacks SIMD extensions (`Rav1dLoopFilterDSPContext::default`), the table points to `loop_filter_sb128_c_erased`, which recovers the safe Rust wrappers via `FFISafe::from_with_offset()` (`src/ffi_safe.rs:44-47`) and calls 100%-safe `loop_filter_sb128_rust()` -> `loop_filter()` (`src/loopfilter.rs:91-356`), where every pixel tap `p6..q6` is bounds-checked via `(dst + strideb * stride_index).index_mut::<BD>()`.
- Similarly, in `src/msac.rs:248-267, 526-680`:
  - `MsacContext::buf_index()` computes `self.buf.pos as usize - self.data().as_ptr() as usize` in integer space (avoiding `ptr::offset_from` provenance UB) and re-slices `&data[self.buf_index()..]` with runtime bounds checking.
  - `rav1d_msac_decode_symbol_adapt{4,8,16}` and `rav1d_msac_decode_hi_tok` defensively clamp assembly return values with `% 4`, `% 8`, `% 16` (`msac.rs:545, 571, 602, 679`), preventing out-of-range symbols returned by assembly from indexing subsequent Rust tables out of bounds.

#### 5.2 Two Residual Soundness Boundaries Across `rav1d`'s Unsafe Perimeter

Direct inspection of `rav1d` @ `2e7216c2...` exposes two sharp boundaries that future verification or Rust-SIMD rewrites must address:

1. **`checkasm` Differential Fuzzing vs. Formal Equivalence (`src/msac.rs:531-665`, `src/loopfilter.rs:63`):**
   Every `unsafe` assembly dispatch site in `src/msac.rs` justifies soundness via:
   `// SAFETY: checkasm has verified that it is equivalent to [dav1d_msac_decode_*_rust].`
   And `src/loopfilter.rs:63` states:
   `// SAFETY: Fallback fn loop_filter_sb128_rust is safe; asm is supposed to do the same.`
   `checkasm` is randomized property/differential testing, **not** an exhaustive proof. Memory-safety bugs in handwritten assembly—such as over-reading past negative or unpadded frame strides, mis-aligned vector loads, or rare edge-case bit-pattern mismatches—bypass Rust's type system completely while `feature = "asm"` is enabled (by contrast, building with `--no-default-features --features="bitdepth_8,bitdepth_16"` executes purely safe Rust DSP fallbacks).
2. **`DisjointMut<T>` Release-Mode Data-Race Soundness Gap (`src/disjoint_mut.rs:32-73, 109-201`):**
   To allow multi-threaded AV1 tile/frame workers to mutate disjoint regions of a single frame buffer concurrently while performing zero-copy typed pixel reinterpretation via `zerocopy::{AsBytes, FromBytes}` (`cast_slice`, `cast`, lines 109–201), `rav1d` wraps shared buffers in `DisjointMut<T>` around `UnsafeCell<T>`.
   - Under `#[cfg(debug_assertions)]` (`debug` and `opt-dev` profiles), `DisjointMutGuard` and `DisjointImmutGuard` dynamically track active byte ranges and panic on overlapping mutable/immutable borrows.
   - Under `--release` (`#[cfg(not(debug_assertions))]`), `DisjointMut<T>` erases all tracking (`#[repr(transparent)]`) and relies purely on manual `pub(crate)` call-site disjointness.
   - **Normative Disagreement in Upstream `SAFETY` Rationale (`src/disjoint_mut.rs:67-72`):** The upstream `unsafe impl Sync for DisjointMut<T>` comment asserts that because `T`'s target elements are provenanceless integers, *"a data race due the lack of runtime disjointness checking in release mode would only result in wrong results, and cannot result in memory safety."* Under the normative Rust memory model (and LLVM's `noalias` / C++11 data-race semantics), **any** unsynchronized concurrent non-atomic read/write or write/write race—even on plain `u8`/`u16` pixels—is full Undefined Behavior, permitting LLVM to hoist loads, assume disjointness via `noalias` on materialized `&mut [V]` guards, or eliminate downstream safety checks!

### 6. Cross-System Trade-Off Matrix for Verified Media Decoding

| Dimension | `libwebp` (`v1.3.2` / `HEAD`) | Google `Wuffs` (`std/deflate`, `std/webp`) | `rav1d` (`asm` enabled) | `rav1d` (`--no-default-features`, pure Rust) | `EverParse` / `Vest` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Memory-Safety Mechanism** | Manual C + dry-run validation + `-fbounds-safety` annotations | Compile-time interval arithmetic + flow-sensitive facts (no SMT) | Rust borrow checker + `checkasm` + `DisjointMut` (debug-checked) | Rust borrow checker + `DisjointMut` (debug-checked) | F*/Low* or Verus SMT proof of safety + functional correctness |
| **Dynamic Heap Allocation** | Yes (`WebPSafeMalloc`, chained `HuffmanTablesSegment`) | **None** (caller-supplied `workbuf` + static decoder struct) | Yes (frame pools, `AlignedVec`) | Yes | **None** (zero-copy views / caller buffers) |
| **Runtime Bounds Panics** | No (C UB if missed; `-fbounds-safety` traps) | **Zero** (all checks proved at compile time) | Possible in Rust control plane; none in asm (UB if bug) | Possible on OOB; no C/asm UB | **Zero** (proven panic-free) |
| **SIMD / Throughput Tier** | High (C + intrinsics) | High for DEFLATE (`fast64`/`bmi2`); moderate for VP8L (tree walk) | **Peak** (handwritten `AVX2`/`AVX512`/`NEON` asm) | Moderate (LLVM auto-vectorization) | High for TLV; **cannot express** entropy coders |
| **Format Coverage Fidelity** | Full VP8L spec (up to 65,536 Huffman groups) | Partial VP8L (`<= 256` Huffman groups; `3.06 MiB` static struct) | Full AV1 spec (`libdav1d` drop-in C ABI) | Full AV1 spec | Container/header framing only |

## Boundaries

- **Lossy VP8 / H.265 HEVC / VVC Entropy Decoders (`not examined`):** Source audits covered VP8L lossless WebP (`libwebp`, `Wuffs`), `DEFLATE` (`Wuffs`), `rANS` (`ryg_rans`), `tANS`/`FSE` (`FiniteStateEntropy`), and AV1 `MSAC` (`rav1d`). Lossy VP8 boolean coder internals, HEVC wavefront parallel processing (WPP) CABAC synchronization, and VVC multi-hypothesis CABAC were not directly inspected.
- **Safe-Rust Portable SIMD Replacement (`safe_simd`) in Later `rav1d` Commits (`not examined`):** At examined revision `2e7216c20ac2a75de204d6c8d7268b75a45959b4`, `src/safe_simd/` does not exist and SIMD kernels reside exclusively in external `src/x86/*.asm` and `src/arm/**/*.S` assembly files. Subsequent `rav1d` work migrating assembly kernels to safe Rust `std::arch` intrinsics is outside this revision snapshot.
- **Clang `-fbounds-safety` Enforcement Coverage in `libwebp` `HEAD` (`unknown`):** While `libwebp` `HEAD` (`eceabea8...`) includes `WEBP_COUNTED_BY`, `WEBP_BIDI_INDEXABLE`, and `WEBP_UNSAFE_FORGE_BIDI_INDEXABLE` macros in `huffman_utils.c`, compiler-enforced `-fbounds-safety` builds require an Apple/LLVM fork supporting the extension; standard GCC/upstream Clang builds compile those macros to empty tokens, so actual trap behavior under `-fbounds-safety` was not executed.
- **Full-Bit-Stream End-to-End Exploit Synthesis (`known not to apply` / `not examined`):** The standalone Python Huffman-table probe analytically executes `BuildHuffmanTable()` directly on canonical `code_lengths[]` vectors to measure exact table-sizing overshoot vs. `kTableSize`; constructing an end-to-end weaponized WebP RIFF/VP8L file or heap-grooming primitive was intentionally out of scope.
- **Functional Equivalence of `Wuffs` C Output (`unsupported` / `not examined`):** Wuffs' compiler proves memory safety, arithmetic overflow freedom, and coroutine suspension safety—**not** full functional conformance to RFC 1951 or the VP8L pixel-reconstruction specification; pixel accuracy is validated via conformance test suites rather than formal equivalence proofs.

## Evidence

### Primary Git Repositories and Inspected Source Locations

| Subject | Repository & Full Commit SHA | Inspected Paths & Key Symbols / Lines |
| :--- | :--- | :--- |
| `libwebp` (`v1.3.1`) | `webmproject/libwebp` @ `fd7bb21c0cb56e8a82e9bfa376164b842f433f3b` | `src/utils/huffman_utils.c:43-76` (`GetNextKey`, `ReplicateValue`, `NextTableBitSize`), `:80-206` (`BuildHuffmanTable` writing 2nd-level tables at lines 172–197 before line 200 fullness check, plus `if (root_table == NULL) continue;` at line 180); `src/dec/vp8l_dec.c:80-102` (`FIXED_TABLE_SIZE`, `kTableSize[12]`), `:358-529` (`ReadHuffmanCodes`) |
| `libwebp` (fix) | `webmproject/libwebp` @ `2af26267cdfcb63a88e5c74a85927a12d6ca1d76` | `src/utils/huffman_utils.c:177-270` (two-pass `BuildHuffmanTable(NULL, ...)` dry-run + chained `HuffmanTablesSegment` allocation with `>=` check); `src/utils/huffman_utils.h:46-67` (`HuffmanTablesSegment`, `HuffmanTables`); `src/dec/vp8l_dec.c:439-528` (`VP8LHuffmanTablesAllocate`) |
| `libwebp` (`HEAD`) | `webmproject/libwebp` @ `eceabea8c5f72920c4a4f92724ef2c38bb2d1985` | `src/utils/huffman_utils.c:59-95, 284-299` (`WEBP_COUNTED_BY`, `WEBP_BIDI_INDEXABLE`, `WEBP_UNSAFE_FORGE_BIDI_INDEXABLE`), `:140-142` (non-assert `offset >= code_lengths_size` guard), `:235-269` (`VP8LHuffmanTablesEnsureCapacity` with exact `>` check) |
| `Wuffs` | `google/wuffs` @ `a87f0bb85b9406d29f48a1c03b6f42c4585145f6` | `doc/note/bounds-checking.md:1-45`; `doc/note/facts.md:1-173`; `doc/note/interval-arithmetic.md:1-133`; `lang/check/bounds.go:26-160` (`interval.IntRange`, `numTypeBounds`); `std/deflate/decode_deflate.wuffs:59-151, 644-682, 845-939` (`HUFFS_TABLE_SIZE = 1024`, pre-write over/under-subscription checks, `via` bounds proofs); `std/webp/decode_webp.wuffs:14-182` (`huffman_nodes : array[256] array[0x187B] base.u16`, `3,208,704` B); `std/webp/decode_vp8l.wuffs:396-405`; `std/webp/decode_huffman.wuffs:180-250` (`subscription_total == 1 << 15`) |
| `rav1d` | `memorysafety/rav1d` @ `2e7216c20ac2a75de204d6c8d7268b75a45959b4` | `README.md:38-55`; `src/msac.rs:14-78, 146-267` (`MsacAsmContext`, `buf_index` safe integer subtraction), `:293-429` (`EC_PROB_SHIFT = 6`, `EC_MIN_PROB = 4`, `rav1d_msac_decode_symbol_adapt_rust`), `:526-680` (`checkasm` safety comments & `% 4/% 8/% 16` return clamping); `src/loopfilter.rs:29-74, 91-381, 383-480` (`loopfilter_sb`, `loop_filter_sb128_rust`, `init_x86`/`init_arm`); `src/disjoint_mut.rs:17, 32-73, 109-201` (`DisjointMut`, debug-only tracking, `zerocopy::{AsBytes, FromBytes}`, release-mode data-race rationale); `src/ffi_safe.rs:1-57`; `src/wrap_fn_ptr.rs:1-101` |
| `dav1d` | `videolan/dav1d` @ `6c7bee685677fd997a431302be4fea8ea4017606` | Upstream C/assembly reference architecture targeted as drop-in ABI by `rav1d` |
| `ryg_rans` | `rygorous/ryg_rans` @ `c9d162d996fd600315af9ae8eb89d832576cb32d` | `rans_byte.h:17-149` (`RANS_BYTE_L = 1u << 23`, LIFO encode/decode, unguarded `do x = (x << 8) \| *ptr++; while (x < RANS_BYTE_L);` at lines 142–145), `:159-280` (Alverson fixed-point reciprocal `RansEncSymbolInit` / `RansEncPutSymbol`) |
| `FiniteStateEntropy` | `Cyan4973/FiniteStateEntropy` @ `9f30e0918f87bd835fa040d922a208d7b219e50b` | `lib/fse_decompress.c:71-126` (`FSE_buildDTable`, `position != 0` completeness check), `:178-238` (dual-state `state1`/`state2` unrolled loop); `lib/bitstream.h:45-119` (`STREAM_ACCUMULATOR_MIN_{32,64}`, backward `BIT_DStream_t`) |
| `EverParse` | `project-everest/everparse` @ `270f5aab699ac284d8777d4f01be20a5d91ea47c` | `README.md:1-150` (`LowParse`, `3D`, `QuackyDucky`, `EverCBOR`, `EverCDDL`) |
| `Vest` | `secure-foundations/vest` @ `026867a37d4b918153058df2c8db6c52fc62ba35` | `README.md:1-74` (Verus-verified `vest_lib`, DSL, ASN.1, CBOR combinators) |

### Specifications and Peer-Reviewed Literature

- Jarek Duda, *"Asymmetric numeral systems: entropy coding combining speed of Huffman coding with compression rate of arithmetic coding"*, `arXiv:1311.2540` (Nov 2013 / Jan 2014).
- Detlev Marpe, Heiko Schwarz, and Thomas Wiegand, *"Context-Based Adaptive Binary Arithmetic Coding in the H.264/AVC Video Compression Standard"*, IEEE Transactions on Circuits and Systems for Video Technology, Vol. 13, No. 7, July 2003, `DOI: 10.1109/TCSVT.2003.815173`.
- Alliance for Open Media (AOMedia), *AV1 Bitstream & Decoding Process Specification*, Section 8.2 (*Symbol decoding process*, `read_symbol`, `EC_PROB_SHIFT`, `EC_MIN_PROB`), `https://aomediacodec.github.io/av1-spec/av1-spec.pdf`.
- Tahina Ramananandro, Antoine Delignat-Lavaud, Cédric Fournet, Nikhil Swamy, Tej Chajed, Nadim Kobeissi, and Jonathan Protzenko, *"EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats"*, 28th USENIX Security Symposium (USENIX Security 2019), pp. 1465–1482.
- Yi Cai, Pratap Singh, Zhengyao Lin, Jay Bosamiya, Joshua Gancher, Milijana Surbatovich, and Bryan Parno, *"Vest: Verified, Secure, High-Performance Parsing and Serialization for Rust"*, 34th USENIX Security Symposium (USENIX Security 2025), pp. 6917–6935.

### Reproducible Execution Probes (Observed 2026-11-19, Python 3 on Linux x86_64)

1. **`libwebp` Canonical Huffman Table-Bounds Probe:**
   Standalone Python 3 model translating `huffman_utils.c:BuildHuffmanTable()` (`ROOT_BITS = 8`, `MAX_LEN = 15`, exact C post-decrement order) in both `v1.3.1` write-pass and `v1.3.2` dry-run modes:
   - `DIST (alpha=40)` `[9, 10, 11, 12, 13, 14] + [15]*34`: `Kraft*2^15 = 160 / 32768 (UNDER)`, `v1.3.1` writes `512` entries vs. `410` budget (`+102` entries / `+408 B`, `ret=0`); `v1.3.2` dry-run writes `0` (`ret=0`, `size_match=True`).
   - `DIST (alpha=40)` `[9]*39 + [0]`: `Kraft*2^15 = 2496 / 32768`, `v1.3.1` writes `422` (`+12` entries, `ret=0`); `v1.3.2` dry-run writes `0`.
   - `R/B/A (alpha=256)` `[9]*255 + [0]`: `v1.3.1` writes `638` vs. `630` (`+8`); `GREEN (alpha=280)` `[9]*279 + [0]`: `v1.3.1` writes `662` vs. `654` (`+8`).
2. **`rANS` LIFO Interleaving, Avalanche, Zero-State Spin & AV1 `MSAC` Probe:**
   - 2-lane interleaved `rANS` (`L = 1 << 23`, `scale_bits = 12`, `FREQS = [3072, 512, 256, 256]`, 128 symbols): exact round-trip in `18` payload bytes (`1.125 bits/sym` vs. `1.186` Shannon); single-bit flip at bit 11 of state header byte 1 produced `41/128` mismatches; `x = 0` over 16 zero bytes triggered unbounded renorm read past EOF at `pos = 16, reads = 16`.
   - AV1 `MSAC` (`EC_PROB_SHIFT = 6`, `EC_MIN_PROB = 4`, `cdf = [24576, 16384, 8192, 0]` on `0x12345678`): step 0 decoded `sym=0`, `renorm_bits=3`, `rng=0xffa0`, `cdf_after=[23808, 15872, 7936, 1]`; 8 symbols decoded with `16` total renorm bits (`2.00 bits/sym`, variable sub-bit transitions).

## Revalidation

Each finding can be revalidated cheaply without re-auditing entire codebases:

1. **`libwebp` Huffman Table Construction:** Diff `src/utils/huffman_utils.c` (`BuildHuffmanTable`, `VP8LHuffmanTablesEnsureCapacity`, `VP8LBuildHuffmanTable`) to confirm the zero-write `BuildHuffmanTable(NULL, ...)` pre-pass precedes all table writes and that `WEBP_COUNTED_BY`/`WEBP_BIDI_INDEXABLE` annotations remain intact.
2. **`rANS` / `FSE` Decoder Input-Bounds Safety:** In any rANS implementation derived from `ryg_rans`, inspect the renormalization loop (`while (x < RANS_BYTE_L)`) for an explicit `ptr < end` check and verify post-init `x >= RANS_BYTE_L` and non-zero frequency table checks. For `FSE`, inspect `FSE_buildDTable()` for the `position != 0` completeness check.
3. **`Wuffs` WebP / DEFLATE Verification Strategy:** Inspect `std/webp/decode_webp.wuffs` (`huffman_nodes` dimensions and `overall_n_huffman_groups` upper bound) to see whether Wuffs has moved from `256`-group static node trees to workbuf-backed tables or 2-level LUTs.
4. **`rav1d` Assembly & `DisjointMut` Soundness Boundary:** Check `git ls-files src/` in newer `memorysafety/rav1d` revisions for safe-Rust SIMD replacements (`safe_simd`), grep `src/msac.rs` and `src/loopfilter.rs` for `checkasm` safety justifications, and inspect `src/disjoint_mut.rs` to verify whether `DisjointMut` still disables overlap checking in release builds or has migrated to atomic/compile-time-split borrows.
