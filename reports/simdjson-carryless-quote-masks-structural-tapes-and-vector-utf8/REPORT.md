# Carry-Less Quote Masking, Two-Stage Structural Tapes, and Vectorized UTF-8 Validation in simdjson and simdutf

## Summary

Data-parallel lexers in `simdjson` (v5.2.0) and `simdutf` (v9.4.0) replace branch-misprediction-bound byte-at-a-time finite automata with algebraic transducers over 64-byte SIMD blocks and 64-bit general-purpose bitmasks. Four tightly coupled contracts govern their performance, memory safety, and semantic equivalence to sequential RFC 8259 and RFC 3629 specifications:

1. **Constant-Depth Cross-Chunk Escape and Quote Transduction:** Stage 1 classifies 64 input bytes at a time into 64-bit masks (`backslash`, `quote`, `whitespace`, `op`), resolves arbitrarily long runs of escaping backslashes in $O(1)$ instructions via unsigned borrow propagation against alternating parity bits (`0xAAAAAAAAAAAAAAAA`), and maps unescaped quotes to string interiors via polynomial multiplication over $\mathbb{F}_2[x]$ (`PCLMULQDQ` with `0xFFFFFFFFFFFFFFFF` on x86-64; 6-step shift-XOR cascade on ARM64 to avoid vector-to-GPR move latency). Two 1-bit carries (`next_is_escaped` and `prev_in_string`, the latter sign-replicated to 64 bits) make the chunked transducer bit-for-bit isomorphic to a sequential byte-stream automaton.
2. **Intentional Stage 1 Over-Approximation vs. Stage 2 / On-Demand Refinement:** Stage 1 character classification (`curlified = in | 0x20`) deliberately admits false-positive structural operators—specifically ASCII `<FF>` (`0x0C`) and `<SUB>` (`0x1A`) colliding with `,` (`0x2C`) and `:` (`0x3A`)—and leaves non-quote scalar runs (`true`, `123`, `123e45foo`) syntactically unchecked. Full RFC 8259 validity holds only after DOM Stage 2 materializes the 64-bit scope-linked tape; by contrast, `simdjson::ondemand` ("Validate What You Use") skips unqueried sibling values and therefore **cannot** be treated as a full-document RFC 8259 validator unless the caller exhaustively consumes every token.
3. **3-Nibble Parallel UTF-8 Syndrome Checking and Surrogate-Count Coupling:** `simdutf` (and `simdjson`'s embedded validator) decides all seven RFC 3629 UTF-8 failure classes in parallel across 64-byte blocks by intersecting three 16-entry nibble shuffle tables (`byte_1_high & byte_1_low & byte_2_high`) and XOR-cancelling legitimate third/fourth continuation bytes (`must23_80`). Unvalidated SIMD UTF-8-to-UTF-16 transcoding (`convert_valid_utf8_to_utf16`) relies on validated lead-byte ranges: feeding unvalidated bytes where a non-4-byte lead (`< 0xF0`) is followed by three continuation bytes (`0x80..0xBF`) can desynchronize length precomputation (`count(>= 0xF0)`) from decoder consumption unless masked (`basic_buffer[i] > 0x3C00000`).
4. **Mandatory Tail-Padding (`SIMDJSON_PADDING = 64`) and Fallback-Free 128-Bit Float Parsing:** Unconditional vector loads in Stage 1/Stage 2 string scanning (`parse_string`), SWAR 8-digit/4-digit number routines, and 12-byte `\uXXXX\uXXXX` surrogate-pair lookaheads read past logical token ends. Callers passing buffers without `SIMDJSON_PADDING` (64 readable trailing bytes) to padded entry points risk deterministic `SIGSEGV` page faults on page-aligned allocations unless routed through explicit bounds-guarded paths (`parse_string_safe` with a `SIMDJSON_PADDING + 12` margin). Decimal-to-IEEE-754 conversion via Eisel-Lemire and the Mushtak-Lemire two-limb 128-bit `power_of_five_128` refinement resolves all significands up to 19 decimal digits exactly without `Bigcomp` fallback, delegating only $> 19$ significant digits to multi-precision parsing.

## Applicability

The findings in this report apply to the following pinned artifacts and specifications, interpreted jointly as the reference architecture for high-throughput vectorized text ingestion and FFI/zero-copy memory-safety verification:

- **`simdjson/simdjson` at commit `36c5b3cfce8125aed9e68ec4db5bbbd5c63229f5` (`v5.2.0`):** Primary source for two-stage DOM parsing (`stage1::json_structural_indexer`, `stage2::tape_builder`), lazy cursor iteration (`simdjson::ondemand`), architecture-dispatched SIMD kernels (`haswell` AVX2 + `PCLMULQDQ`, `icelake` AVX-512F/BW/VBMI2 + `PCLMULQDQ`, `arm64` NEON), `SIMDJSON_PADDING` buffer contracts, and `numberparsing::compute_float_64` / `compute_float_32`.
- **`simdutf/simdutf` at commit `177945073a2e44f6ef252aa2b9cf1ecb8e4d2ab0` (`v9.4.0`):** Primary source for the Keiser-Lemire 3-nibble `utf8_lookup4_algorithm.h` validator, AVX-512 ternary-logic specialization (`icelake_utf8_validation.inl.cpp`), UTF-8 code-point/UTF-16 length counters (`utf8_segmenter`), and 12-byte masked `vpshufb` UTF-8-to-UTF-16 transcoding (`avx2_convert_utf8_to_utf16.cpp`).
- **`fastfloat/fast_float` at commit `8ec59686a1430867ba609c2777ca15143dd81003` (`v8.3.3`):** Reference C++ header-only implementation of the Eisel-Lemire and Mushtak-Lemire decimal-to-binary floating-point conversion algorithms (`decimal_to_binary.h`, `ascii_number.h`, `float_common.h`) from which `simdjson`'s number parser derives its invariants.
- **Normative and Algorithmic Specifications:** IETF RFC 8259 (JSON grammar and string/number rules), IETF RFC 3629 (UTF-8 encoding, shortest-form requirement, `U+D800..U+DFFF` surrogate exclusion, and `U+10FFFF` ceiling), Langdale & Lemire (*VLDB J.* 2019, `10.1007/s00778-019-00578-5`), Keiser & Lemire (*SPE* 2021, `10.1002/spe.2920`; *SPE* 2024, `10.1002/spe.3313`), Lemire & Mula (*SPE* 2022, `10.1002/spe.3036`), Lemire (*SPE* 2021, `10.1002/spe.2984`), and Mushtak & Lemire (*SPE* 2023, `10.1002/spe.3198`).

**Host and Target Scope:** Little-endian 64-bit platforms (`x86_64` with SSSE3/AVX2/PCLMULQDQ or AVX-512, and `aarch64` with NEON). `simdjson`'s DOM tape format (`doc/tape.md`) explicitly assumes little-endian 64-bit word layout and caps single-document size at `SIMDJSON_MAXSIZE_BYTES = 0xFFFFFFFF` (4 GiB minus 1 byte) so structural byte offsets fit in unsigned 32-bit integers (`uint32_t`). Hardware execution probes were run on Linux `x86_64` supporting `avx2`, `pclmulqdq`, `ssse3`, and `bmi2`.

## Findings

### 1. Stage 1 SIMD Nibble Classification and Intentional Operator Aliasing

`Basis: normative + source + execution`

RFC 8259 Section 2 defines four ASCII whitespace bytes (`0x20` space, `0x09` horizontal tab, `0x0A` LF, `0x0D` CR) and six structural characters (`[`, `]`, `{`, `}`, `:`, `,`). Instead of testing six equality comparisons and four whitespace comparisons per vector, `simdjson` reduces classification of a 64-byte `simd8x64<uint8_t>` block to two parallel 4-bit table lookups (`src/haswell.cpp:43-94`, `src/icelake.cpp:48-96`):

1. **Curlified Structural Operator Lookup (`| 0x20`):** In ASCII, `[` (`0x5B`) and `]` (`0x5D`) differ from `{` (`0x7B`) and `}` (`0x7D`) solely in bit 5 (`0x20`), while `,` (`0x2C`) and `:` (`0x3A`) already have bit 5 set. Setting bit 5 (`curlified = in | 0x20`) collapses the six structural tokens onto four targets whose low nibbles (`c & 0x0F`) are pairwise distinct:
   - `,` (`0x2C`): low nibble `0xC` $\to$ table slot `12 = ','` (`0x2C`)
   - `:` (`0x3A`): low nibble `0xA` $\to$ table slot `10 = ':'` (`0x3A`)
   - `[` (`0x5B`), `{` (`0x7B`): low nibble `0xB` $\to$ table slot `11 = '{'` (`0x7B`)
   - `]` (`0x5D`), `}` (`0x7D`): low nibble `0xD` $\to$ table slot `13 = '}'` (`0x7D`)
   - All other 12 slots of `op_table` hold `0x00`, which can never equal `in | 0x20` because bit 5 of `in | 0x20` is unconditionally `1`.
   - **False-Positive Control-Character Invariant:** On AVX2/AVX-512, `_mm256_shuffle_epi8(op_table, in)` (and `_mm512_shuffle_epi8`) zeroes the output lane whenever bit 7 (`0x80`) of the index byte `in` is `1`, rejecting all non-ASCII UTF-8 bytes (`0x80..0xFF`). However, among 7-bit ASCII values `[0x00..0x7F]`, setting bit 5 maps two control characters onto `,` and `:`: form feed `<FF>` (`0x0C | 0x20 == 0x2C`, low nibble `0xC`) and substitute `<SUB>` (`0x1A | 0x20 == 0x3A`, low nibble `0xA`). Hardware execution across all 256 byte values confirms that `op` fires on **exactly eight bytes**: `0x0C`, `0x1A`, `0x2C`, `0x3A`, `0x5B`, `0x5D`, `0x7B`, `0x7D`. Outside strings, `0x0C` and `0x1A` are emitted into `structural_indexes` as pseudo-structural starts and rejected only when Stage 2 switches on the raw byte; inside strings, `in.lteq(0x1F)` flags them via `unescaped_chars_error` (`src/generic/stage1/json_structural_indexer.h:242-248`).
2. **Whitespace Lookup:** `whitespace_table` places `' '` (`0x20`) at slot `0`, `'\t'` (`0x09`) at slot `9`, `'\n'` (`0x0A`) at slot `10`, `'\r'` (`0x0D`) at slot `13`, and non-matching sentinels (`100`, `17`, `113`, `2`, `112`) elsewhere (`src/haswell.cpp:46`). Because `_mm256_shuffle_epi8` outputs `0x00` when bit 7 of `in` is set, non-ASCII bytes compare `in == 0x00` (false), while ASCII NUL (`0x00`) compares `0x00 == ' '` (false).
3. **ARM64 NEON Classification Without `PMOVMSKB`:** Because AArch64 NEON lacks a single-instruction byte-MSB-to-GPR bitmask instruction analogous to x86 `vpmovmskb`, `src/arm64.cpp:75-115` classifies four 16-byte registers using `vqtbl1q_u8(op_table, (d + 3) >> 4)` and `vqtbx1q_u8`, masks lane results against positional powers of two (`0x01, 0x02, ..., 0x80`), and folds all four 16-byte vectors into a single 64-bit GPR mask via three levels of `vpaddq_u8` pairwise byte addition.
4. **Scalar Start Identification by Negated Follow-Sets:** Non-quote JSON scalars (`true`, `false`, `null`, numbers) have no opening delimiter. `json_scanner::next` (`src/generic/stage1/json_scanner.h:68-90, 134-157`) defines `scalar = ~(op | whitespace)`, excludes unescaped quotes (`nonquote_scalar = scalar & ~quote`), shifts left by 1 bit with a 1-bit cross-chunk carry `prev_scalar` (`follows_nonquote_scalar = (nonquote_scalar << 1) | prev_scalar; prev_scalar = nonquote_scalar >> 63`), and computes:
   $$\text{structural\_start} = \big(\text{op} \lor (\text{scalar} \land \neg\text{follows\_nonquote\_scalar})\big) \land \neg(\text{in\_string} \oplus \text{quote})$$
   Every structural operator and the first byte of every scalar token outside string interiors (plus every opening quote, since `in_string ^ quote` clears the opening quote bit and sets the closing quote bit) receives a `1` bit. Adjacent `"string"true` still marks `t` because quotes are excluded from `nonquote_scalar`.

### 2. Branchless Odd-Backslash Carry Propagation and $\mathbb{F}_2[x]$ Carry-Less Quote Masking

`Basis: source + derived + execution`

A `"` byte (`0x22`) closes or opens a JSON string if and only if it is preceded by an **even** number of immediately contiguous `\` (`0x5C`) bytes. A contiguous run of $m \ge 1$ backslashes spanning arbitrary 64-byte chunk boundaries alternates between active escape operators (positions $0, 2, 4, \dots$ from the start of the unescaped run) and escaped literal backslashes (positions $1, 3, 5, \dots$).

#### Constant-Time Borrow-Subtraction Escape Scanner

In `src/generic/stage1/json_escape_scanner.h:50-143`, `json_escape_scanner` maintains a 1-bit state `next_is_escaped` $\in \{0, 1\}$ indicating whether bit 0 of the current 64-byte chunk is escaped by an active backslash at bit 63 of the preceding chunk. When `backslash == 0`, `next` short-circuits immediately (`return {next_is_escaped, 0}; next_is_escaped = 0`). Otherwise, let $P = \text{backslash} \land \neg\text{next\_is\_escaped}$ be the mask of backslashes not already consumed at bit 0, and let $O = \texttt{0xAAAAAAAAAAAAAAAA}_{16}$ be the mask of all odd bit indices $\{1, 3, \dots, 63\}$. The scanner computes:

$$\begin{aligned}
M &= (P \ll 1) \lor O \pmod{2^{64}} \\
D &= (M - P) \bmod 2^{64} \\
E_{\text{term}} &= D \oplus O \\
\text{escaped} &= E_{\text{term}} \oplus (\text{backslash} \lor \text{next\_is\_escaped}) \\
\text{escape} &= E_{\text{term}} \land \text{backslash} \\
\text{next\_is\_escaped}' &= \text{escape} \gg 63
\end{aligned}$$

**Algebraic Proof of Run-Parity Equivalence:** Consider any maximal contiguous run of $1$-bits in $P$ at bit positions $[a, b]$ ($0 \le a \le b \le 63$), where bit $a-1$ (if $a > 0$) is $0$ in $P$ and bit $b+1$ (if $b < 63$) is $0$ in $P$:
- In $P \ll 1$, bits $[a+1, b]$ (and $b+1$ if $b < 63$) are $1$, while bit $a$ is $0$.
- **Case 1 ($a$ is even):** Bit $a$ of $O$ is $0$, so bit $a$ of $M = (P \ll 1) \lor O$ is $0$, whereas bit $a$ of $P$ is $1$. Subtracting $P$ from $M$ generates an arithmetic borrow at bit $a$. Across $j \in [a+1, b]$, bit $j$ of $M$ is $1$ (since $P \ll 1$ has $1$ at $j$) and bit $j$ of $P$ is $1$, so $1 - 1 - \text{borrow} = -1 \equiv 1 \pmod 2$: the borrow propagates unbroken through the entire run and is absorbed at bit $b+1$ (where $P_{b+1} = 0$ and $(P \ll 1)_{b+1} = 1$, giving $1 - 0 - 1 = 0$ with borrow $0$; if $b = 63$, it wraps mod $2^{64}$). Thus $D$ has `[a..b] = 11...1` and bit `b+1 = 0` (whereas $O_{b+1}$ was $0$ if $b+1$ even, or if $b+1$ is odd then $M_{b+1}=1$, absorbing the borrow to $0$). XORing with $O$ flips odd bits, turning `[a..b]` into alternating `1010...` starting with `1` at even index $a$, and setting bit $b+1$ to $1$ iff $b - a + 1$ is odd!
- **Case 2 ($a$ is odd):** Bit $a$ of $O$ is $1$, so bit $a$ of $M$ is $1$ and $1 - 1 = 0$ with **no borrow**! Across $j \in [a+1, b]$, $M_j = 1$ and $P_j = 1$, giving $1 - 1 = 0$. At $b+1$ (if $b < 63$), $(P \ll 1)_{b+1} = 1$ and $P_{b+1} = 0$, so $D_{b+1} = 1$. Thus $D$ has `[a..b] = 00...0`. XORing with $O$ turns `[a..b]` into alternating `1010...` starting with `1` at odd index $a$, and sets bit $b+1$ to $1 \oplus O_{b+1}$, which again equals $1$ iff $b - a + 1$ is odd!

Exhaustive execution over all $2^{16} \times 2 = 131{,}072$ `(backslash, next_is_escaped)` states and 5,000 adversarial 256-byte multi-chunk streams confirms zero discrepancies against a sequential RFC 8259 escape transducer.

#### $\mathbb{F}_2[x]$ Carry-Less Prefix-XOR and ISA Microarchitectural Trade-Offs

Once `quote = in.eq('"') & ~escaped` isolates unescaped quotes (`src/generic/stage1/json_string_scanner.h:65`), toggling string-interior membership at each set bit of `quote` is equivalent to the inclusive prefix-XOR $y_k = \bigoplus_{j=0}^k q_j$ for $0 \le k < 64$. Viewing $Q(x) = \sum_{j=0}^{63} q_j x^j \in \mathbb{F}_2[x]$ and $U(x) = \sum_{i=0}^{63} x^i = \texttt{0xFFFFFFFFFFFFFFFF}_{16}$:

$$(Q(x) \cdot U(x)) \bmod x^{64} = \sum_{k=0}^{63} \left(\bigoplus_{j=0}^{k} q_j\right) x^k$$

`simdjson` lowers `prefix_xor` differently across architectures due to register-file transfer latencies:

| Backend | Source File | Implementation | Microarchitectural Rationale |
| :--- | :--- | :--- | :--- |
| `haswell`, `icelake`, `westmere` | `include/simdjson/{haswell,icelake,westmere}/bitmask.h:18-24` | `_mm_cvtsi128_si64(_mm_clmulepi64_si128(_mm_set_epi64x(0ULL, bitmask), _mm_set1_epi8('\xFF'), 0))` | Single `vpclmulqdq` / `pclmulqdq` instruction (1 $\mu$op, ~3–4 cycle latency on modern x86-64); low `vmovq` between GPR and XMM is 1–2 cycles. |
| `arm64` | `include/simdjson/arm64/bitmask.h:17-38` | 6-step GPR Kogge-Stone shift-XOR: `bitmask ^= bitmask << 1; ...; bitmask ^= bitmask << 32;` | Avoids `vmull_p64` (`PMULL`): first, `PMULL` requires optional `__ARM_FEATURE_CRYPTO`; second, moving `bitmask` GPR $\to$ SIMD (`fmov`, 3 cycles on Neoverse N1 / 5 cycles on Cortex-A72) and SIMD $\to$ GPR (`fmov`, 2–5 cycles) costs 5–10 extra cycles on the critical path while integer ALUs are otherwise idle during vector Stage 1 work. |

Cross-chunk state is maintained by `in_string = prefix_xor(quote) ^ prev_in_string` (`json_string_scanner.h:73-78`), where `prev_in_string = uint64_t(static_cast<int64_t>(in_string) >> 63)` broadcasts bit 63 via arithmetic right shift to `0x0000000000000000` (outside string) or `0xFFFFFFFFFFFFFFFF` (inside string). Under this convention, `in_string` has `1` on the opening `"` and all interior characters, and `0` on the closing `"`. At end-of-input, `json_string_scanner::finish()` returns `UNCLOSED_STRING` iff `prev_in_string != 0`.

### 3. Bit Compression, Scope-Linked 64-Bit DOM Tapes, and On-Demand Cursor Contracts

`Basis: documentation + source`

#### Bit-Mask Extraction (`bit_indexer::write`)

Stage 1 flattens each 64-bit `structural_start` mask into a contiguous array of 32-bit byte offsets `uint32_t *structural_indexes`:
- **Generic x86-64 (`src/generic/stage1/json_structural_indexer.h:57-123`):** Uses `trailing_zeroes(bits)` (`tzcnt`) and `clear_lowest_bit(bits)` (`blsr`, `bits & (bits - 1)`), unrolled in groups of `STEP = 4` up to `STEP_UNTIL = 24` before a scalar tail loop. Because unrolled stores write up to 3 dead slots past `cnt`, `structural_indexes` must be over-allocated accordingly.
- **ARM64 (`src/arm64.cpp:30-47`):** Reverses the 64-bit word once (`rbit`) and extracts leading zeros (`clz`), unrolling 4 unconditionally and then stepping by 2 up to 24 to reduce wasted stores on typical JSON densities (4–8 structurals per 64 bytes).
- **Ice Lake AVX-512 VBMI2 (`src/icelake.cpp:121-152`):** Eliminates scalar bit-extraction loops entirely via `_mm512_maskz_compress_epi8(bits, [0..63])` (`vpcompressb`), packing all matching byte offsets of the 64-byte block in one vector instruction and widening 16-byte slices to 32-bit integers via `_mm512_cvtepu8_epi32`.

#### DOM Stage 2 Scope-Linked 64-Bit Tape Layout

In DOM mode (`doc/tape.md:68-144`, `include/simdjson/internal/tape_type.h:10-24`), Stage 2 walks `structural_indexes` once to validate grammar and emit a flat little-endian `uint64_t` tape plus a separate UTF-8 string buffer:

| Node Kind | Tag (`bits 63..56`) | Word 0 Payload (`bits 55..0`) | Word 1 (`uint64_t`) | Key Invariant / Cost |
| :--- | :--- | :--- | :--- | :--- |
| Document root open / close | `'r'` (`0x72`) | Open: index of closing `'r'`; Close: `0` | None | `tape[0] & 0x00FFFFFFFFFFFFFF` gives total document tape span. |
| Object open `{` / Array open `[` | `'{'` (`0x7B`) / `'['` (`0x5B`) | `bits 55..32`: 24-bit saturating child/pair count $\min(c, 16{,}777{,}215)$; `bits 31..0`: $1 + \text{close\_idx}$ | None | Subtree skip is $O(1)$ (`idx = uint32_t(word)`). Counts $\ge 2^{24}-1$ (`0xFFFFFF`) saturate and require linear scan for exact `.size()`. |
| Object close `}` / Array close `]` | `'}'` (`0x7D`) / `']'` (`0x5D`) | `bits 31..0`: tape index of matching `'{'` or `'['` | None | Bidirectional linking allows $O(1)$ validation and reverse navigation; caps tape index space at 32 bits. |
| String `"` | `'"'` (`0x22`) | 56-bit byte offset into string buffer | None | String buffer stores `[uint32_t byte_len][UTF-8 bytes][0x00]`, supporting embedded NULs (`\u0000`) via explicit 32-bit length. |
| Signed / Unsigned 64-bit int | `'l'` (`0x6C`) / `'u'` (`0x75`) | `0` | Raw `int64_t` / `uint64_t` | Stored inline on main tape (2 words) for cache locality. |
| IEEE 754 binary64 float | `'d'` (`0x64`) | `0` | Raw `double` bits | Stored inline on main tape (2 words). |
| Big integer (opt-in) | `'Z'` (`0x5A`) | 56-bit byte offset into string buffer | None | Default returns `BIGINT_ERROR` outside `[INT64_MIN, UINT64_MAX]`; `number_as_string(true)` writes raw digits to string buffer. |
| Literals `true`, `false`, `null` | `'t'`, `'f'`, `'n'` | `0` | None | Single 64-bit word (`tag << 56`). |

#### On-Demand Lazy Cursor Semantics and Sentinel Padding

`simdjson::ondemand` (`doc/ondemand_design.md:19-90, 235-263`; Keiser & Lemire *SPE* 2024) runs the **exact same Stage 1** structural indexer and UTF-8 validator, then exposes a single forward-only pointer over `structural_indexes` with **no Stage 2 tape**:

- **Elimination of Type Blindness:** DOM Stage 2 must branch on every scalar value to decide whether it is `int64`, `uint64`, `double`, `bool`, or `null`. On-Demand defers value parsing until the caller requests a concrete C++ type (e.g., `uint64_t(doc["id"])`), invoking a type-specialized parser directly on the raw input buffer at `*structural_cursor`.
- **Three-Slot Sentinel Termination Trick (`src/generic/stage1/json_structural_indexer.h:276-298`):** After finding $n = \text{n\_structural\_indexes}$ tokens in a buffer of length `len`, Stage 1 unconditionally writes:
  ```cpp
  parser.structural_indexes[n]     = uint32_t(len);
  parser.structural_indexes[n + 1] = uint32_t(len);
  parser.structural_indexes[n + 2] = 0;
  ```
  If malformed truncated JSON (such as `{"a": [,,`) causes an On-Demand iterator to advance past index $n - 1$, it reads `buf[len]` twice in succession. Because only `[`, `]`, and `}` can repeat legally in JSON, repeating `]` or `}` cannot match an opening document token (`structural_indexes[2]` backtracks to `0`), and repeating `[` forces a mismatch if the root `[` is required to close with `]`. This bounds cursor runaway without per-token end-of-array branches.
- **Critical Security Boundary (Partial Validation):** On-Demand guarantees Stage 1 invariants globally (valid UTF-8 when `SIMDJSON_UTF8VALIDATION=1`, balanced quotes, no unescaped `<= 0x1F` control bytes inside strings), **not** RFC 8259 grammar validity on unvisited subtrees. An input such as `{"used": 1, "unused": [1 2 truX]}` succeeds if the caller reads `doc["used"]` and discards `doc` without iterating `"unused"`. Furthermore, out-of-order iterator use or reiterating a consumed array/scalar is a contract violation (`DEVELOPMENT_CHECKS` asserts in debug builds; undefined cursor state in release builds without `NDEBUG` checks).

### 4. Sub-Instruction-Per-Byte SIMD UTF-8 Validation and Transcoding (`simdutf`)

`Basis: normative + source + execution`

RFC 3629 restricts valid UTF-8 sequences to 1–4 bytes encoding scalar values in $[\texttt{U+0000}, \texttt{U+D7FF}] \cup [\texttt{U+E000}, \texttt{U+10FFFF}]$. A byte stream is invalid iff it exhibits at least one of seven local anomalies:

| Bit Flag | Constant (`utf8_lookup4_algorithm.h:16-36`) | Hex | Invalid Adjacent Byte-Pair / Length Condition (`prev1`, `curr`) | Concrete Specimen |
| :--- | :--- | :--- | :--- | :--- |
| Bit 0 | `TOO_SHORT` | `0x01` | Lead byte (`11______`) followed immediately by ASCII (`0_______`) or another lead (`11______`), or truncated lead at EOF | `\xC2a`, `\xE0\xA0a` |
| Bit 1 | `TOO_LONG` | `0x02` | ASCII byte (`0_______`) followed immediately by continuation byte (`10______`) | `a\x80` |
| Bit 2 | `OVERLONG_3` | `0x04` | `0xE0` (`11100000`) followed by `0x80..0x9F` (`100_____`), encoding $\le \texttt{U+07FF}$ in 3 bytes | `\xE0\x9F\xBF` |
| Bit 3 | `TOO_LARGE` | `0x08` | `0xF4` followed by `0x90..0xBF`, or `0xF5..0xFF` followed by `0x90..0xBF` ($> \texttt{U+10FFFF}$) | `\xF4\x90\x80\x80` (`U+110000`) |
| Bit 4 | `SURROGATE` | `0x10` | `0xED` (`11101101`) followed by `0xA0..0xBF` (`101_____`), encoding UTF-16 surrogates `U+D800..U+DFFF` | `\xED\xA0\x80` (`U+D800`) |
| Bit 5 | `OVERLONG_2` | `0x20` | `0xC0` or `0xC1` (`1100000_`) followed by any continuation (`10______`), encoding $\le \texttt{U+007F}$ | `\xC0\x80` (Modified UTF-8 NUL) |
| Bit 6 | `OVERLONG_4` / `TOO_LARGE_1000` | `0x40` | `0xF0` + `0x80..0x8F` (overlong 4-byte $\le \texttt{U+FFFF}$) **or** `0xF5..0xFF` + `0x80..0x8F` ($> \texttt{U+10FFFF}$); shares bit 6 safely because `prev1` low nibbles `{0}` vs `{5..15}` are disjoint! | `\xF0\x8F\xBF\xBF`, `\xF5\x80\x80\x80` |
| Bit 7 | `TWO_CONTS` | `0x80` | Continuation (`10______`) followed by continuation (`10______`), **unless** cancelled by a 3-byte lead at `-2` or 4-byte lead at `-3` | `\xC2\x80\x80`, `\xE0\xA0\x80\x80` |

#### Three-Nibble Syndrome Intersection and XOR Continuation Cancellation

In `simdutf/src/generic/utf8_validation/utf8_lookup4_algorithm.h:8-109`, for each lane $i$, let `prev1`, `prev2`, `prev3` be bytes $i-1, i-2, i-3$ (bridged across chunks via `prev_input_block`):
1. `sc = byte_1_high[prev1 >> 4] & byte_1_low[prev1 & 0x0F] & byte_2_high[curr >> 4]` computes the exact 8-bit syndrome of the 2-byte window `(prev1, curr)`. On Ice Lake (`src/icelake/icelake_utf8_validation.inl.cpp:3-27`), the two bitwise ANDs collapse into a single `_mm512_ternarylogic_epi64(byte_1_high, byte_1_low, byte_2_high, 128)` (`vpternlogq` with immediate `0x80 = A & B & C`).
2. Every valid 3-byte or 4-byte UTF-8 character intentionally raises `sc == TWO_CONTS` (`0x80`) on its second (and third) continuation byte because `(prev1, curr)` are both `10______` (and no other error bit can fire when `prev1` is `10______`, since `byte_1_high[8..11]` equals `TWO_CONTS` alone).
3. `must_be_2_3_continuation(prev2, prev3)` (`src/haswell.cpp:100-104`, `icelake_utf8_validation.inl.cpp:34-45`) computes unsigned saturating subtractions:
   $$\text{is\_third} = \text{subs\_epu8}(\text{prev2}, \texttt{0xE0} - \texttt{0x80}), \qquad \text{is\_fourth} = \text{subs\_epu8}(\text{prev3}, \texttt{0xF0} - \texttt{0x80})$$
   Note the implementation difference between Haswell (`subs_epu8(prev2, 0x60)` $\ge \texttt{0x80}$ iff `prev2 >= 0xE0`, masked directly with `& 0x80`) and Ice Lake (`subs_epu8(prev2, 0xDF)` $> 0$ iff `prev2 >= 0xE0`, saturated-added with `0x7F` to set bit 7 `0x80` before `_mm512_ternarylogic_epi32(..., 0b1101010)` computing `(A & B) ^ C`): in both encodings, `must23_80` equals `0x80` at lane $i$ iff `prev2 >= 0xE0` (3- or 4-byte lead two bytes back) or `prev3 >= 0xF0` (4-byte lead three bytes back).
4. `error |= (sc ^ must23_80)`:
   - If lane $i$ is legitimately the 3rd byte of a 3/4-byte sequence or 4th byte of a 4-byte sequence, `curr` is a continuation (`sc == 0x80`) and `must23_80 == 0x80`, so `0x80 ^ 0x80 == 0x00`.
   - If lane $i$ is NOT a continuation (`curr < 0x80` or `curr >= 0xC0`) when `must23_80 == 0x80`, then `sc` has bit 7 equal to `0` (`TOO_SHORT` or `0`), so `sc ^ 0x80` sets bit 7 (`!= 0`), catching missing 3rd/4th continuation bytes!
   - If `curr` is a continuation following a 2-byte lead (`0xC2..0xDF` at `-2`), `must23_80 == 0x00` while `sc == 0x80`, leaving `0x80` set and catching excess continuations!
5. **Cross-Block Truncation Latch (`prev_incomplete`):** If a 64-byte block ends with a 4-byte lead in the last 3 bytes (`>= 0xF0` at index 61), a 3/4-byte lead in the last 2 bytes (`>= 0xE0` at index 62), or any lead in the last byte (`>= 0xC0` at index 63), `is_incomplete` (`utf8_lookup4_algorithm.h:115-154`) records a non-zero vector via saturating subtraction against `[..., 0xEF, 0xDF, 0xBF]`. If the *next* 64-byte block takes the `is_ascii(input)` fast path (`_mm256_movemask_epi8 == 0`, skipping `check_utf8_bytes`) or if EOF is reached (`check_eof()`), `this->error |= this->prev_incomplete` catches the dangling multibyte prefix in 1 instruction. Execution across all 19 canonical boundary vectors and 20,000 random byte sequences matches Python's strict RFC 3629 decoder on 100% of inputs.

#### SIMD UTF-8 Length Formula and Transcoding Overflow Guard

`simdutf`'s `utf8_counters` (`utf8_lookup4_algorithm.h:167-180`) computes both code-point length and UTF-16 `char16_t` length from two popcounts over validated UTF-8 of byte length $N$:
$$\text{codepoints} = N - \#\{\text{bytes } b : \text{int8}(b) < -64\}, \qquad \text{utf16\_words} = N - \#\{\text{continuations}\} + \#\{\text{bytes } b : b \ge \texttt{0xF0}\}$$
because every UTF-8 scalar has exactly one non-continuation byte (`int8(b) >= -64`, i.e., `b < 0x80` or `b >= 0xC0`), and only 4-byte leads (`>= 0xF0`, encoding `U+10000..U+10FFFF`) emit 2 UTF-16 surrogate code units instead of 1.

In `src/haswell/avx2_convert_utf8_to_utf16.cpp:8-195`, `convert_masked_utf8_to_utf16` extracts a 12-bit end-of-code-point mask (`~continuation_mask & 0xFFF`), dispatches fast paths for pure ASCII (`0xFFF`, 12 bytes $\to$ 12 `char16_t`), eight 2-byte scalars (`0xAAAA`, 16 bytes $\to$ 8 `char16_t`), and four 3-byte scalars (`0x924`, 12 bytes $\to$ 4 `char16_t`), or indexes the 209-entry `utf8bigindex` + `shufutf8` `vpshufb` permutation table (`idx < 64`: 6 scalars; `idx < 145`: 4 scalars; `idx < 209`: 2 scalars including 4-byte surrogate pairs). Note two critical memory-safety invariants documented directly in `avx2_convert_utf8_to_utf16.cpp`:
1. **SIMD Store Overwrite Slack (Lines 101–122):** Both the 6-unit (`idx < 64`) and 4-unit (`idx < 145`) branches execute 16-byte `_mm_storeu_si128` writes into `utf16_output`, advancing `utf16_output` by 6 `char16_t` (4-byte overwrite slack) or 4 `char16_t` (8-byte overwrite slack); callers internal to `simdutf` guard the tail with a temporary buffer before copying final elements.
2. **Masquerading 4-Byte Lead Hazard on Unvalidated Input (Lines 125–153, 181):** If unvalidated garbage enters `convert_valid_utf8_to_utf16` where a byte `< 0xF0` (e.g., `0xE0`) is followed by 3 continuation bytes (`0xA0 0x80 0x80`), the continuation mask treats all 4 bytes as one unit (`idx` in `[145, 209)`), yet `utf8_counters` did **not** count `0xE0` in `four_byte` (`< 0xF0`). Emitting a surrogate pair would overflow a buffer sized via `utf16_length_from_utf8`! `avx2_convert_utf8_to_utf16.cpp` prevents surrogate emission unless `basic_buffer[i] > 0x3C00000` (which holds iff the leading byte shifted right by 6 exceeds `0xF0000000 >> 6 == 0x3C00000`, i.e., `lead >= 0xF1`, or `0xF0` with non-zero payload bits). Even with that local guard, `convert_valid_*` functions skip `utf8_checker` entirely and **must never** be exposed to untrusted bytes without prior `validate_utf8`.

### 5. Tail-Padding Contracts (`SIMDJSON_PADDING`) and Overread Page-Fault Surfaces

`Basis: source + execution`

`include/simdjson/base.h:42` defines `constexpr size_t SIMDJSON_PADDING = 64;`. Multiple hot paths in `simdjson` execute unmasked wide reads or fixed-width stores past logical token boundaries:

| Subsystem | Source Location | Speculative Read / Write Span | Consequence of Omitting Padding / Slack |
| :--- | :--- | :--- | :--- |
| Stage 1 block reader (padded mode) | `src/generic/stage1/json_structural_indexer.h:216` | Reads full 64- or 128-byte vector blocks; tail copied via `get_remainder_padded` | Unmapped page fault (`SIGSEGV`) if caller wraps raw pointer in `padded_string_view(ptr, len, len)` without `+ 64` readable bytes (unless `_unpadded` mode is used). |
| Stage 2 SIMD string unescaping | `src/generic/stage2/stringparsing.h:151-198` (`parse_string`) | Copies `BYTES_PROCESSED` (32 B on AVX2, 64 B on AVX-512) from `src` to `dst` before checking quote index, plus `+12` bytes on `\uD800\uDC00` surrogate lookahead | Over-reads `src` by up to `max(BYTES_PROCESSED, bs_dist + 12)` and over-writes `dst` by `SIMDJSON_PADDING` bytes; annotated `SIMDJSON_NO_SANITIZE_MEMORY` (`src/haswell.cpp:146`) because uninitialized padding bytes may be loaded into vector registers. |
| Stage 2 bounds-safe string path | `src/generic/stage2/stringparsing.h:214-260` (`parse_string_safe`) | Fast loop guarded by `src + SIMDJSON_PADDING + 12 <= buf_end`, then copies tail to stack scratch | Eliminates `src` overread for unpadded inputs; note the mandatory `+ 12` surrogate margin beyond `SIMDJSON_PADDING` when `BYTES_PROCESSED == 64` (`icelake`). |
| SWAR digit validation / parsing | `include/simdjson/generic/numberparsing.h:563-598` | `std::memcpy(&val, chars, 8)` (`static_assert(7 <= SIMDJSON_PADDING)`) and 4-byte SWAR `memcpy` | Over-reads up to 7 bytes past a 1-byte final JSON number (e.g., `[1]` or top-level `0`). |
| Float serialization (`to_chars`) | `include/simdjson/common_defs.h:11-37` | Fixed 16/17-byte `memcpy`/`memset` past ~24-char Dragonbox output | Requires `to_chars_buffer_size = 40` writable bytes; shrinking below 40 corrupts adjacent stack/heap memory. |

**Empirical Guard-Page Reproduction (`Basis: execution`):** Placing the valid 7-byte JSON document `{"a":1}` at `page_end - 7` immediately before an `mprotect(..., PROT_NONE)` page and invoking the 64-byte AVX2 Stage 1 classifier terminates the process deterministically with `SIGSEGV` (`signal 11`), whereas placing the same 7 bytes at `page_end - 71` with 64 space bytes (`0x20`) in `[page_end - 64, page_end)` succeeds with `op_mask = 0x51` (`{` at bit 0, `:` at bit 4, `}` at bit 6). Callers wrapping zero-copy network or `mmap` slices **must** verify `capacity - offset >= len + 64` before constructing `padded_string_view`, or copy into `padded_string` when at page/buffer tails.

### 6. Eisel-Lemire and Mushtak-Lemire Exact Floating-Point Conversion

`Basis: source + derived + execution`

Parsing a decimal scientific token $w \times 10^q$ (normalized to an integer significand $w \in [1, 10^{19}-1] \subset [1, 2^{64}-1]$ and base-10 exponent $q$) into a correctly rounded IEEE 754 binary64 (`double`, $p = 53$ mantissa bits) or binary32 (`float`, $p = 24$ mantissa bits) proceeds through three tiers in `include/simdjson/generic/numberparsing.h:65-558` and `fastfloat/fast_float/include/fast_float/decimal_to_binary.h:20-215`:

1. **Clinger Exact-Float Fast Path (`numberparsing.h:77-102, 363-380`):** When `FLT_EVAL_METHOD` $\in \{0, 1\}$, every integer $w \le 2^{53}-1 = 9{,}007{,}199{,}254{,}740{,}991$ and every $10^{|q|}$ for $|q| \le 22$ ($5^{22} = 2{,}384{,}185{,}791{,}015{,}625 < 2^{53}$) is **exact** in binary64 (analogously $w \le 2^{24}-1$ and $|q| \le 10$ in binary32). A single hardware `double` multiply (`q >= 0`) or divide (`q < 0`) is guaranteed by IEEE 754 round-to-nearest-even to return the exact rounded result.
2. **Eisel-Lemire 128-Bit Truncated Multiplication + Mushtak-Lemire Two-Limb Refinement (`numberparsing.h:157-313`, `decimal_to_binary.h:21-47, 71-73`):**
   - **Exact Fixed-Point Binary Exponent:** For all $q \in [-400, 349]$ (covering the entire finite binary64 range $q \in [-342, 308]$), `(((152170 + 65536) * q) >> 16)` (biased by `2048 * 65536` prior to C++20 for portable floor-shift on negative `q`) equals $\lfloor q \log_2 5 \rfloor + q$ **with zero error across all 750 integer exponents** (verified exhaustively against arbitrary-precision `5**q` bit lengths).
   - **64-Bit Normalization and Primary Product:** Left-shifting $w$ by `lz = clz(w)` places $w' = w \cdot 2^{\text{lz}} \in [2^{63}, 2^{64}-1]$. Looking up the precomputed 128-bit truncated significand $(T_{\text{hi}}[q], T_{\text{lo}}[q])$ of $5^q$ (also normalized to $[2^{63}, 2^{64}-1]$), the 128-bit product $P_1 = w' \times T_{\text{hi}}[q]$ lies in $[2^{126}, 2^{128})$, so its MSB is at bit 127 (`upperbit = 1`) or bit 126 (`upperbit = 0`).
   - **Ambiguity Mask and Fallback Elimination:** Extracting 53 mantissa bits + 1 rounding bit + 1 `upperbit` slack requires the top **55 bits** of $w' \times 5^q$ (26 bits for binary32). `P_1.high` can differ in its top 55 bits from the true product $w' \times (T_{\text{hi}} + T_{\text{lo}} \cdot 2^{-64})$ **only if** adding $\lfloor (w' \times T_{\text{lo}}) / 2^{64} \rfloor < w' < 2^{64}$ into `P_1.low` carries across all 9 low bits `[8:0]` of `P_1.high`—which requires `(P_1.high & 0x1FF) == 0x1FF` (38 bits `0x3FFFFFFFFF` for binary32). When `(P_1.high & 0x1FF) == 0x1FF` triggers (~$2^{-9}$ of random products), adding `secondproduct.high = mulhi64(w', T_lo[q])` into `P_1.low` (with carry into `P_1.high`) resolves the product. Mushtak & Lemire (*SPE* 2023, `10.1002/spe.3198`) proved that for **all** $w < 10^{19} < 2^{64}$ and all finite IEEE 754 exponents $q$, this 128-bit table entry has no unresolved midpoint collisions—eliminating `Bigcomp` fallback entirely for $\le 19$ significant digits!
   - **Exact Midpoint Tie-to-Even Window (`numberparsing.h:277-293, 469-475`):** An exact halfway value $(2m + 1) \cdot 2^k$ requires $w \cdot 5^q \cdot 2^q = (2m+1) \cdot 2^k$. For $q \ge 0$, $5^q \mid (2m+1) < 2^{54} \implies q \le 23$ ($5^{23} < 2^{54} < 5^{24}$); for $q < 0$, $w \ge (2m+1) \cdot 5^{-q} > 2^{53} \cdot 5^{-q}$ and $w < 2^{64} \implies 5^{-q} < 2^{11} \implies q \ge -4$ (for binary32: $q \in [-17, 10]$). Thus tie-to-even rounding is checked *only* when `lower <= 1 && -4 <= power && power <= 23 && (mantissa & 3) == 1 && (mantissa << (upperbit + 9)) == upper`.
   - **Subnormal-to-Normal Rounding Promotion (`numberparsing.h:243-265`):** When `real_exponent <= 0`, shifting right and rounding `mantissa` can carry bit 52 to `1` (specifically at the threshold `2.2250738585072013e-308` $\to$ `0x0010000000000000`, `exp = 1`, minimum positive normal, whereas `2.2250738585072011e-308` $\to$ `0x000fffffffffffff`, `exp = 0`, maximum subnormal). Both `simdjson` and `fast_float` test `mantissa < (1ULL << 52)` *after* rounding to set `real_exponent = 0` vs `1`.
3. **$> 19$ Significant-Digit Fallback and Binary32 Double-Rounding Avoidance (`numberparsing.h:535-558`):** Only when a JSON number has $> 19$ significant nonzero digits (truncating the 64-bit accumulator `i`) does `simdjson` invoke `parse_float_fallback` (`from_chars` / `from_chars_float` using `bigint` / Dragonbox-style exact digit comparison). Crucially, `compute_float_32` uses `from_chars_float` directly rather than casting `double` $\to$ `float`, avoiding IEEE 754 double-rounding errors at binary32 midpoints. Note also that RFC 8259 forbids `NaN` and `Infinity`; `simdjson` rejects overflow (`real_exponent > 2046` or `> 254`) with `NUMBER_ERROR` unless `SIMDJSON_ENABLE_NAN_INF=1`.

## Boundaries

- **Big-Endian Host Architectures (`unsupported`):** `simdjson`'s DOM tape representation (`doc/tape.md:6`) and SWAR digit parsers (`SIMDJSON_SWAR_NUMBER_PARSING`) assume little-endian byte order; big-endian PowerPC (`ppc64`) builds restrict or swap vector paths, and raw DOM tape serialization is not endian-portable.
- **Documents Larger Than `4 GiB - 1` (`unsupported`):** `SIMDJSON_MAXSIZE_BYTES = 0xFFFFFFFF` (`include/simdjson/base.h:28`) is a hard representation ceiling in `simdjson` v5.2.0 because `structural_indexes` (`uint32_t`) and DOM container jump payloads (`bits 31..0`) are 32-bit unsigned offsets. Inputs $> 4\text{ GiB} - 1$ return `CAPACITY` unless split via `document_stream` (`parse_many` / `iterate_many`) into batches shorter than `4 GiB`.
- **Using `simdjson::ondemand` as a Complete JSON Syntax Validator (`known not to apply`):** Passing `ondemand::parser::iterate` and reading a subset of fields does **not** establish that unvisited fields, trailing tokens, or skipped array elements satisfy RFC 8259 (`doc/ondemand_design.md:89`). Applications acting as security gateways or canonicalizing proxies that forward raw JSON bytes downstream must either use DOM `parser::parse` or exhaustively traverse/re-serialize every field.
- **Duplicate Object Keys and Canonical Uniqueness (`known not to apply`):** RFC 8259 Section 4 states that object member names *should* be unique, without mandating rejection. Neither DOM `tape_builder` nor `ondemand::object` rejects duplicate keys by default; On-Demand linear field lookup stateful wraparound can expose different duplicate entries than downstream map-based parsers (a classic JSON parser-differential vector unless keys are deduplicated or rejected explicitly).
- **Calling `simdutf::convert_valid_utf8_to_*` on Untrusted Inputs (`known not to apply`):** While `avx2_convert_utf8_to_utf16.cpp:181` contains a local mask guard (`basic_buffer[i] > 0x3C00000`) against masquerading 4-byte leads in one branch, `convert_valid_*` routines omit `utf8_checker` syndrome checks (`OVERLONG_*`, `SURROGATE`, `TOO_LARGE`, truncated tails) and may emit ill-formed UTF-16 unpaired surrogates or read past corrupt multi-byte boundaries. Untrusted inputs must call `convert_utf8_to_utf16_with_errors` or `validate_utf8` first.
- **LoongArch (`lsx`/`lasx`) and RISC-V Vector (`rvv-vls`) Performance & Errata (`not examined`):** While `simdjson` v5.2.0 and `simdutf` v9.4.0 contain `lsx`, `lasx`, `ppc64`, and `rvv-vls` backends in their source trees, only the `haswell`, `icelake`, `arm64`, and generic Stage 1/Stage 2 kernels were directly audited and micro-probed in this report.
- **Locale-Dependent Decimal Separators and Hexadecimal Floats (`unsupported` in `simdjson`, configurable in `fast_float`):** `simdjson` strictly enforces the RFC 8259 number grammar (no leading `+`, no leading `.5` or trailing `1.`, no `01` leading zeros, period `.` only); `fast_float` v8.3.3 supports C++17 `std::chars_format` options (`hex`, custom decimal point) that do not apply to `simdjson`.

## Evidence

### Primary Source Locations Examined

- **`simdjson/simdjson` (`36c5b3cfce8125aed9e68ec4db5bbbd5c63229f5`, v5.2.0):**
  - `include/simdjson/simdjson_version.h:7-23` (`SIMDJSON_VERSION = "5.2.0"`).
  - `include/simdjson/base.h:27-50` (`SIMDJSON_MAXSIZE_BYTES = 0xFFFFFFFF`, `SIMDJSON_PADDING = 64`, `DEFAULT_MAX_DEPTH = 1024`).
  - `include/simdjson/common_defs.h:11-51` (`to_chars_buffer_size = 40` write-past requirement; `from_chars` / `from_chars_float` declarations).
  - `include/simdjson/haswell/bitmask.h:18-24` & `include/simdjson/icelake/bitmask.h:18-24` (`_mm_clmulepi64_si128` `prefix_xor`).
  - `include/simdjson/arm64/bitmask.h:17-38` (6-step shift-XOR `prefix_xor` and `fmov` vs `PMULL` cycle analysis).
  - `src/generic/stage1/json_escape_scanner.h:17-144` (`ODD_BITS = 0xAAAAAAAAAAAAAAAAULL`, `next_escape_and_terminal_code` borrow-subtraction algebra, `next_is_escaped` carry).
  - `src/generic/stage1/json_string_scanner.h:14-92` (`json_string_block`, `prefix_xor(quote) ^ prev_in_string`, `UNCLOSED_STRING`).
  - `src/generic/stage1/json_scanner.h:32-161` (`structural_start`, `follows_nonquote_scalar`, `prev_scalar` carry).
  - `src/haswell.cpp:43-159`, `src/icelake.cpp:48-205`, `src/arm64.cpp:30-182` (`json_character_block::classify`, `curlified` `| 0x20` `<FF>`/`<SUB>` collision, `_mm512_maskz_compress_epi8` bit indexer, `SIMDJSON_NO_SANITIZE_MEMORY`).
  - `src/generic/stage1/json_structural_indexer.h:25-315` (`bit_indexer`, 128-byte dual-block pipelining, 3-entry On-Demand EOF sentinel `[len, len, 0]`, `unescaped_chars_error`).
  - `doc/tape.md:1-144` & `include/simdjson/internal/tape_type.h:10-24` (64-bit DOM tape layout, 24-bit saturating container count `16777215`, `BIGINT = 'Z'`).
  - `doc/ondemand_design.md:19-263` (forward-only lazy cursor, type blindness, "Validate What You Use" boundary).
  - `src/generic/stage2/stringparsing.h:23-260` (`escape_map`, UTF-16 surrogate pair decoding, `parse_string` vs `parse_string_safe` `+ 12` lookahead margin).
  - `include/simdjson/generic/numberparsing.h:65-598` (Clinger fast path, Eisel-Lemire `compute_float_64` & `compute_float_32`, Mushtak-Lemire `0x1FF` / `0x3FFFFFFFFF` two-limb check, round-to-even `[-4, 23]` / `[-17, 10]`, subnormal promotion, SWAR digit checks).
- **`simdutf/simdutf` (`177945073a2e44f6ef252aa2b9cf1ecb8e4d2ab0`, v9.4.0):**
  - `include/simdutf/simdutf_version.h:7-23` (`SIMDUTF_VERSION = "9.4.0"`).
  - `src/generic/utf8_validation/utf8_lookup4_algorithm.h:8-322` (`check_special_cases` 3-nibble LUTs, `check_multibyte_lengths`, `is_incomplete`, `utf8_counters`, `utf8_checker`, `utf8_segmenter`).
  - `src/icelake/icelake_utf8_validation.inl.cpp:3-116` (`_mm512_ternarylogic_epi64(..., 128)` and `_mm512_ternarylogic_epi32(..., 0b1101010)`).
  - `src/haswell/avx2_convert_utf8_to_utf16.cpp:8-195` (12-bit code-point end mask fast paths `0xFFF`, `0xAAAA`, `0x924`, `utf8bigindex`, 4/8-byte store slack, `basic_buffer[i] > 0x3c00000` surrogate guard).
- **`fastfloat/fast_float` (`8ec59686a1430867ba609c2777ca15143dd81003`, v8.3.3):**
  - `CMakeLists.txt:4` (`VERSION 8.3.3`).
  - `include/fast_float/decimal_to_binary.h:20-215` (`compute_product_approximation`, `detail::power`, subnormal and tie-to-even logic).

### Execution Evidence (Observed `2026-11-19`, Linux `x86_64`, Python `3.13.15`, `cc` with `-O2 -mavx2 -mpclmul`)

1. **Transducer Equivalence, `Lookup4` UTF-8 Audit, and Eisel-Lemire Exponent/Subnormal Probe:**
   - Command:
     ```bash
     python3 -c '
     import struct
     MASK64, ODD = (1<<64)-1, 0xAAAAAAAAAAAAAAAA
     def esc_next(bs, c):
         if not bs: return c, 0, 0
         p = bs & (~c & MASK64)
         et = ((((p << 1) & MASK64) | ODD) - p) & MASK64
         et ^= ODD
         return et ^ (bs | c), et & bs, ((et & bs) >> 63) & 1
     for c in (0, 1):
         for bs in range(1 << 16):
             e1, s1, _ = esc_next(bs, c)
             e2 = s2 = 0; cr = c
             for i in range(16):
                 if cr: e2 |= 1<<i; cr = 0
                 elif (bs>>i)&1: s2 |= 1<<i; cr = 1
             assert (e1 & 0xFFFF) == e2 and (s1 & 0xFFFF) == s2 and ((s1>>15)&1) == cr
     for q in range(-400, 350):
         got = (((152170 + 65536) * q + (2048 * 65536)) >> 16) - 2048 - q
         exp = (5**q).bit_length() - 1 if q >= 0 else -(5**(-q)).bit_length()
         assert got == exp
     u0 = struct.unpack("<Q", struct.pack("<d", float("2.2250738585072011e-308")))[0]
     u1 = struct.unpack("<Q", struct.pack("<d", float("2.2250738585072013e-308")))[0]
     print(f"OK 131072/131072 escape; 750/750 log2(5); sub=0x{u0:016x} nrm=0x{u1:016x}")
     '
     ```
   - Recorded output:
     `OK 131072/131072 escape; 750/750 log2(5); sub=0x000fffffffffffff nrm=0x0010000000000000`
   - Extended fuzzing across 5,000 multi-chunk 256-byte backslash/quote streams and 20,000 random UTF-8 byte sequences + 19 RFC 3629 boundary vectors (`\xC0\x80` $\to$ `0x20`, `\xE0\x9F\xBF` $\to$ `0x04`, `\xED\xA0\x80` $\to$ `0x10`, `\xF0\x8F\xBF\xBF` $\to$ `0x40`, `\xF4\x90\x80\x80` $\to$ `0x08`, `\xE0\xA0\x80\x80` $\to$ `0x80`, cross-chunk truncated 4-byte + ASCII $\to$ `0x01`) completed with 0 mismatches.

2. **Hardware AVX2 / `PCLMULQDQ` Operator Aliasing and `mprotect` Guard-Page Overread Probe:**
   - Command: compiled `/tmp/probe_pclmul_guard.c` with `/usr/bin/cc -O2 -mavx2 -mpclmul` testing `_mm_clmulepi64_si128`, scanning all 256 byte values under `_mm256_or_si256(c, 0x20)` + `_mm256_shuffle_epi8(op_tbl, c)`, and placing `{"a":1}` (7 bytes) with and without 64-byte padding immediately before an `mprotect(..., PROT_NONE)` guard page.
   - Recorded output:
     ```text
     PCLMUL_PREFIX_XOR(0x0000040000080024) = 0x000003fffff8001c
     CURLIFIED_OP_MATCHES: 0x0c 0x1a 0x2c 0x3a 0x5b 0x5d 0x7b 0x7d
     PADDED_SAFE_OP_MASK=0x0000000000000051
     UNPADDED_GUARD_PAGE_SIGNAL=11 (SIGSEGV=11)
     ```

## Revalidation

To revalidate these findings quickly against a newer revision of `simdjson`, `simdutf`, or `fast_float` without repeating broad code exploration:

1. **Check Padding and Tape Constants (`simdjson`):** Diff `include/simdjson/base.h` (`SIMDJSON_PADDING`, `SIMDJSON_MAXSIZE_BYTES`), `include/simdjson/common_defs.h` (`to_chars_buffer_size`), `include/simdjson/internal/tape_type.h`, and `src/generic/stage2/stringparsing.h` (`parse_string_safe` lookahead margin `+ 12`). Any increase in vector width (e.g., 128-byte vector chunks without tail masking) or lookahead span directly changes the safe zero-copy buffer padding contract.
2. **Check Escape/Quote and UTF-8 Syndrome Tables:** Diff `src/generic/stage1/json_escape_scanner.h`, `src/generic/stage1/json_string_scanner.h`, `include/simdjson/{haswell,arm64}/bitmask.h`, and `simdutf`'s `src/generic/utf8_validation/utf8_lookup4_algorithm.h`. If any table constant in `check_special_cases` or `must_be_2_3_continuation` changes, re-run the exhaustive 16-bit escape assertion and compare `check_special_cases` + `must23_80` over all $256^2$ adjacent pairs and 3/4-byte continuations against Python's `bytes.decode('utf-8', 'strict')`.
3. **Check Fallback-Free Float Invariants:** Diff `include/simdjson/generic/numberparsing.h` (`compute_float_64`, `compute_float_32`) and `fast_float`'s `include/fast_float/decimal_to_binary.h` (`compute_product_approximation`). Confirm the 9-bit (`0x1FF`) and 38-bit (`0x3FFFFFFFFF`) second-limb masks, the round-to-even exponent windows `[-4, 23]` (binary64) and `[-17, 10]` (binary32), and post-rounding subnormal promotion (`2.2250738585072011e-308` vs `2.2250738585072013e-308`).
