# ISOBMFF, Matroska, MPEG-TS, HLS, and DASH Demuxer/Muxer Edge Cases, Fuzz Hazards, and Zero-Copy Parser Invariants

## Summary

Primary-source inspection of `FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) across `libavformat` and `libavutil/mathematics.c` establishes five recurring failure classes in C multimedia container demuxers, muxers, and streaming manifest handlers, alongside exact algebraic and architectural invariants for a verified zero-copy Rust rewrite:

1. **Timestamp sentinel conflation and signed overflow undefined behavior (`libavutil/mathematics.c`):** `AV_NOPTS_VALUE` (`INT64_MIN = -9223372036854775808`) is bit-identical to the overflow and invalid-denominator error sentinel returned by `av_rescale_rnd` (`libavutil/mathematics.c:65-66, 88-89, 115-116`). Omitting `AV_ROUND_PASS_MINMAX` converts `AV_NOPTS_VALUE` into `-4611686018427387904` (at `1/2` scaling) via `-FFMAX(a, -INT64_MAX)` (`mathematics.c:74-75`), while `av_rescale_delta` (`mathematics.c:180-181`) triggers signed 64-bit integer overflow undefined behavior (`2 * in_ts - 1`) whenever `|in_ts| >= 2^62`.
2. **Compressed-table OOM amplification in ISOBMFF (`libavformat/mov.c`):** Box parsers construct flat in-memory sample tables (`AVIndexEntry[]`, `MOVStts[]`) before reading sample bytes. In `mov_read_trun` (`mov.c:6408-6495`), when `flags == 0`, `entry_size` evaluates to `0`, bypassing the `left / entry_size` bound check; on non-seekable streams (`sample_data_size < 0`) or attacker-controlled reported file sizes (`tools/target_dem_fuzzer.c:145`), a 20-byte `trun` atom requesting `178,000,000` entries passes validation and attempts a `4.272 GiB` `av_fast_realloc` (`213,600,000x` amplification).
3. **Recursive, cyclic, and C-promotion hazards in EBML/Matroska, FLV, and Ogg:** `libavformat/matroskadec.c` handles `EBML_UNKNOWN_LENGTH` (`UINT64_MAX`, lines `979-986`) by terminating container levels on upper-level element IDs (`lines 1291-1327`), guards `SeekHead` loops via `elem->parsed` (`lines 1960-1996`), and retains an implicit C11 `uint32_t + int64_t` signed-to-unsigned conversion trap in differential EBML lacing (`matroska_parse_laces`, `line 3702`). FLV caps AMF0 recursion at `MAX_DEPTH = 16` (`libavformat/flvdec.c:48, 631, 1053`), while Ogg (`libavformat/ogg/demuxer.c:215-250, 442`) supports mid-stream single-track parameter replacement (`ogg_replace_stream`) that mutates stream state after headers are complete.
4. **String-ly typed manifest/protocol SSRF boundaries:** Following historical local-file exfiltration vulnerabilities (`CVE-2016-1897` via `concat:`, `CVE-2016-1898` via `subfile:`), `libavformat` defends manifest consumers via `AVDictionary`-propagated `protocol_whitelist`/`protocol_blacklist` (`libavformat/avio.c:212-260`), extension whitelists in `hls.c` (`open_url`, `lines 867-975`), and hostname CRLF guards in `http.c` (`line 268`), while `dashdec.c` (`line 1348`) invokes `libxml2` `xmlReadMemory(..., 0)` without explicit `XML_PARSE_NONET` hardening.
5. **Verified zero-copy clean-rewrite structure:** Separating layout-verified in-place table views (`zerocopy::FromBytes + Unaligned` over `network_endian` integers) and credit-bounded lazy run descriptors from pure capability-free manifest parsers eliminates OOM amplification, sentinel conflation, and ambient SSRF by construction—satisfying UB-freedom, static panic-freedom under `joshlf/anneal`, differential FATE/fuzz equivalence, and normative ISO/IETF/ITU-T conformance.

## Applicability

This report characterizes container demuxers, fragmented ISOBMFF/CMAF muxers, timestamp arithmetic, and streaming protocol boundaries in `FFmpeg/FFmpeg` at commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (`RELEASE` `8.0.git`). Note two upstream source-tree paths at this revision that differ from older FFmpeg documentation: Ogg demuxing resides in `libavformat/ogg/demuxer.c` (with `libavformat/ogg/Makefile`) rather than `libavformat/oggdec.c`, and EBML/Matroska shared constants reside in `libavformat/matroska.h` alongside `libavformat/matroskadec.c`.

The analysis interprets FFmpeg's C implementation against:

- **Normative media standards:** ISO/IEC 14496-12:2022 (ISOBMFF) and ISO/IEC 23000-19:2024 (CMAF); IETF RFC 8794 (EBML) and IETF RFC 9559 (Matroska); ITU-T Rec. H.222.0 | ISO/IEC 13818-1 (MPEG-TS); IETF RFC 8216 (HLS) and ISO/IEC 23009-1 (MPEG-DASH); and IETF RFC 3533 (Ogg) and IETF RFC 7826 (RTSP 2.0).
- **Existing Rust and verified-parser designs:** `mozilla/mp4parse-rust` (`d3a9abfc93b22687e5e5cd9df86697adcb7d5887`), `pdeljanov/Symphonia` (`5f879df0bf309246a48d57caae457fd8c0e2a5cb`), `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`), `project-everest/everparse` (`f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`; PLDI 2022 DOI `10.1145/3519939.3523708`), and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`).

Foundational topics covered elsewhere in this corpus are cited rather than repeated: formal strong-prefix `clens` laws and non-malleability appear in `everparse-lowparse-strong-prefix-clens-and-nonmalleable-zero-copy-codecs` and `bidirectional-lenses-resugaring-and-non-malleable-format-compilers`; `zerocopy` layout and `FromBytes` soundness predicates appear in `zerocopy-byte-apis-cross-target-layout-and-packet-certificates` and `zerocopy-validity-predicates-projection-layout-and-ffi-intrinsics`; entropy-coded NAL/bitstream framing appears in `entropy-coded-media-bitstreams-video-codec-security-and-simd-decoders`; HTTP header smuggling and URL parser differentials appear in `http-request-smuggling-hpack-qpack-compression-and-url-parser-differentials`; Rust overflow/panic MIR profiles appear in `mir-profile-subsumption-overflow-checks-debug-assertions-and-panic-modes`; and C ABI FFI unwinding boundaries appear in `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`.

## Findings

### 1. Timestamp Domain Algebra, AVRational 64-Bit Rescaling, and Wraparound Horizons

Basis: normative (`ISO/IEC 14496-12`, `ITU-T H.222.0`) + source (`FFmpeg/FFmpeg`) + execution (`probe_avformat_math.c`).

FFmpeg represents timebases with `AVRational { int num; int den; }` (`libavutil/rational.h:58-61`), where negative or zero denominators are valid inhabitants of the C struct. Timestamp conversion flows through `av_rescale_q_rnd(a, bq, cq, rnd)` (`libavutil/mathematics.c:134-140`), which forms two 64-bit cross-products `b = bq.num * (int64_t)cq.den` and `c = cq.num * (int64_t)bq.den` and delegates to `av_rescale_rnd(a, b, c, rnd)` (`mathematics.c:58-127`):

- **128-bit split multiplication preconditions (`mathematics.c:94-117`):** When `b > INT_MAX` or `c > INT_MAX`, `av_rescale_rnd` performs unsigned 32x32-bit partial products (`a0, a1, b0, b1`) and a 64-step restoring binary long division (`for (i = 63; i >= 0; i--)`). The intermediate sum `t1 = a0 * b1 + a1 * b0` (`line 98`) is guaranteed not to wrap 64 bits *only* because prior checks enforce `0 <= a <= INT64_MAX` and `0 <= b <= INT64_MAX`, bounding $t_1 \le 2(2^{32}-1)(2^{31}-1) = 2^{64} - 2^{33} - 2^{32} + 2 < 2^{64}$.
- **Sentinel conflation and unguarded `INT64_MIN` arithmetic (`mathematics.c:65-75, 88-89, 115-116`):** `av_rescale_rnd` checks `if (c <= 0 || b < 0 || ...)` (`line 65`) and overflow `if (t1 > INT64_MAX)` (`line 115`), returning `INT64_MIN` on every error path. Because `AV_NOPTS_VALUE` is defined as `(int64_t)UINT64_C(0x8000000000000000) == INT64_MIN`, callers cannot distinguish "timestamp unknown" from "rational rescaling overflowed" or "negative timebase denominator" (e.g., adversarial container `timescale` where `uint32_t` exceeds `INT32_MAX` and casts negative into `AVRational.den`). Furthermore, when a caller calls `av_rescale_q` (`line 144`, defaulting to `AV_ROUND_NEAR_INF` *without* `AV_ROUND_PASS_MINMAX`) on `a = AV_NOPTS_VALUE`, `line 75` clamps `-FFMAX(a, -INT64_MAX)` to `-INT64_MAX` and returns `-4611686018427387904` instead of `AV_NOPTS_VALUE` (verified in `probe_avformat_math.c`).
- **Signed integer overflow UB in `av_rescale_delta` (`mathematics.c:168-189`):** `av_rescale_delta` asserts `in_ts != AV_NOPTS_VALUE` (`line 171`), then executes `2*in_ts - 1` and `2*in_ts + 1` in signed 64-bit arithmetic (`lines 180-181`). Any container timestamp with `|in_ts| >= 2^62` (`4611686018427387904`) invokes C signed overflow undefined behavior.
- **`av_add_stable` (`mathematics.c:191-215`):** Combines an exact divisibility fast path (`m % d == 0`) with a double-rescale fallback that traps `old == INT64_MAX || old == AV_NOPTS_VALUE || old_ts == AV_NOPTS_VALUE` (`line 210`) before calling `av_sat_add64` (`line 213`).
- **Wraparound horizons (`libavformat/demux.c:53-71, 505-538`, `flvdec.c:1804-1809`):** For streams with `pts_wrap_bits < 64` (notably MPEG-TS 33-bit 90 kHz clocks wrapping every $2^{33}/90000 \approx 95443.7177\text{ s} \approx 26.512\text{ hours}$), `update_wrap_reference` establishes a `pts_wrap_reference` 60 seconds before the initial timestamp (`demux.c:515`) and picks `AV_PTS_WRAP_ADD_OFFSET` or `AV_PTS_WRAP_SUB_OFFSET` (`lines 517-519`) depending on whether the initial timestamp lies within 1/8 of the wrap modulus and 60 s before wraparound. In FLV (`flvdec.c:1804-1805`), 24-bit composition time offsets are sign-extended via `(avio_rb24(s->pb) + 0xff800000) ^ 0xff800000` and summed with `av_sat_add64(dts, cts)`, warning when `cts < 0` or discarding both timestamps (`AV_NOPTS_VALUE`) if `|dts - pts| > 15` minutes (`line 1811`).

**Clean-rewrite invariant:** Replace raw `i64` sentinel overloading with a niche-encoded enum `pub enum Timestamp { Unset, Ticks(NonMinI64) }` (size 8 bytes, identical to C `int64_t` via `INT64_MIN` niche, while making arithmetic on `Unset` unrepresentable at compile time) paired with `NonZeroU32` positive timebase denominators and Rust `i128` widening `((a as i128 * b as i128 + r) / c)` returning `Result<NonMinI64, RescaleError>`. Notice that in Rust, unlike FFmpeg's 2-limb 64-bit division loop, `i128` multiplication cannot overflow for 64-bit inputs since $(2^{63}-1)(2^{62}) < 2^{126} < 2^{127}-1$.

### 2. ISOBMFF, MP4, Edit Lists, Fragmented MP4/CMAF, and Index Amplification Bombs

Basis: normative (`ISO/IEC 14496-12:2022`, `ISO/IEC 23000-19:2024`) + source (`FFmpeg/FFmpeg`, `mozilla/mp4parse-rust`, `pdeljanov/Symphonia`) + execution (`probe_avformat_math.c`).

ISOBMFF (ISO/IEC 14496-12 §4.2) structures media as nested length-prefixed `Box`es (`32-bit size`, `4-byte FourCC`, optional `64-bit largesize` when `size == 1`, and unbounded extend-to-EOF when `size == 0`). `libavformat/mov.c` implements recursive dispatch in `mov_read_default` (`mov.c:10611-10715`) with the following hazard points:

| Mechanism | Source Location (`FFmpeg/FFmpeg`) | Edge Case / Fuzz Hazard | Mitigation & Residual Gap |
| :--- | :--- | :--- | :--- |
| Recursive atom nesting | `mov.c:10617-10621` | Deeply nested `moov`/`trak`/`udta` containers | Hard depth cap `c->atom_depth > 10` returns `AVERROR_INVALIDDATA`. |
| Extended / EOF atom size | `mov.c:10658-10672` | `size == 1` (`64-bit` read `- 8`), `size == 0`, negative `a.size` | Rejects `a.size < 0` after `- 8`; clamps to `atom.size - total_size`. |
| Non-strict `free`/`hoov` recovery | `mov.c:10631-10646` | Non-standard encoders hiding `moov` inside `free`/`hoov` | Rewrites `a.type = 'moov'` when `< FF_COMPLIANCE_STRICT`, intentionally deviating from strict ISO 14496-12. |
| `elst` edit lists | `mov.c:6895-6967`, `5116-5145` | `version 0` (12 B) vs `1` (20 B); `media_time == -1` empty dwell; `rate = rb32/65536.0`; non-strict `atom.size / elst_entry_size` truncation | Rejects `e->duration < 0` (`line 6958`); warns unless `-advanced_editlist` is active for multi-edit timelines (`lines 5135-5143`). |
| `stts` duration wraparound | `mov.c:3985-4045`, `13476` | `sample_duration > c->max_stts_delta` (`UINT_MAX - 48000*10`) | Casts `(int32_t)sample_duration` as negative drift correction via `av_sat_add64`, clipping entry duration toward `1`. |
| `trun` OOM amplification | `mov.c:6337-6495` | `flags == 0` gives `entry_size == 0`; bypasses `left / entry_size` | On non-seekable streams or spoofed `filesize`, 20-byte `trun` requests `4.272 GiB` (`213.6M x`). |
| `sidx` / `tfdt` PTS-vs-DTS | `mov.c:6464-6469`, `6683-6735` | `sidx` encodes presentation time (`PTS`), not `DTS` | `mov.c:6465` admits `FIXME: sidx earliest_presentation_time is *PTS*, s.b.` while assigning it to `dts` when `!use_tfdt`. |

#### Anatomy of the `mov_read_trun` Index Amplification Bomb

In fragmented MP4 (`moof` -> `traf` -> `tfhd` + `trun`, ISO/IEC 14496-12 §8.8.8), each sample entry in `trun` is optional per bitflags (`MOV_TRUN_SAMPLE_DURATION`, `MOV_TRUN_SAMPLE_SIZE`, `MOV_TRUN_SAMPLE_FLAGS`, `MOV_TRUN_SAMPLE_CTS`). Inspecting `mov.c:6391-6495`:

1. Line `6400` rejects `entries && !frag->size && !(flags & MOV_TRUN_SAMPLE_SIZE)`, so setting `default_sample_size = 1` in the preceding `tfhd` box satisfies this check while keeping `flags = 0` in `trun`.
2. At `mov.c:6408-6411`, `entry_size` sums the four `!!(flags & ...)*4` terms, yielding `entry_size = 0`.
3. Consequently, the stream-remaining bound `max_entries = FFMIN(max_entries, left / entry_size)` at `lines 6408-6417` is skipped (`if (entry_size)` is false)!
4. If the input is non-seekable (`avio_size(sc->pb) <= 0`), `line 6415` (`if (sample_data_size > 0)`) does not execute, leaving `max_entries = INT64_MAX`. Even in seekable fuzz harnesses (`tools/target_dem_fuzzer.c:145`), `opaque.filesize` is explicitly fuzzed independently of actual input `size`!
5. Line `6486` only caps `(uint64_t)sti->nb_index_entries + entries` against `UINT_MAX / sizeof(AVIndexEntry)`. For a `24`-byte `AVIndexEntry` and `entries = 178,000,000` (encoded as a 4-byte `uint32_t` inside a 20-byte `trun` atom), `mov.c:6493-6495` attempts `av_fast_realloc(..., 4,272,000,000 bytes)`—a **`213,600,000x` memory amplification factor** from 20 wire bytes.

#### Fragmented Muxer (`movenc.c`) and Rust Parser Comparison (`mp4parse-rust`, `Symphonia`)

On the muxer side (`libavformat/movenc.c`), CMAF (`FF_MOV_FLAG_CMAF`, `movenc.c:93, 8503-8505`) implies `FRAGMENT | EMPTY_MOOV | DEFAULT_BASE_MOOF | NEGATIVE_CTS_OFFSETS`, which avoids edit lists when `use_editlist` is unset or clears `NEGATIVE_CTS_OFFSETS` when edit lists are enabled (`movenc.c:8548-8549`). Generating global or fragment-local `sidx` boxes (`mov_write_sidx_tags`, `movenc.c:6242-6278`) performs a two-pass write using `ffio_open_null_buf` (`lines 6254-6273`) solely to measure total `sidx` byte size so `first_offset` (`line 6236`) reaches the subsequent `moof` box; non-consecutive fragments trigger an error log (`line 6223`) without aborting muxing.

Comparing FFmpeg against existing Rust demuxers clarifies the safety/panic gap:

- **`mozilla/mp4parse-rust` (`d3a9abfc93b22687e5e5cd9df86697adcb7d5887`):** Enables `[profile.release] overflow-checks = true` (`Cargo.toml:6-9`), uses `fallible_collections::TryReserveError` and `TryBox` (`mp4parse/src/lib.rs:25-26`, `mp4parse_capi/src/lib.rs:787`) to return `ENOMEM`/error statuses rather than aborting on OOM, and avoids raw pointer casts. However, `mp4parse` is **not statically panic-free**: `ToU64` (`mp4parse/src/lib.rs:78-83`) and `impl_to_usize_from!` (`lines 95-108`) invoke `.expect(...)`, and C-ABI deallocators `mp4parse_free` / `mp4parse_avif_free` (`mp4parse_capi/src/lib.rs:785-801`) invoke `assert!(!parser.is_null())` inside `extern "C" fn`—causing immediate process abort (or UB in older unwind ABIs) if a C caller passes `NULL`.
- **`pdeljanov/Symphonia` (`5f879df0bf309246a48d57caae457fd8c0e2a5cb`):** Models timebases cleanly via `NonZero<u32>` (`symphonia-core/src/units.rs` referenced via `symphonia-format-isomp4/src/demuxer.rs:117-125`) and explicit `TimeSpan`, making divide-by-zero timescales unrepresentable in the track type system, while still retaining `.expect("1 is non-zero")` on `Default` (`line 124`) rather than a `const` `NonZero::MIN`.

### 3. Matroska/WebM EBML Variable-Length Integers, Unknown-Size Clusters, Lacing, and SeekHead Loops

Basis: normative (`IETF RFC 8794`, `IETF RFC 9559`) + source (`FFmpeg/FFmpeg`).

Matroska/WebM elements use EBML variable-length integers (`VINT`, RFC 8794 §4) for both Element IDs (1–4 octets) and Element Data Sizes (1–8 octets). Inspecting `libavformat/matroskadec.c`:

- **VINT decoding and non-canonical malleability (`ebml_read_num`, `matroskadec.c:914-972`):** Leading zero-bit count determines octet width via `read = 8 - ff_log2_tab[total]` (`line 927`). First-byte `0x00` or `read > max_size` returns `AVERROR_INVALIDDATA` (`lines 929-942`), and the `VINT_MARKER` bit is cleared via `total ^= 1 << ff_log2_tab[total]` (`line 945`). Critically, `ebml_read_num` permits **non-minimal VINT encodings** (e.g., encoding `5` in 2 bytes as `0x40 0x05` instead of `0x85`), and `ebml_parse_elem` distinguishes Element IDs (`max_size = 4`, keeping the marker bit via `id64 | 1 << 7 * res` at `line 1304`) from lengths (`max_size = 8`). Unlike EverParse/LowParse non-malleable codecs (`everparse-lowparse-strong-prefix-clens-and-nonmalleable-zero-copy-codecs`), real-world WebM/Matroska muxers frequently emit fixed-width 8-byte VINTs for placeholder `Segment` or `Cluster` headers; rejecting non-minimal VINTs breaks compatibility in permissive mode.
- **All-ones `EBML_UNKNOWN_LENGTH` (`ebml_read_length`, `matroskadec.c:83, 979-986, 1291-1327`):** Any VINT width `res` in `1..=8` whose stripped payload satisfies `*number + 1 == 1ULL << (7 * res)` (i.e., `0xFF`, `0x7FFF`, ..., `0x01FFFFFFFFFFFFFF`) maps to `EBML_UNKNOWN_LENGTH = UINT64_MAX` (`line 984`). Inside `ebml_parse_elem`, unknown-length containers remain open until either EOF (`lines 1291-1295`) or an element ID matching an enclosing `EbmlSyntax` level terminates the child level (`lines 1315-1326`)—requiring a bounded lookback/pushback mechanism (`current_id` saved across `LEVEL_ENDED` returns).
- **C implicit conversion bug in EBML differential lacing (`matroska_parse_laces`, `matroskadec.c:3628-3722`):** For lacing type `0x3` (EBML lacing, `lines 3680-3716`), the first frame size is decoded as unsigned `uint64_t num`, followed by signed deltas `snum` (`matroska_ebmlnum_sint`). At `matroskadec.c:3702`, the bounds guard writes:
  ```c
  if (lace_size[n - 1] + snum > (uint64_t)INT_MAX)
      return AVERROR_INVALIDDATA;
  ```
  where `lace_size[n - 1]` has type `uint32_t` and `snum` has type `int64_t`. Under C11 §6.3.1.8 usual arithmetic conversions, `lace_size[n - 1] + snum` has signed `int64_t` type (`[ -2^55, ... ]`), which is then **converted to `uint64_t`** for comparison against `(uint64_t)INT_MAX`. A large negative delta `snum < -(int64_t)lace_size[n - 1]` makes the sum negative in `int64_t`, wrapping to $> 2^{63}$ in `uint64_t` and rejecting it as `> INT_MAX`—a benign fail-closed outcome here *only* because `lace_size[n - 1]` is `uint32_t` (`<= INT_MAX`) and `snum` is bounded to 56-bit VINT range (`[-(2^55-1), 2^55-1]`), avoiding signed `int64_t` overflow UB, yet demonstrating how fragile C promotion rules are in security-critical bounds checks!
- **SeekHead cyclic graph protection and broken-index heuristic (`matroskadec.c:1960-2020`):** `matroska_execute_seekhead` skips any `MatroskaLevel1Element` with `elem->parsed` set (`lines 1979, 1994`), preventing infinite loops when adversarial `SeekHead` entries point back to the current `SeekHead`. Cues parsing is deferred (`line 1985`), and `matroska_add_index_entries` silently discards the entire seek index if `index[1].time > 1E14 / matroska->time_scale` (`line 2012`, using `double` floating-point arithmetic).

### 4. MPEG-TS Packet Resynchronization, PCR/PES Clock Recovery, FLV, and Chained Ogg Streams

Basis: normative (`ITU-T H.222.0`, `IETF RFC 3533`) + source (`FFmpeg/FFmpeg`).

- **MPEG-TS framing and resync (`libavformat/mpegts.c`):** MPEG-TS streams appear on the wire in 188-byte (`TS_PACKET_SIZE`), 192-byte (`TS_DVHS_PACKET_SIZE` M2TS with 4-byte TP_extra_header), or 204-byte (`TS_FEC_PACKET_SIZE` with 16-byte Reed-Solomon trailer) cadences. `get_packet_size` (`mpegts.c:680-709`) polls up to `16` partial reads into `PROBE_PACKET_MAX_BUF`, scoring `0x47` periodicity via `analyze()` across all three strides and selecting the winner only if it exceeds the median score (`mid_pred`, `line 696`) by `PROBE_PACKET_MARGIN`. During packet iteration, `handle_packet` (`mpegts.c:3232-3360`) indexes into fixed-size `MpegTSFilter *pids[NB_PID_MAX]` (`NB_PID_MAX = 8192`, `lines 204, 559`—bounding per-stream filter fanout to `O(1)` lookup over 13-bit PIDs), validates PSI section pointer fields (`len > p_end - p`, `line 3313`) and CRC-32 (`crc_validity`), extracts the 42-bit 27 MHz Program Clock Reference (`parse_pcr`, `lines 3544-3568`: 33-bit 90 kHz base + 9-bit 27 MHz extension), and feeds `mpegts_push_data` (`lines 1256-1305`) for PES packet reassembly. Sync loss triggers `mpegts_resync` (`line 3362`), which seeks back `FFMIN(seekback, pos)` bytes to re-align on consecutive `0x47` sync markers.
- **FLV AMF0 recursion and CTS (`libavformat/flvdec.c`):** `amf_parse_object` (`flvdec.c:619-710`) recursively parses AMF0 `OBJECT`, `MIXEDARRAY`, and `ARRAY` metadata tags. Unbounded `arraylen` loops (`line 698`) are capped by `avio_tell(ioc) < max_pos - 1`, and recursive stack exhaustion is bounded by `if (depth > MAX_DEPTH) return AVERROR_PATCHWELCOME;` (`lines 48, 631`, `MAX_DEPTH = 16`). Note that `amf_parse_object` returns `-1` on EOF/syntax errors (`lines 650, 665, 685`) rather than an `AVERROR_*` constant in nested branches, masking distinction between stream truncation and malformed metadata.
- **Ogg CRC-32 framing and mid-stream chaining (`libavformat/ogg/demuxer.c`):** `ogg_read_page` (`ogg/demuxer.c:320-450`) reads the 27-byte `OggS` page header, computes CRC-32 (`0x04C11DB7`) with the 4-byte checksum field zeroed (`lines 384-387`), reads `nsegs` (1 byte, max `255` segments totaling at most `255 * 255 = 65,025` payload bytes, `lines 389-398`), and verifies CRC *before* rejecting unknown header versions (`lines 419-437`). Crucially, when an unknown stream `serial` appears *after* data packets have already been decoded (`data_packets_seen(ogg)` at `line 441`), `ogg_replace_stream` (`lines 215-250`) handles **chained Ogg bitstreams** only when `ogg->nstreams == 1` and the replacement BOS page resolves to the exact same `ogg_codec` (`lines 223-237`), resetting `os->serial`, `lastpts`, `lastdts`, and setting `os->replace = 1`—implicitly requiring downstream audio/video decoders to tolerate mid-stream codec-state resets or fail with `AVERROR_PATCHWELCOME`.

### 5. Adaptive Streaming Manifests (HLS, DASH) and Network Protocol Security Boundaries (HTTP, RTSP, AVIO)

Basis: normative (`IETF RFC 8216`, `ISO/IEC 23009-1`, `IETF RFC 7826`) + source (`FFmpeg/FFmpeg`) + documentation (`CVE-2016-1897`, `CVE-2016-1898`).

Manifest formats (`.m3u8` in HLS, `.mpd` XML in DASH, `.sdp` in RTSP) turn a single demuxer input into an unbounded fetcher of secondary URLs. Historically, FFmpeg's `libavformat` evaluated arbitrary nested protocol strings (such as `concat:http://...` and `subfile:...`) found inside untrusted HLS playlists, allowing attackers to exfiltrate lines of local files via SSRF (`CVE-2016-1897`, `CVE-2016-1898`). Inspection of `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` reveals a layered—but still string-based and incomplete—C defense perimeter:

1. **AVIO protocol whitelist/blacklist propagation (`libavformat/avio.c:212-260`):** `ffurl_connect` checks `av_match_list(uc->prot->name, uc->protocol_whitelist, ',') <= 0` (`line 227`) and `protocol_blacklist` (`line 232`), populating `uc->protocol_whitelist` from `uc->prot->default_whitelist` if unset (`line 237`) and forwarding both lists inside `AVDictionary *options` to child `url_open2` protocols (`lines 246-259`). Crucially, line `243-244` logs a debug warning and leaves `protocol_whitelist` **unset (`NULL`)** whenever a protocol declares no `default_whitelist`, making enforcement strictly opt-in when callers omit `-protocol_whitelist`.
2. **HLS inner-scheme and extension gating (`libavformat/hls.c:867-976`):** `open_url` (`lines 867-953`) peels `crypto+`/`crypto:` (`lines 876-878`) and `data+`/`data:` (`lines 879-881`) wrappers, resolves the inner protocol via `avio_find_protocol_name`, restricts inner schemes to `file`, `http`, or `data` (`lines 891-904`), and checks `c->allowed_extensions` on `file:` URLs (`lines 892-898`). Separately, when `c->extension_picky` is enabled, `test_segment` (`lines 955-976`) checks `c->allowed_segment_extensions` via both `av_match_ext` and `ff_match_url_ext` (`lines 964-970`) unless overridden with `"ALL"`. Furthermore, `hls.c` relies on a polling retry/sleep loop that OSS-Fuzz explicitly masks (`tools/target_dem_fuzzer.c:174-175`: `interrupt_counter &= 31`).
3. **MPEG-DASH `libxml2` surface (`libavformat/dashdec.c:727-790, 1338-1365`):** `parse_manifest` reads the entire MPD into an `AVBPrint` capped at `INT_MAX` (`2 GiB`, `line 1338`) and invokes `xmlReadMemory(buf.str, buf.len, c->base_url, NULL, 0)` (`line 1348`). Passing `options = 0` relies entirely on the linked `libxml2` build's compile-time defaults rather than explicitly specifying `XML_PARSE_NONET | XML_PARSE_NOBLANKS`, while `resolve_content_path` (`lines 727-790`) manually builds URLs across up to 4 nested `<BaseURL>` XML nodes.
4. **HTTP redirect and CRLF injection guards (`libavformat/http.c:253-315, 1357`):** `http_open_cnx_internal` validates `if (strpbrk(hostname, "\r\n")) return AVERROR(EINVAL);` (`line 268`) to block HTTP header injection, re-evaluates `protocol_whitelist` and `protocol_blacklist` on every redirect target (`lines 292-300`), and switches `https` to lower protocol `tls` (`line 303`).
5. **RTSP/SDP bounds (`libavformat/rtsp.c:82, 760`):** `ff_sdp_parse` copies lines into fixed `char buf[SDP_MAX_SIZE]` (`line 764`) with explicit length truncation (`(q - buf) < sizeof(buf) - 1`), while `reorder_queue_size` accepts up to `INT_MAX` buffered RTP packets (`line 82`), creating an option-gated memory amplification vector under hostile server streams.

### 6. Clean-Rewrite Zero-Copy & Panic-Free Demuxer/Muxer Architecture

Basis: source (`google/zerocopy`, `project-everest/everparse`, `joshlf/anneal`) + derived.

Designing a verified Rust `libavformat` replacement requires distinguishing **incidental C structure** from **essential multimedia constraints**:

- **Historical C accidents to eliminate:** (1) overloading `INT64_MIN` as both "missing timestamp" and "arithmetic error"; (2) mutating global protocol registries and passing comma-separated `protocol_whitelist` strings through `AVDictionary`; (3) materializing O(samples) `AVIndexEntry[]` vectors upfront before verifying sample payloads exist on disk; (4) invoking external C `libxml2` over unbounded `INT_MAX` strings for DASH manifests; (5) relying on `strict_std_compliance` runtime branches mixed ad-hoc inside byte-reading loops.
- **Fundamental domain constraints to preserve:** (1) non-monotone B-frame `PTS` vs `DTS` (`ctts` / negative CTS offsets in CMAF and FLV); (2) streaming `EBML_UNKNOWN_LENGTH` live Matroska clusters and 33-bit MPEG-TS PCR/PTS wraparound; (3) multi-edit `elst` timelines and chained Ogg stream transitions; (4) zero-copy parsing performance on multi-gigabyte `moov` sample tables and high-bitrate TS streams.

#### Architectural Blueprint Across the Verification Priority Stack

1. **Zero-Copy Wire Views (`google/zerocopy@ec133ce4d7993775413d852f91c9e3eb2a2a0897`):**
   Represent fixed-width ISOBMFF sample tables (`stts`, `ctts`, `stsc`, `stsz`, `stco`, `co64`, `elst`, `sidx`) and fixed 4-byte MPEG-TS headers as `#[derive(FromBytes, KnownLayout, Immutable, Unaligned)]` `#[repr(C)]` structs using `zerocopy::byteorder::network_endian::{U16, U32, U64, I32, I64}` (`zerocopy/src/byteorder.rs:1006`, `zerocopy/src/lib.rs:4358`). Casting a buffered `moov` slice via `zerocopy::Ref::from_prefix_with_elems::<[SttsEntryWire]>(buf, count)` (`zerocopy/src/ref.rs:835-860`) performs **zero heap allocations and $O(1)$ slice validation**, eliminating both unaligned-read UB and `trun`/`stts` index amplification bombs. Lazy seeking uses sparse prefix-sum checkpoints (1 checkpoint per 1024 entries) or binary search over validated wire slices, enforcing a hard **byte-credit invariant**:
   $$\text{allocated\_index\_bytes} \le K \cdot \text{consumed\_wire\_bytes} \quad (K \approx 4)$$
   For `flags == 0` fragmented `trun` runs, store a single 32-byte `RunDescriptor { first_dts, sample_count, default_dur, default_size, default_flags }` and emit packets lazily on demand rather than pre-allocating `178M` `AVIndexEntry` structs.

2. **Verified Framing & Non-Malleable Subset Separation (`project-everest/everparse@f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`, `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
   Following EverParse3D (`DOI: 10.1145/3519939.3523708`) and LowParse strong-prefix `clens` discipline, split container decoders into: (a) **pure slice-consuming frame parsers** `fn parse(&[u8]) -> Result<(T, &[u8]), ParseErr>` where termination (`remaining.len() < prev.len()`), total checked arithmetic (`checked_add`/`checked_mul`), and bounds safety are discharged via Anneal's 3-axiom MIR-to-Lean proofs (`propext`, `Quot.sound`, `Classical.choice`); and (b) **strict vs permissive normalization adapters** that canonicalize real-world non-minimal EBML VINTs or `free`/`hoov` aliases explicitly at the boundary rather than leaking parser differentials downstream.

3. **Capability-Typed IO Isolation (Zero Ambient SSRF):**
   Decouple manifest/container parsers (`hls`, `dash`, `rtsp/sdp`) from network/filesystem IO. A manifest parser takes `&[u8]` plus a pure `UrlResolver` and outputs validated `Vec<SegmentPlan>` data structures without possessing any `File` or `TcpStream` handle. Only a caller-injected `trait FetchBackend`—which carries explicit typed enum capabilities (`enum AllowedScheme { Http, Https }` with no `file:`/`concat:`/`subfile:` variant)—can open segment streams, removing `CVE-2016-1897`/`1898` protocol confusion at the Rust type level.

4. **Verification Priority Stack Matrix:**

| Priority Tier | Target Guarantee | Concrete Demuxer / Muxer Implementation Strategy |
| :--- | :--- | :--- |
| **1. UB-Freedom** | 100% memory- & type-soundness | `#![forbid(unsafe_code)]` in pure container parsers via `zerocopy::FromBytes`/`Ref::from_prefix_with_elems`; no raw `AVCodecContext` pointer casts or C11 implicit promotion traps; `extern "C"` C-ABI shims validated against non-null pointers before `Box::from_raw`. |
| **2. Panic-Freedom** | Zero aborts/panics on hostile bytes or OOM | `#![deny(clippy::unwrap_used, clippy::expect_used)]`; ban `Vec` unchecked indexing; fallible allocations (`try_reserve`) gated by wire byte-credit invariants; `i128` checked rational rescaling (`Timestamp::Unset` vs `NonMinI64`); Anneal `#[spec]` MIR proofs guaranteeing no panic edge reachable. |
| **3. Behavioral Equivalence** | Differential FATE + fuzz equivalence vs FFmpeg | Differential corpus harness (`FFmpeg/FFmpeg` `target_dem_fuzzer.c` corpus + FATE samples) comparing emitted `(stream_idx, dts, pts, duration, flags, payload_bytes)` packets, with documented intentional divergences only on FFmpeg UB (`av_rescale_delta` `|ts| >= 2^62`), `trun` OOM bombs, and `protocol_whitelist`-less SSRF. |
| **4. Spec Conformance** | ISO 14496-12 / CMAF / RFC 9559 / H.222.0 / RFC 8216 | Explicit `Strictness::Spec` vs `Strictness::FfmpegCompat` mode bit separating normative rules (canonical EBML VINTs, `sidx` PTS vs `tfdt` DTS, valid `elst` `media_time >= -1`) from legacy FFmpeg heuristics (`hoov`-as-`moov`, negative `stts` drift clamping). |

## Boundaries

- **known not to apply:** Zero-copy slice casting via `zerocopy::FromBytes` applies to fixed-layout tables (`stts`, `stco`, `elst`, TS 4-byte headers, Ogg fixed 27-byte header prefix) and is **known not to apply** directly to variable-bit/byte-encoded elements—specifically EBML VINTs (`ebml_read_num`), MPEG-TS optional adaptation-field extensions, Xiph/EBML block lacing, and codec Annex-B emulation-prevention streams (covered in `entropy-coded-media-bitstreams-video-codec-security-and-simd-decoders`). Similarly, EverParse non-malleability (unique canonical encoding for every value) is **known not to apply** to permissive Matroska/MP4 demuxing of legacy files containing non-minimal VINTs or `free`/`hoov` workarounds (`mov.c:10631-10646`), which require explicit permissive compatibility normalization.
- **not examined:** Subtitle/teletext demuxers (`srt`, `webvtt`, `ass`, `dvbsub`), Common Encryption (`cenc` AES-CTR/CBCS key-schedule and cryptographic verification internals beyond `pssh`/`senc` box framing), RTP jitter-buffer packet loss concealment (see `webrtc-neteq-jitter-buffers-opus-silk-celt-hybrids-and-flac-lpc-overflows`), and full end-to-end throughput benchmarks comparing multi-gigabyte FFmpeg C remuxing vs Rust `zerocopy` pipelines (only extracted C micro-probes of rational math and `trun` amplification arithmetic were executed).
- **unknown:** The prevalence in real-world MP4 archives of streams requiring FFmpeg's negative `(int32_t)sample_duration` `stts` drift heuristic (`mov.c:4007-4025`) rather than strict ISO/IEC 14496-12 `uint32_t` rejection.
- **unsupported:** Exact frame-accurate seeking on unindexed `EBML_UNKNOWN_LENGTH` Matroska live streams or HTTP chunked responses without `Content-Length` / `Cues` / `sidx` metadata, in both FFmpeg and streaming Rust demuxers without full stream buffering.

## Evidence

### Source Code & Specification Citations

- **`FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`):**
  - `libavutil/rational.h:58-61` (`AVRational`), `89-108` (`av_cmp_q`, `av_q2d`).
  - `libavutil/mathematics.c:58-127` (`av_rescale_rnd`), `134-140` (`av_rescale_q_rnd`), `168-189` (`av_rescale_delta`, signed `2*in_ts - 1` / `2*in_ts + 1` at `180-181`), `191-215` (`av_add_stable`).
  - `libavformat/demux.c:53-71` (`wrap_timestamp`, `ff_wrap_timestamp`), `505-538` (`update_wrap_reference`, 60 s heuristic).
  - `libavformat/mov.c:3985-4045, 13476` (`mov_read_stts`, `max_stts_delta`), `5099-5145` (`mov_build_index` + `elst` handling), `6337-6495` (`mov_read_trun`, `entry_size` bypass & `av_fast_realloc`, `6465` `sidx` PTS-vs-DTS FIXME), `6683-6735` (`mov_read_sidx`), `6895-6967` (`mov_read_elst`), `10611-10715` (`mov_read_default`, `atom_depth > 10`, `free`/`hoov` recovery).
  - `libavformat/movenc.c:93, 6156-6278, 8500-8565` (`FF_MOV_FLAG_CMAF`, `mov_write_moof_tag_internal`, `mov_write_sidx_tag`, `mov_write_sidx_tags` two-pass `ffio_open_null_buf`).
  - `libavformat/matroskadec.c:83` (`EBML_UNKNOWN_LENGTH`), `914-972` (`ebml_read_num`), `979-986` (`ebml_read_length`), `1275-1335` (`ebml_parse_elem` level-termination logic), `1960-2020` (`matroska_execute_seekhead` `elem->parsed`, `matroska_add_index_entries`), `3628-3722` (`matroska_parse_laces`, `line 3702` `uint32_t + int64_t` promotion).
  - `libavformat/mpegts.c:202-204, 559` (`NB_PID_MAX`), `680-709` (`get_packet_size` 188/192/204 scoring), `1256-1305` (`mpegts_push_data`), `3232-3362` (`handle_packet`, `mpegts_resync`), `3544-3568` (`parse_pcr`).
  - `libavformat/hls.c:867-976` (`open_url`, `crypto+`/`data+` stripping, `allowed_extensions`; `test_segment`, `extension_picky`, `allowed_segment_extensions`).
  - `libavformat/dashdec.c:727-790` (`resolve_content_path`), `1330-1370` (`parse_manifest`, `xmlReadMemory(..., 0)` at `1348`).
  - `libavformat/avio.c:212-260` (`ffurl_connect`, `protocol_whitelist`, `protocol_blacklist`).
  - `libavformat/http.c:253-315` (`http_open_cnx_internal`, CRLF check at `268`, redirect whitelist at `292-300`), `1340-1385` (`Location` / `Content-Length`).
  - `libavformat/rtsp.c:82` (`reorder_queue_size` `INT_MAX`), `760-785` (`ff_sdp_parse`).
  - `libavformat/flvdec.c:48, 619-710` (`amf_parse_object`, `MAX_DEPTH = 16`), `1795-1825` (24-bit `cts` sign extension + `av_sat_add64`).
  - `libavformat/ogg/Makefile` & `libavformat/ogg/demuxer.c:215-250` (`ogg_replace_stream`), `380-450` (`ogg_read_page`, CRC-32 `0x04C11DB7`).
  - `tools/target_dem_fuzzer.c:98-205` (fuzzed `opaque.filesize` at `145`, HLS `interrupt_counter &= 31` at `174-175`).
- **Rust & Verified Parser References:**
  - `mozilla/mp4parse-rust` (`d3a9abfc93b22687e5e5cd9df86697adcb7d5887`): `Cargo.toml:6-9`, `mp4parse/src/lib.rs:25-26, 70-108`, `mp4parse_capi/src/lib.rs:717-801`.
  - `pdeljanov/Symphonia` (`5f879df0bf309246a48d57caae457fd8c0e2a5cb`): `symphonia-format-isomp4/src/demuxer.rs:38-130`.
  - `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`): `zerocopy/Cargo.toml:17-18`, `zerocopy/src/lib.rs:4358`, `zerocopy/src/ref.rs:835-860`, `zerocopy/src/byteorder.rs:1006`.
  - `project-everest/everparse` (`f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`): `README.md`; Swamy et al., *Hardening Attack Surfaces with Formally Proven Binary Format Parsers*, PLDI 2022 (`DOI: 10.1145/3519939.3523708`).
  - `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`): `Cargo.toml:1-15`.

### Reproducible Execution Probe (`probe_avformat_math.c`)

Standalone extracted C model reproducing `av_rescale_rnd` / `av_rescale_q_rnd` (`libavutil/mathematics.c:58-145`), `av_rescale_delta` line `180` signed overflow, and `mov_read_trun` (`libavformat/mov.c:6408-6495`) amplification arithmetic. Executed on `Linux 7.1.6-1rodete1-amd64 x86_64` (`Intel(R) Xeon(R) CPU @ 2.20GHz`), compiled with `gcc (Debian 15.2.0-14) 15.2.0`:

```c
#include <stdint.h>
#include <stdio.h>
#include <limits.h>

#define AV_NOPTS_VALUE ((int64_t)UINT64_C(0x8000000000000000))
#define FFMAX(a,b) ((a) > (b) ? (a) : (b))
#define FFMIN(a,b) ((a) > (b) ? (b) : (a))

enum AVRounding {
    AV_ROUND_ZERO     = 0,
    AV_ROUND_INF      = 1,
    AV_ROUND_DOWN     = 2,
    AV_ROUND_UP       = 3,
    AV_ROUND_NEAR_INF = 5,
    AV_ROUND_PASS_MINMAX = 8192,
};

typedef struct AVRational { int num; int den; } AVRational;

int64_t av_rescale_rnd(int64_t a, int64_t b, int64_t c, enum AVRounding rnd) {
    int64_t r = 0;
    if (c <= 0 || b < 0 || !((unsigned)(rnd & ~AV_ROUND_PASS_MINMAX) <= 5 && (rnd & ~AV_ROUND_PASS_MINMAX) != 4))
        return INT64_MIN;
    if (rnd & AV_ROUND_PASS_MINMAX) {
        if (a == INT64_MIN || a == INT64_MAX)
            return a;
        rnd -= AV_ROUND_PASS_MINMAX;
    }
    if (a < 0)
        return -(uint64_t)av_rescale_rnd(-FFMAX(a, -INT64_MAX), b, c, rnd ^ ((rnd >> 1) & 1));
    if (rnd == AV_ROUND_NEAR_INF) r = c / 2;
    else if (rnd & 1) r = c - 1;
    if (b <= INT_MAX && c <= INT_MAX) {
        if (a <= INT_MAX) return (a * b + r) / c;
        int64_t ad = a / c;
        int64_t a2 = (a % c * b + r) / c;
        if (ad >= INT32_MAX && b && ad > (INT64_MAX - a2) / b)
            return INT64_MIN;
        return ad * b + a2;
    } else {
        uint64_t a0 = a & 0xFFFFFFFF, a1 = a >> 32;
        uint64_t b0 = b & 0xFFFFFFFF, b1 = b >> 32;
        uint64_t t1 = a0 * b1 + a1 * b0, t1a = t1 << 32;
        a0 = a0 * b0 + t1a;
        a1 = a1 * b1 + (t1 >> 32) + (a0 < t1a);
        a0 += r;
        a1 += a0 < r;
        for (int i = 63; i >= 0; i--) {
            a1 += a1 + ((a0 >> i) & 1);
            t1 += t1;
            if (c <= a1) { a1 -= c; t1++; }
        }
        if (t1 > INT64_MAX) return INT64_MIN;
        return t1;
    }
}

int64_t av_rescale_q_rnd(int64_t a, AVRational bq, AVRational cq, enum AVRounding rnd) {
    int64_t b = bq.num * (int64_t)cq.den;
    int64_t c = cq.num * (int64_t)bq.den;
    return av_rescale_rnd(a, b, c, rnd);
}

int main(int argc, char **argv) {
    int64_t r_nopts = av_rescale_rnd(AV_NOPTS_VALUE, 1, 2, AV_ROUND_NEAR_INF);
    int64_t r_ovf   = av_rescale_rnd(INT64_MAX, 90000, 1, AV_ROUND_NEAR_INF);
    int64_t r_negd  = av_rescale_q_rnd(1000, (AVRational){1, -1000}, (AVRational){1, 90000}, AV_ROUND_NEAR_INF);
    printf("nopts_unmasked=%lld (is_nopts=%d)\n", (long long)r_nopts, r_nopts == AV_NOPTS_VALUE);
    printf("overflow_ret=%lld (is_nopts=%d)\n", (long long)r_ovf, r_ovf == AV_NOPTS_VALUE);
    printf("neg_den_ret=%lld (is_nopts=%d)\n", (long long)r_negd, r_negd == AV_NOPTS_VALUE);

    unsigned entries = 178000000U;
    int entry_size = 0;
    int64_t sample_data_size = -1;
    int64_t max_entries = INT64_MAX;
    if (sample_data_size > 0) max_entries = sample_data_size;
    if (entry_size) max_entries = FFMIN(max_entries, 12 / entry_size);
    size_t requested_size = (size_t)entries * 24;
    printf("trun_check_pass=%d requested_bytes=%zu amp_vs_20B=%.1fx\n",
           entries <= max_entries, requested_size, (double)requested_size / 20.0);

    if (argc > 1) {
        int64_t in_ts = (int64_t)1 << 62;
        int64_t ub = 2 * in_ts - 1;
        printf("ub=%lld\n", (long long)ub);
    }
    return 0;
}
```

Command and verbatim output (`2026-11-20`):

```text
$ gcc -O2 -Wall -fsanitize=undefined -fno-sanitize-recover=undefined probe_avformat_math.c -o probe_avformat_math
$ ./probe_avformat_math
nopts_unmasked=-4611686018427387904 (is_nopts=0)
overflow_ret=-9223372036854775808 (is_nopts=1)
neg_den_ret=-9223372036854775808 (is_nopts=1)
trun_check_pass=1 requested_bytes=4272000000 amp_vs_20B=213600000.0x
$ ./probe_avformat_math trigger_ub
probe_avformat_math.c:88:24: runtime error: signed integer overflow: 4611686018427387904 * 2 cannot be represented in type 'long int'
```

## Revalidation

To verify whether these findings still hold on a newer `FFmpeg/FFmpeg` revision:

1. **Rational math & `trun` OOM probe:** Recompile and run the extracted `probe_avformat_math.c` above under `-fsanitize=undefined -fno-sanitize-recover=undefined`, and diff upstream `libavutil/mathematics.c` (`av_rescale_rnd`, `av_rescale_delta`) and `libavformat/mov.c` (`mov_read_trun`) to check whether `flags == 0` (`entry_size == 0`) or non-seekable streams gained a stream-byte or `nb_index_entries` credit bound.
2. **Protocol/XML security gates:** Inspect `libavformat/hls.c` (`open_url`), `libavformat/avio.c` (`ffurl_connect`), `libavformat/http.c` (`http_open_cnx_internal`), and `libavformat/dashdec.c` (`xmlReadMemory`) for whether `protocol_whitelist` remains optional (`NULL` when `default_whitelist` is unset) and whether `dashdec.c` adds `XML_PARSE_NONET`.
3. **Directory layout drift:** Check `libavformat/ogg/Makefile` and `libavformat/matroskadec.c` (`ebml_read_length`, `matroska_parse_laces`) for refactored demuxer locations or C promotion fixes.
