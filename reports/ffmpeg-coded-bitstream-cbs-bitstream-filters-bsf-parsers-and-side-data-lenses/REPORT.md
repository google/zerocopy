# FFmpeg CodedBitstream Lenses, Bitstream Filters, Elementary-Stream Parsers, and Typed Side-Data Contracts

## Summary

Between container demuxers (`libavformat`) and elementary decoders/encoders (`libavcodec`), FFmpeg (`FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) interposes four tightly coupled packet-framing and metadata-rewriting subsystems:

1. **`69` Stateful `FFCodecParser` Elementary-Stream Splitters (`libavcodec/parsers.c`, `parser.c`):** Reassemble unframed arbitrary-sized byte chunks into access units via shift-register start-code scanners and `ff_combine_frame()`. Auditing `parser.c` reveals three severe contract hazards: (a) **`ff_combine_frame()` (`parser.c:272-274`) unconditionally reads `64` bytes (`AV_INPUT_BUFFER_PADDING_SIZE`) past `*buf + next`** whenever `pc->index > 0`, making unpadded slice inputs immediate heap-buffer-overread UB; (b) `av_parser_parse2()` (`parser.c:171-200`) clamps negative parser returns to `0` and cannot propagate `AVERROR(ENOMEM)`, silently discarding buffered partial frames on allocation failure (`parser.c:244, 268`); and (c) `AV_PARSER_PTS_NB = 4` (`parser.h:37`) wraps its 4-slot timestamp ring buffer whenever more than four input chunks precede a frame boundary.
2. **`57` `FFBitStreamFilter` (`AVBSFContext`) Packet Rewriters (`libavcodec/bitstream_filters.c`, `libavcodec/bsf/*`):** Partitioned into `15` `CodedBitstream`-backed AST filters, `3` multi-pad `AVBitStreamFilterGraph` filters (`source`, `sink`, `lcevc_merge`), and `39` bespoke raw packet filters. `tools/target_bsf_fuzzer.c:62-64` calls `av_bsf_alloc()`, which returns `AVERROR(ENOTSUP)` on graph filters (`bsf.c:105-106`), leaving **0% OSS-Fuzz coverage on multi-pad BSF synchronization (`bsf/packetsync.c`)**. Worst-case size-amplification and integer-safety analysis proves:
   - `h264_mp4toannexb` (`bsf/h264_mp4toannexb.c:390-420`) exhibits **quadratic $O(S \cdot E)$ size amplification** up to $\lfloor S / 4 \rfloor \cdot (E + 9)$ bytes when `length_size == 1` and alternating 2-byte IDR/non-IDR NALs repeatedly trigger $E$-byte `SPS+PPS` re-injection, whereas `hevc_mp4toannexb` and `vvc_mp4toannexb` enforce **linear $\le 2S + E$** amplification by injecting extradata at most once per packet.
   - **`vp9_superframe` (`bsf/vp9_superframe.c:38-69`) contains an unchecked 32-bit `unsigned sum` integer-wraparound heap buffer overflow UB** when accumulating up to `MAX_CACHE = 8` cached invisible-frame packet sizes before `av_new_packet(out, sz)` and `memcpy()`.
   - `setts` (`bsf/setts.c:210-225`) evaluates 64-bit timestamps in IEEE-754 `binary64` (`53`-bit mantissa) and casts back via `llrint()`, causing precision loss above $2^{53}$ and C11 domain-error cross-ISA divergence (`x86-64` `cvtsd2si` vs `AArch64` `fcvtzs`) on `NaN`/`±Inf`/out-of-range expressions, while omitting `.flush`.
3. **`10` `CodedBitstream` (`cbs_*`) Bidirectional Syntax Engines (`libavcodec/cbs*.c`):** Instantiates single-source C macro templates (`cbs_*_syntax_template.c`) twice (`#define READ` vs `#define WRITE`) over reference-counted ASTs (`AVRefStruct`). Formally, `cbs_*` is **not** a classical state-free well-behaved lens (`GetPut`/`PutGet` per Foster et al., ACM TOPLAS 2007 `doi:10.1145/1232420.1232424`), but a **state-coupled asymmetric quotient lens** requiring twin state contexts `(CBSBSFContext.input, CBSBSFContext.output)` (`cbs_bsf.c:154-160`). Five concrete `GetPut` ($\operatorname{put}(\operatorname{get}(b)) = b$) violations occur on decomposed units: mandatory MP4-to-Annex-B framing erasure (`cbs_h2645.c:323-404`), AV1 non-canonical LEB128 normalization (`cbs_av1.c:127-194`), RBSP trailing-zero/emulation-prevention normalization (`cbs_h2645.c:245-251`), AV1 `uvlc` $\ge 32$-zero rejection (`cbs_av1.c:55-67`), and read-only `AVERROR_PATCHWELCOME` on VP8 (`cbs_vp8.c:357-360`).
4. **Typed Side-Data Propagation Lattice (`44` Packet Types $\to$ `39` Frame Types):** `libavcodec/decode.c:1569-1680` merges stream-global `coded_side_data`, per-packet `pkt->side_data`, and in-band SEI/OBU/ITU-T T.35 payloads (`h2645_sei.c`, `itut35.c`, `atsc_a53.c`, `dovi_rpudec.c`). Contrasting `dovi_rpudec.c` + `bsf/dovi_rpu.c` against Rust's `quietvoid/dovi_tool@41dae646193c12de152333ff5dbc33579cb9ef4a` exposes **three C11 float/signed-overflow UBs in `dovi_rpudec.c:90-126`**, an incomplete last-NAL-only check in `bsf/dovi_rpu.c:83-98`, and irreversible stripping of unknown Dolby Vision DM v1/v2 extension blocks that `dovi_tool` preserves bit-for-bit.

## Applicability

This report characterizes the elementary-stream parsing (`FFCodecParser`), bitstream filtering (`FFBitStreamFilter` / `AVBitStreamFilterGraph`), `CodedBitstream` (`cbs_*`), and side-data propagation subsystems in `FFmpeg/FFmpeg` at commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, alongside `tools/target_bsf_fuzzer.c`. Dolby Vision Reference Processing Unit (RPU) round-trip semantics are compared directly against `quietvoid/dovi_tool` at commit `41dae646193c12de152333ff5dbc33579cb9ef4a`. Bidirectional AST invariants are analyzed against the lens laws of Foster et al. (`doi:10.1145/1232420.1232424`) and normative syntax rules in ITU-T H.264 (08/2024), ITU-T H.265 (09/2023), ITU-T H.266 (09/2023), AOM AV1 v1.0.0 Errata 1, SMPTE ST 2094-40:2020 (`doi:10.5594/SMPTE.ST2094-40.2020`), and ATSC A/53 Part 4:2009.

Companion corpus relationships:

- Container-level ISOBMFF/Matroska/MPEG-TS demuxing hazards precede this layer and are covered in `isobmff-mp4-matroska-mpegts-hls-dash-demuxer-muxer-edge-cases-and-fuzz-hazards`.
- General OSS-Fuzz CVE classes across `libavcodec` decoders appear in `ffmpeg-cve-ub-memory-safety-taxonomy-and-oss-fuzz-failure-modes`.
- Public C ABI layout and `AVBufferRef` lifetimes are covered in `ffmpeg-c-abi-libav-struct-layout-callbacks-and-rust-ffi-compatibility-layer` and `libavfilter-graph-scheduling-frame-threading-and-avbufferref-lifetime-invariants`.
- Clean-room verified parser combinator theory (`StrongPrefix`, non-malleable codecs) is covered in `formal-verification-of-media-parsers-fixed-point-dsp-and-panic-free-rust`. This report supplies the complete FFmpeg parser/BSF/CBS/side-data architecture, exact amplification bounds, and lens divergences.

## Findings

### 1. All `69` Stateful `FFCodecParser` Elementary-Stream Splitters and Carryover Hazards

`Basis: source`

`libavcodec/parsers.c:24-95` registers exactly **`69` `FFCodecParser` instances**, invoked via `av_parser_parse2()` (`libavcodec/parser.c:133-214`) whenever an unframed stream (raw Annex B `.h264`/`.hevc`, MPEG-TS PES payloads, ADTS/AC-3 radio streams, raw image pipes) lacks container packet boundaries. Exhaustive source inspection partitions all `69` parsers into four state-machine classes:

| Parser Class | Count | Registered `FFCodecParser` Names (`ff_<name>_parser` in `libavcodec/parsers.c`) | Carryover & Framing Mechanism |
| --- | ---: | --- | --- |
| **1. Direct `ff_combine_frame` Shift-Register Splitters** | `46` | `aac_latm`, `adx`, `ahx`, `amr`, `avs2`, `avs3`, `bmp`, `cavsvideo`, `cri`, `dca`, `dnxhd`, `dnxuc`, `dolby_e`, `dpx`, `dvbsub`, `evc`, `ftr`, `gif`, `gsm`, `h261`, `h263`, `h264`, `hdr`, `hevc`, `ipu`, `jpeg2000`, `jpegxl`, `jpegxs`, `lcevc`, `mjpeg`, `mlp`, `mpeg4video`, `mpegaudio`, `mpegvideo`, `opus`, `png`, `pnm`, `qoi`, `sbc`, `sipr`, `tak`, `vc1`, `webp`, `xbm`, `xma`, `xwd` | Accumulate `ParseContext.state` (`uint32_t`) or `state64` (`uint64_t`) across chunk boundaries; pass positive byte offset `next` or negative start-code rewind `next < 0` (`END_NOT_FOUND = -100`) to `ff_combine_frame()` |
| **2. `CodedBitstream` (`cbs_*`)-Assisted Splitters** | `3` | `apv`, `av1`, `vvc` | Use `CodedBitstreamContext` (`ff_cbs_read`) to parse OBU / VVC NAL headers for exact frame/AU boundaries (`vvc_parser.c` pairs `ff_combine_frame` NAL splitting with CBS picture-header inspection; `apv_parser.c` and `av1_parser.c` inspect pre-framed packets via CBS without `ff_combine_frame`) |
| **3. `ff_aac_ac3_parse` Sync-Word State Machines** | `2` | `aac`, `ac3` | Shared two-frame sync-word confirmation + header-derived frame-length lookahead in `aac_ac3_parser.c` wrapping `ff_combine_frame()` |
| **4. Custom-Ring / Packet-Only Header Inspectors** | `18` | *Custom reassembly (`3`):* `flac` (`AVFifo` + fuzzy CRC-8/CRC-16 header candidate scoring), `dirac` (custom sync buffer), `dvdsub` (PES packet reassembly). *Pre-framed (`15`):* `cook`, `dvaudio`, `dvd_nav`, `ffv1`, `g723_1`, `g729`, `misc4`, `prores`, `prores_raw`, `rv34`, `rw2`, `vorbis`, `vp3`, `vp8`, `vp9` | Extract `key_frame`, `pict_type`, `duration`, `width`/`height`, or `pts` from already-framed container packets without cross-chunk `ParseContext` reassembly |

#### `ff_combine_frame()` State Machine and Negative `next` Rewind (`parser.c:218-292`)

`ParseContext` (`libavcodec/parser.h:35-65`) maintains `uint8_t *buffer`, `int index` (valid bytes currently buffered), `int last_index`, `unsigned int buffer_size`, `uint32_t state`, `uint64_t state64`, `int frame_start_found`, and `int overread` / `int overread_index`. When a multi-byte start code (such as H.264/HEVC `00 00 01` or `00 00 00 01`) straddles the boundary between chunk $k$ (ending with `00 00`) and chunk $k + 1$ (beginning with `01 65 ...`), the scanner detects the start code after consuming `1` byte of chunk $k + 1$, computing **`next = -2`** (`2` trailing bytes at the end of `pc->buffer` actually belong to the *next* frame!). `ff_combine_frame()` handles three regimes:

1. **Overread drainage (`lines 224-233`):** Copies leftover start-code prefix bytes saved from the prior frame (`pc->overread > 0`) down to `pc->buffer[0 .. pc->overread - 1]` before scanning new data.
2. **Incomplete frame (`next == END_NOT_FOUND = -100`, `lines 239-254`):** Reallocates `pc->buffer` via `av_fast_padded_malloc(&pc->buffer, &pc->buffer_size, *buf_size + pc->index + AV_INPUT_BUFFER_PADDING_SIZE)` and appends `*buf[0 .. *buf_size - 1]`, setting `*buf_size = 0` to signal "need more bytes".
3. **Frame completed (`next != END_NOT_FOUND`, `lines 259-290`):** If `pc->index == 0` and `next >= 0`, returns zero-copy slice `*buf[0 .. next - 1]` directly without copying into `pc->buffer`! If `pc->index + next > 0` and `next < 0`, shrinks the completed frame in `pc->buffer` by `|next|` bytes and parks those trailing bytes at `pc->overread_index = pc->index + next`, `pc->overread = -next` for the next call.

#### Three Critical Safety and Liveness Defects in `parser.c`

1. **Unconditional `64`-Byte Caller Buffer Overread (`parser.c:272-274`):**
   When `pc->index > 0` (chunk carryover active) and `next > -AV_INPUT_BUFFER_PADDING_SIZE` (`next > -64`), lines `272-274` execute:
   ```c
   if (next > -AV_INPUT_BUFFER_PADDING_SIZE)
       memcpy(&pc->buffer[pc->index], *buf,
              next + AV_INPUT_BUFFER_PADDING_SIZE);
   ```
   Even when `*buf_size == next` (e.g., `next == 10` bytes in a `10`-byte input chunk), `memcpy` reads **`next + 64` bytes from `*buf`**! Note that `av_parser_parse2()` (`lines 148-151`) substitutes a stack `uint8_t dummy_buf[AV_INPUT_BUFFER_PADDING_SIZE]` **only when `buf_size == 0`** (EOF flush). Any Rust or C FFI caller passing an exact-length unpadded slice (`buf_size > 0` without `64` readable trailing bytes in the underlying allocation) triggers **immediate out-of-bounds heap/stack read UB** whenever a frame straddles two chunks.
2. **Silent `AVERROR(ENOMEM)` Erasure & Stream Corruption (`parser.c:171-200, 244, 268`):**
   `av_parser_parse2()` returns the non-negative count of consumed input bytes (`0 .. buf_size`), never an `AVERROR`:
   ```c
   index = s->parser->parse(s, avctx, poutbuf, poutbuf_size, buf, buf_size);
   av_assert0(index > -0x20000000); // API check, ensure no AVERROR codes
   ...
   if (index < 0)
       index = 0;
   ```
   However, `AVERROR(ENOMEM)` on POSIX (`-ENOMEM = -12`, where `-12 > -0x20000000`!) passes the `av_assert0` check! When `av_fast_padded_malloc` fails inside `ff_combine_frame()` (`lines 243-245` or `267-269`), `ff_combine_frame` sets `pc->index = 0` (permanently discarding the buffered prefix of the frame!) and returns `AVERROR(ENOMEM)` (`-12`), which codec parsers return directly to `av_parser_parse2()`, where `if (index < 0) index = 0;` **masks the OOM as "0 bytes consumed, `*poutbuf_size = 0`"** — causing callers either to spin infinitely feeding the same `buf` or to silently splice truncated NAL payloads!
3. **4-Slot Timestamp Ring Wraparound (`parser.h:37`, `parser.c:89-118, 154-161`):**
   `ff_fetch_timestamp()` tracks input chunk timestamps in a fixed `4`-element ring `cur_frame_pts[AV_PARSER_PTS_NB]` (`AV_PARSER_PTS_NB = 4`). Whenever a large access unit arrives fragmented across $\ge 5$ small network/pipe reads (`cur_frame_start_index = (cur_frame_start_index + 1) & 3`), newer chunk byte offsets overwrite older unconsumed entries before the frame completes, silently dropping or misattributing `s->pts` / `s->dts`.

---

### 2. All `57` `FFBitStreamFilter` Transforms, Multi-Pad Graph Blind Spots, and Size-Amplification Bounds

`Basis: source + derived`

`libavcodec/bitstream_filters.c:27-90` registers **`57` `FFBitStreamFilter` definitions** (`55` standard filters + `2` graph endpoint filters `ff_source_bsf` and `ff_sink_bsf`):

| BSF Architecture Tier | Count | Exact Registered Filter Names (`libavcodec/bitstream_filters.c`) | Core Engine |
| --- | ---: | --- | --- |
| **1. `CodedBitstream` (`cbs_*`) AST Filters** | `15` | `apv_metadata`, `av1_frame_merge`, `av1_frame_split`, `av1_metadata`, `dovi_rpu`, `dts2pts`, `filter_units`, `h264_metadata`, `h264_redundant_pps`, `hevc_metadata`, `lcevc_metadata`, `mpeg2_metadata`, `trace_headers`, `vp9_metadata`, `vvc_metadata` | Parse packets via `ff_cbs_read_packet`, mutate or reorder `CodedBitstreamFragment` ASTs, and emit via `ff_cbs_write_packet` (except zero-copy `av1_frame_split`, `dts2pts`, `trace_headers`) |
| **2. Multi-Pad `AVBitStreamFilterGraph` Filters** | `3` | `lcevc_merge`, `source` (`ff_source_bsf`), `sink` (`ff_sink_bsf`) | Multi-input/output pad topology (`AVBitStreamFilterPad` in `bsf/filters.h`) synchronized by DTS/PTS queues in `bsf/packetsync.c` (`FFPacketSync`), merging base H.264/HEVC/VVC streams with LCEVC enhancement streams |
| **3. Bespoke Raw Packet / Bitstream Filters** | `39` | `aac_adtstoasc`, `ahx_to_mp2`, `chomp`, `dca_core`, `dovi_split`, `dump_extradata`, `dv_error_marker`, `eac3_core`, `eia608_to_smpte436m`, `evc_frame_merge`, `extract_extradata`, `h264_mp4toannexb`, `hapqa_extract`, `hevc_mp4toannexb`, `imx_dump_header`, `jpegapp`, `media100_to_mjpegb`, `mjpeg2jpeg`, `mjpega_dump_header`, `mov2textsub`, `mpeg4_unpack_bframes`, `noise`, `null`, `opus_metadata`, `pcm_rechunk`, `pgs_frame_merge`, `prores_metadata`, `remove_extradata`, `setts`, `showinfo`, `side_data`, `smpte436m_to_eia608`, `text2movsub`, `trim`, `truehd_core`, `vp9_raw_reorder`, `vp9_superframe`, `vp9_superframe_split`, `vvc_mp4toannexb` | Direct `GetByteContext` / `PutByteContext` / `GetBitContext` / `h2645_packet_split` packet surgery |

#### OSS-Fuzz `target_bsf_fuzzer.c` Multi-Pad Blind Spot (`tools/target_bsf_fuzzer.c:62-64`)

`tools/target_bsf_fuzzer.c` selects a single `AVBitStreamFilter *f` and calls `res = av_bsf_alloc(f, &bsf);` (`line 62`), exiting if `res < 0`. Inside `libavcodec/bsf.c:105-106`, `av_bsf_alloc()` explicitly rejects multi-pad graph filters that implement pad callbacks rather than the legacy 1-in/1-out `.filter` function pointer:
```c
if (!ff_bsf(filter)->filter)
    return AVERROR(ENOTSUP);
```
Consequently, **`target_bsf_fuzzer.c` achieves `0%` fuzz coverage of `lcevc_merge` and `bsf/packetsync.c`**, leaving multi-stream timestamp synchronization and LCEVC NAL interleaving completely untested by FFmpeg's single-BSF fuzz target.

#### Exact Size-Amplification Bounds and Vulnerability Audit of Core BSFs

| Bitstream Filter (`libavcodec/bsf/`) | Worst-Case Output Size Bound (Input Size $S$, Extradata Size $E$) | Exact Mechanism, Edge Cases, and Memory-Safety / UB Verdict |
| --- | --- | --- |
| **`h264_mp4toannexb`** (`h264_mp4toannexb.c:325-428`) | **Quadratic $O(S \cdot E)$:** $\lfloor S / 4 \rfloor \cdot (E + 9)$ bytes (when `length_size = 1`, $E > 0$); **$2.5 S$** when $E = 0$ | With AVCC `length_size = 1` (`extradata[4] & 3 == 0`): for $E = 0$, repeating 2-byte `[0x01, 0x07]` (`H264_NAL_SPS`) replaces 1-byte length with 4-byte `00 00 00 01` ($2 \to 5$ bytes = **$2.5\times$**; ordinary slices `[0x01, 0x01]` get 3-byte `00 00 01` after the first NAL = $2.0\times$). When out-of-band `SPS+PPS` has size $E > 0$: 2-byte IDR `[0x01, 0x05]` injects $E$ bytes + 4-byte start code (`lines 390-395`, $= E + 5$ bytes) and sets `idr_sps_seen = idr_pps_seen = 1`, **and an immediately following 2-byte non-IDR slice `[0x01, 0x01]` (`lines 410-414`) executes `s->new_idr = 1; s->sps_seen = 0; s->pps_seen = 0;`**, re-arming full $E$-byte injection on the very next 2-byte IDR! Repeating `[0x01, 0x05, 0x01, 0x01]` ($4$ bytes) yields $E + 9$ output bytes per $4$ input bytes (e.g., $S = 64\text{ KiB}, E = 16\text{ KiB} \implies \mathbf{256\text{ MiB}}$ output from one packet!). Safe against 32-bit wrap only because `uint64_t out_size` checks `out_size > INT_MAX - AV_INPUT_BUFFER_PADDING_SIZE` (`line 420`) |
| **`hevc_mp4toannexb`** (`hevc_mp4toannexb.c:407-538`) & **`vvc_mp4toannexb`** (`vvc_mp4toannexb.c:237-304`) | **Linear:** $\le 2 S + E$ bytes | Both require `nalu_size >= 2` (2-byte HEVC/VVC NAL header), so minimal `length_size = 1` unit is `3` input bytes `[0x02, h0, h1]` $\to$ `6` output bytes (`00 00 00 01 h0 h1`, **$2.0\times$**). Crucially, both guard extradata insertion with a per-packet latch (`!got_irap` / `!added_extra`), **injecting $E$ at most once per packet**, and `hevc_mp4toannexb.c:435-443` caps parameter-set CRC deduplication checks via `MAX_PS_CHECKS_PER_PACKET` and `MAX_PS_CHAIN_DEPTH` |
| **`vp9_superframe`** (`vp9_superframe.c:38-69, 108-175`) | $2 + 5 N + \sum_{k=0}^{N-1} S_k$ ($N \le \text{MAX\_CACHE} = 8$) | **CRITICAL 32-BIT INTEGER OVERFLOW HEAP WRITE UB (`lines 38-69`):** `stats()` accumulates `n_in <= 8` packet sizes (`int size <= INT_MAX` each) into **32-bit `unsigned sum = 0`** (`line 38`) and computes `unsigned sz = sum + 2 + (mag + 1) * n_in` (`line 61`) with **zero overflow check**, allocates `av_new_packet(out, sz)` (`line 62`), and executes `memcpy(ptr, in[n]->data, in[n]->size)` across all cached packets (`lines 66-69`)! Three invisible frames of `1.5 GiB` (`0x60000000`) wrap `sum` modulo $2^{32}$ to `512 MiB` (`0x20000000`), causing a **`4.0 GiB` out-of-bounds heap write**! Also drops all `AVPacketSideData` attached to `s->cache[0 .. s->n_cache - 2]`, copying props only from the final visible frame (`line 169`) |
| **`av1_frame_split`** vs **`av1_frame_merge`** (`av1_frame_split.c:51-193`, `av1_frame_merge.c:46-137`) | Split: $\sum S_{\text{out}} = S_{\text{in}}$ (`1.0×` zero-copy); Merge: $\le \sum S_{\text{in}}$ (`MAX_TU_OBUS = 65536`) | **Asymmetric round-trip:** `av1_frame_split` decomposes headers via CBS (`decompose_unit_types`), then slices `s->buffer_pkt` zero-copy (`av_packet_ref` + `out->data = td->units[...].data`, preserving non-canonical LEB128 `obu_size`, setting `out->pts = AV_NOPTS_VALUE` on `!show_frame && !show_existing_frame` invisible frames at `lines 170-171`, and **cloning `side_data` onto every split sub-packet**). Conversely, `av1_frame_merge` demands a leading `AV1_OBU_TEMPORAL_DELIMITER` (`lines 78-80`), re-serializes via `ff_cbs_write_packet` (normalizing LEB128), and retains `buffer_pkt` metadata only from the first packet with `pts != AV_NOPTS_VALUE` (`lines 123-126`) |
| **`aac_adtstoasc`** (`aac_adtstoasc.c:39-130`) |Payload shrinks by $7$ or $9$ bytes + optional `PCE` (`MAX_PCE_SIZE = 304`); side data $+ (2 + \text{PCE})$ bytes | Strips 7-byte (or 9-byte CRC) ADTS header zero-copy (`pkt->data += 7 + 2*!crc_absent`). On the first frame only (`!ctx->first_frame_done`), extracts in-band Program Config Element (`PCE`) if `chan_config == 0` (`lines 80-98`) and emits `AV_PKT_DATA_NEW_EXTRADATA`. Rejects valid MPEG-2/4 ADTS streams having `num_aac_frames > 1` with CRC (`lines 63-68`) via `AVERROR_PATCHWELCOME`, and ignores mid-stream sample-rate/channel reconfigurations once `first_frame_done == 1` |
| **`extract_extradata`** (`extract_extradata.c:96-260`) | Packet unchanged (or shrunk when `remove=1`); side data $\le S + 4 N_{\text{ps}}$ | Extracts global headers (`AV1` `SEQUENCE_HEADER` + `HDR_CLL`/`HDR_MDCV` metadata OBUs; `H264`/`HEVC`/`VVC` `VPS`/`SPS`/`PPS` normalized to 4-byte Annex B start codes) into `AV_PKT_DATA_NEW_EXTRADATA` **only when `has_sps` / `has_seq` holds** (`lines 120, 222`) |
| **`setts`** (`setts.c:96, 210-225, 291-298`) | Payload `1.0×` zero-copy | Evaluates `pts`, `dts`, and `duration` (`int64_t`) via `av_expr_eval()` in IEEE-754 `double` (`53`-bit precision, corrupting timestamps $> 2^{53} = 9.007 \times 10^{15}$, including `AV_NOPTS_VALUE = -2^{63}` when referenced arithmetically) and casts back via **`llrint(double)`** (`line 214`), whose return value on `NaN`/`±Inf`/out-of-range is **unspecified in ISO C11 §7.12.9.5 / Annex F.4** (`0x8000000000000000` on x86-64 `cvtsd2si` vs `0` for `NaN` and `0x7FFFFFFFFFFFFFFF` for `+Inf` on AArch64 `fcvtzs`!). Also **omits `.flush`**, leaking `s->cur_pkt` across stream resets |
| **`dovi_rpu`** (`dovi_rpu.c:79-128`) | Re-encoded RPU NAL (`UNSPEC62`) or ITU-T T.35 OBU | **Incomplete NAL scan bug (`lines 83-98`):** `dovi_rpu_update_fragment_hevc()` inspects **only `au->units[au->nb_units - 1]`**! In dual-layer HEVC Profile 7 streams where `HEVC_NAL_UNSPEC63` (Enhancement Layer) or trailing `FD_NUT`/`EOS_NUT` follows `HEVC_NAL_UNSPEC62` (`[..., Slice, UNSPEC62, UNSPEC63]`), `strip=1` deletes `UNSPEC63` while **failing to strip `UNSPEC62`**, and `strip=0` returns `0` at `line 97` without updating the RPU |

---

### 3. `CodedBitstream` (`cbs_*`) Bidirectional AST Engine and State-Coupled Quotient Lens Laws

`Basis: normative + source + derived`

`libavcodec/cbs.c:33-64` registers **`10` codec-specific `CodedBitstreamType` backends** (`cbs_apv.c`, `cbs_av1.c`, `cbs_h264.c`, `cbs_h265.c`, `cbs_h266.c`, `cbs_jpeg.c`, `cbs_lcevc.c`, `cbs_mpeg2.c`, `cbs_vp8.c`, `cbs_vp9.c`, sharing `cbs_h2645.c` and `cbs_sei.c`). Rather than maintaining separate parser and serializer codebases, each codec defines its normative bitstream grammar once in a header-included macro file (`cbs_h264_syntax_template.c`, `cbs_h265_syntax_template.c`, `cbs_h266_syntax_template.c`, `cbs_av1_syntax_template.c`, `cbs_vp9_syntax_template.c`, `cbs_jpeg_syntax_template.c`, `cbs_mpeg2_syntax_template.c`, `cbs_apv_syntax_template.c`, `cbs_lcevc_syntax_template.c`, `cbs_sei_syntax_template.c`) and `#include`s that file twice:

- **Read instantiation (`#define READ`):** Expands grammar combinators `xf(width, name, var, range_min, range_max, subs, ...)` / `ue(...)` / `se(...)` / `fixed(width, name, value)` into `GetBitContext` reads, range assertions (`[range_min, range_max]`, returning `AVERROR_INVALIDDATA` on violation), trace logging, and `AVRefStruct` AST allocation (`CodedBitstreamUnitTypeDescriptor` in `cbs_internal.h:85-145`).
- **Write instantiation (`#define WRITE`):** Expands the identical combinator sequence into range assertions plus `PutBitContext` writes. `ff_cbs_write_unit_data()` (`cbs.c:344-366`) starts with a `1 MiB` (`1 << 20`) `write_buffer` and **doubles buffer capacity on `AVERROR(ENOSPC)` up to `INT_MAX / 8` (`256 MiB`, the 32-bit bit-counter ceiling of `PutBitContext`)**.

#### Formal Lens Characterization: Classical Lenses vs State-Coupled Quotient Lenses

In bidirectional programming (`Foster et al., ACM TOPLAS 29(3), 2007`, `doi:10.1145/1232420.1232424`), a total/partial lens between concrete byte representations $B$ and abstract views $A$ satisfies:
$$\text{(GetPut)} \quad \operatorname{get}(b) = a \implies \operatorname{put}(b, a) = b, \qquad \text{(PutGet)} \quad \operatorname{put}(b, a) = b' \implies \operatorname{get}(b') = a$$
FFmpeg's `CodedBitstream` violates state-free lens assumptions in two fundamental ways:

1. **Dual-State Parameter-Set Coupling (`CBSBSFContext` in `cbs_bsf.c:154-160`):**
   Video bitstream grammars (`ITU-T H.264/H.265/H.266`, `AOM AV1`) are **context-sensitive**: bit-widths of slice/frame header fields (such as `pic_order_cnt_lsb` width `log2_max_pic_order_cnt_lsb_minus4 + 4`, `frame_num` width, or AV1 `frame_number` bits `id_len`) depend on the currently active `SPS` / `PPS` / `VPS` / `Sequence Header` stored in `CodedBitstreamContext->priv_data` (`active_sps`, `sps[32]`, `pps[256]`). When a BSF such as `h264_metadata` or `av1_metadata` rewrites a field inside an `SPS` or `Sequence Header`, **subsequent input packets in the original stream are still encoded against the unmutated upstream parameter set $S_{\text{in}}$, whereas serialized output packets must be written against the mutated parameter set $S_{\text{out}}$!** Therefore `cbs_bsf.c` maintains **two separate stateful contexts** $(S_{\text{in}}, S_{\text{out}})$:
   $$\operatorname{read\_frag} : S_{\text{in}} \times B \rightharpoonup S'_{\text{in}} \times \operatorname{Frag}(A), \qquad \operatorname{write\_frag} : S_{\text{out}} \times \operatorname{Frag}(A) \rightharpoonup S'_{\text{out}} \times B'$$
2. **Quotient Canonicalization & Five Concrete `GetPut` Violations:**
   For units **excluded** from `ctx->decompose_unit_types` (`cbs.c:179-186, 398-399`), `unit->content == NULL` and `unit->data` retains a zero-copy `AVBufferRef` slice into the input packet, preserving `unit->data` verbatim (modulo container framing). However, for **decomposed units**, `cbs_*` discards non-semantic syntax representations (`put` is a canonicalizing section over an equivalence relation $\sim$ rather than a state-retaining `put(b, a)`):

| Backend (`libavcodec/`) | Concrete `GetPut` ($\operatorname{write}(\operatorname{read}(b)) = b$) Violation | Exact Source Coordinates & Worst-Case Re-Serialization Bound |
| --- | --- | --- |
| **`cbs_h264` / `cbs_h265` / `cbs_h266`** (`cbs_h2645.c`) | **1. Mandatory MP4 $\to$ Annex B Framing Erasure:** `cbs_h2645_split_fragment()` parses length-prefixed `AVCC`/`HVCC`/`VVCC` packets (`frag->data` with `nal_length_size = 1, 2, 4`) and MP4 configuration records in `extradata`, but `cbs_h2645_assemble_fragment()` **unconditionally writes Annex B `00 00 00 01` / `00 00 01` start codes** (`cbs_h2645.c:323-404`, `cbs_h264.c:733`) — silently converting MP4 packets/extradata into Annex B unless re-muxed! | `cbs_h2645.c:265-404`; `cbs_h264.c:733` |
| **`cbs_h264` / `cbs_h265` / `cbs_h266` / `cbs_jpeg`** | **2. Trailing-Zero Stripping & Byte-Stuffing Canonicalization:** On split, `cbs_h2645` strips trailing `0x00` bytes (`cbs_h2645.c:245-251`) and `0x03` RBSP emulation-prevention bytes (`00 00 03 -> 00 00`). Non-canonical inputs (e.g., redundant `00 00 03 04` or extra trailing `cabac_zero_word` `0x00`s) re-serialize canonically. On write, `cbs_h2645_write_nal_unit` (`line 340`) reserves exact tight RBSP expansion **`4 + unit->data_size * 3 / 2`** (`00 00 -> 00 00 03` = $1.5\times$); `cbs_jpeg_assemble_fragment` (`cbs_jpeg.c:364-404`) stuffs `0xFF -> 0xFF 0x00` ($2.0\times$ bound) | `cbs_h2645.c:245-251, 338-385`; `cbs_jpeg.c:364-404` |
| **`cbs_av1`** (`cbs_av1.c`) | **3. Non-Canonical LEB128 `obu_size` Normalization:** AOM AV1 §4.10.5 permits `obu_size` to be padded with leading `0x80` continuation bytes up to 8 bytes (common in hardware encoders that patch `obu_size` post-encode into a fixed 4-byte reservation). `cbs_av1_read_leb128()` (`lines 127-153`) discards original byte count, and `cbs_av1_write_leb128(..., fixed_length = 0)` (`lines 155-194`) emits minimal `(av_log2(value) + 7) / 7` bytes, shrinking packet byte offsets and breaking external byte-range indices | `cbs_av1.c:127-194, 1180-1245` |
| **`cbs_av1`** (`cbs_av1.c`) | **4. Spec vs `libaom` `uvlc` Ambiguity Rejection:** In AOM AV1 §4.10.3 `uvlc()`, when `leadingZeroBits >= 32`, the normative pseudocode and reference `libaom` disagree on whether the terminating `1` bit is read before returning `(1 << 32) - 1`. `cbs_av1_read_uvlc()` (`lines 55-67`) **hard-rejects `zeroes >= 32` with `AVERROR_PATCHWELCOME`** | `cbs_av1.c:55-67` |
| **`cbs_vp8`** (`cbs_vp8.c`) | **5. Unidirectional Read-Only Backend:** Because VP8 macroblock/frame headers past the 3-byte uncompressed tag are arithmetic-coded (`vp8_rac`), `cbs_vp8.c` implements `.read_unit` (`cbs_vp8_read_unit`) only; **`cbs_vp8_write_unit()` (`lines 357-360`) unconditionally returns `AVERROR_PATCHWELCOME`** | `cbs_vp8.c:357-360` |

---

### 4. Typed Side-Data Propagation Contracts, ITU-T T.35 Muxing, and Dolby Vision RPU Lossiness

`Basis: normative + source`

FFmpeg separates out-of-band / extracted metadata into **`44` `AVPacketSideDataType`s** (`libavcodec/packet.h`, `packet_internal.h:39-83`) and **`39` `AVFrameSideDataType`s** (`libavutil/frame.h`). During decoding (`libavcodec/decode.c:1569-1680`), metadata propagates through a strict **three-tier precedence lattice** (`StreamGlobal < PacketContainer < InBandBitstream`):

1. **Tier 1 — Stream-Global `avctx->coded_side_data` (`ff_sd_global_map` in `decode.c:1569-1584`):** Automatically attaches `MASTERING_DISPLAY_METADATA`, `CONTENT_LIGHT_LEVEL`, `DYNAMIC_HDR_VIVID`, `DISPLAYMATRIX`, `STEREO3D`, `SPHERICAL`, `ICC_PROFILE`, `AMBIENT_VIEWING_ENVIRONMENT`, and `EXIF` to every output `AVFrame` unless already populated.
2. **Tier 2 — Per-Packet `pkt->side_data` (`ff_decode_frame_props_from_pkt` in `decode.c:1586-1635`):** Maps packet-scoped side data onto the decoded `AVFrame` (`A53_CC`, `AFD`, `DYNAMIC_HDR10_PLUS -> AV_FRAME_DATA_DYNAMIC_HDR_PLUS`, `DYNAMIC_HDR_SMPTE_2094_APP5`, `S12M_TIMECODE`, `SKIP_SAMPLES`, `LCEVC`, `EXIF`, `IAMF_*`), overriding Tier 1 when duplicated.
3. **Tier 3 — In-Band SEI / OBU / ITU-T T.35 Payloads (`h2645_sei.c`, `itut35.c`, `atsc_a53.c`, `dovi_rpudec.c`):** Overrides Tiers 1–2 with codec-stateful persistence rules:
   - **Mastering Display & Content Light (`h2645_sei.c:250-290, 415-455`):** Because Coded Video Sequence (CVS)-scoped SEI messages arrive on the IRAP (IDR/CRA) picture in decoding order before trailing RASL/RADL B-frames from the prior CVS finish outputting, `H2645SEIMasteringDisplay` and `H2645SEIContentLight` set `present = 2` on receipt and decrement `present` at IRAP boundaries (`lines 264, 281`), preventing premature cross-GOP metadata bleed. Note also that ITU-T H.265 Clause D.2.27 transmits primaries in **`{G, B, R}` (`c = 0, 1, 2`)** order, which `h2645_sei.c:426` permutes via `mapping[3] = {2, 0, 1}` into `AVMasteringDisplayMetadata`'s canonical `{R, G, B}` order.
   - **Film Grain Synthesis (`AVFilmGrainParams`):** Tagged union (`libavutil/film_grain_params.h`) discriminating `AV_FILM_GRAIN_PARAMS_AV1` (auto-regressive AR coefficients + piecewise-linear luma/Cb/Cr scaling points from AV1 `film_grain_params()` or ITU-T T.35 `AFGS1`) from `AV_FILM_GRAIN_PARAMS_H274` (ITU-T H.274 frequency-cutoffs + intensity intervals from H.264/HEVC/VVC `FILM_GRAIN_CHARACTERISTICS` SEI). When `avctx-> export_side_data & AV_CODEC_EXPORT_DATA_FILM_GRAIN` is set, decoders suppress internal grain synthesis and export `AV_FRAME_DATA_FILM_GRAIN_PARAMS` for GPU/filter presentation.

#### ITU-T T.35 Registered User-Data Dispatch (`libavcodec/itut35.c:54-149`) and ATSC A/53 Asymmetry

`itut35.c` demultiplexes `user_data_registered_itu_t_t35` SEI/OBU payloads across country, provider (`uint16_t`), and provider-oriented codes:

| `itu_t_t35_country_code` | `provider_code` | `provider_oriented_code` / Magic | Normative Standard & Target `AVFrameSideDataType` |
| --- | --- | --- | --- |
| `0xB5` (United States) | `0x0031` (ATSC) | `'GA94'` (`0x47413934`) or `'DTG1'` (`0x44544731`) | ATSC A/53 Part 4 (`CEA-708` `cc_data` triplets) $\to$ `AV_FRAME_DATA_A53_CC` |
| `0xB5` (United States) | `0x003C` (Samsung) | `0x0001` (`application_identifier = 4`) | SMPTE ST 2094-40 (`HDR10+` Bezier curve & distribution percentiles) $\to$ `AV_FRAME_DATA_DYNAMIC_HDR_PLUS` (`dynamic_hdr_plus.c`) |
| `0xB5` (United States) | `0x003B` (Dolby) | `27`-bit EMDF wrapper magic `0x01be6841` | Dolby Vision AV1 Profile 10 RPU $\to$ `AV_FRAME_DATA_DOVI_RPU_BUFFER` + `AV_FRAME_DATA_DOVI_METADATA` |
| `0xB5` (United States) | `0x0090` (SMPTE) | `0x0001` | SMPTE ST 2094-50 (Application #5) $\to$ `AV_FRAME_DATA_DYNAMIC_HDR_SMPTE_2094_APP5` |
| `0xB5` (United States) | `0x5890` (AOM) | `'AFGS1'` | AOM Film Grain Synthesis 1 $\to$ `AV_FRAME_DATA_FILM_GRAIN_PARAMS` (`AV1` variant) |
| `0xB4` (United Kingdom) | `0x0050` (V-Nova) | LCEVC payload | ISO/IEC 23094-2 LCEVC enhancement data $\to$ `AV_FRAME_DATA_LCEVC` |
| `0x26` (China) | `0x0004` (CUVA) | `0x0005` / `0x0006` | CUVA 005.1 HDR Vivid $\to$ `AV_FRAME_DATA_DYNAMIC_HDR_VIVID` |

**ATSC A/53 Closed-Caption Round-Trip Lossiness (`libavcodec/atsc_a53.c:45-125`):** On decode, `ff_parse_a53_cc()` (`lines 93-106`) accepts `'GA94'`, `'DTG1'`, and SCTE-20 formats and **concatenates multiple SEI messages per frame** (e.g., separate top-field and bottom-field SEI NALs) by reallocating `buf_ref` and summing `cc_count` (`3` bytes per triplet). On encode, however, `ff_alloc_a53_sei()` (`lines 45-75`) **hardcodes `'GA94'` (`line 57`) and masks `cc_count` to 5 bits (`cc_count <= 0x1F = 31` triplets = `93` bytes)** — silently truncating concatenated multi-field or high-rate caption buffers $> 93$ bytes!

#### Dolby Vision RPU Hazards and Lossiness vs `quietvoid/dovi_tool`

`libavcodec/dovi_rpudec.c` (`lines 46-771`) parses Dolby Vision RPUs from two incompatible transport wrappers:

- **HEVC `NAL_UNSPEC62` (`0x7C01` + `0x19` prefix):** Byte-aligned RBSP after stripping `0x03` emulation-prevention bytes (`dovi_rpudec.c:363-376`).
- **AV1 `OBU_METADATA_ITUT_T35` EMDF (`dovi_rpudec.c:377-403`):** Following `0xB5` + `0x003B`, the ETSI TS 102 366 EMDF header reads a **`27`-bit magic constant (`0x01be6841`)** plus variable-bit `emdf_payload_size`, leaving the embedded RPU bitstream **misaligned by `+1` bit (or arbitrary bit offset `pos % 8 != 0`)**! Because RPU trailing CRC-32 (`AV_CRC_32_IEEE`, big-endian MPEG-2 CRC initialized to `-1`, `lines 755-760`) operates on bytes of the unwrapped RPU, `dovi_rpudec.c:389-397` must bit-copy the entire remaining bitstream into a freshly allocated byte-aligned scratch buffer before parsing! Furthermore, `lines 728-754` must disambiguate encoders that insert a redundant `0x00` byte before the 32-bit CRC when `align_get_bits` was already byte-aligned (`term_unpadded` vs `term_padded` checking `0x80` stop byte at both `+4` and `+5` bytes, running CRC twice on collision).

Auditing `dovi_rpudec.c` and `bsf/dovi_rpu.c` against Rust's `quietvoid/dovi_tool` (`dolby_vision/src/rpu/dovi_rpu.rs` at `41dae646193c12de152333ff5dbc33579cb9ef4a`) uncovers **three C11 Undefined Behaviors and four round-trip lossiness defects** in FFmpeg:

1. **C11 Float-to-Integer Cast UB on Untrusted `RPU_COEFF_FLOAT` (`dovi_rpudec.c:90-126`):**
   When `hdr->coef_data_type == RPU_COEFF_FLOAT` (`1`), `get_ue_coef()` (`lines 101-103`) and `get_se_coef()` (`lines 120-122`) execute:
   ```c
   fpart.u32 = get_bits_long(gb, 32);
   return fpart.f32 * (1LL << hdr->coef_log2_denom);
   ```
   Here `fpart.u32` is an arbitrary untrusted 32-bit word from the packet, and `hdr->coef_log2_denom` is validated only in `[13, 32]` (`lines 455-465`). Casting `float` directly to `uint64_t` (`line 103`) or `int64_t` (`line 122`) triggers **immediate ISO C11 §6.3.1.4p1 Undefined Behavior** whenever `fpart.f32` is `NaN`, `±Inf`, $\le -1.0\text{f}$ (for `uint64_t`), or has magnitude $\ge 2^{63 - \text{coef\_log2\_denom}}$ (e.g., any float $\ge 2^{31}$ when `coef_log2_denom == 32`).
2. **C11 Signed Multiplication Overflow UB in `RPU_COEFF_FIXED` (`dovi_rpudec.c:115-118`):**
   `ipart = get_se_golomb_long(gb)` returns `int32_t` (reaching `±(2^{31}-1)` or `INT32_MIN`), and `ipart * (1LL << hdr->coef_log2_denom)` overflows signed `int64_t` whenever `coef_log2_denom == 32` and `|ipart| >= 2^{31}`.
3. **Destructive Re-Serialization vs `quietvoid/dovi_tool` (`dovi_rpudec.c:150-290, 603-661` vs `dovi_rpu.rs:59-67`):**
   - FFmpeg's `bsf/dovi_rpu.c` decodes RPUs into fixed-schema C structs (`AVDOVIMetadata`, `AVDOVIDmData`) and re-encodes from scratch (`ff_dovi_rpu_generate` in `dovi_rpuenc.c`): **any unknown DM v1 or DM v2 extension block level (`default:` in `parse_ext_v1`/`parse_ext_v2`, `lines 190-192`) is silently dropped**; `linear_interp_flag == 1` (`line 610`) and `affected_dm_id != current_dm_id` (`line 660`) fail hard with `AVERROR_PATCHWELCOME`; and `RPU_COEFF_FLOAT` coefficients are permanently quantized to fixed-point.
   - By contrast, `quietvoid/dovi_tool` (`dolby_vision/src/rpu/dovi_rpu.rs:59-67`) stores typed extension enums **plus raw bit-level residual payloads** (`remaining: Option<BitVec<u8, Msb0>>`, `trailing_zeroes: usize`, and raw unknown `ExtMetadataBlock` byte vectors), preserving exact bit-level `GetPut` round-trip (`write_rpu(parse_rpu(bytes)) == bytes`) on untouched blocks while safely recomputing CRC-32/MPEG-2 when active L1/L2/L5/L6/L8/L11 trims are edited.

---

### 5. Clean-Room Verification Priority Stack and Rust Lens/BSF Architecture

`Basis: derived`

Designing a formally verified Rust packet-framing, BSF, and `CodedBitstream` replacement separates FFmpeg's C legacy hazards from the true domain invariants across all four verification tiers:

1. **Level 1 — Undefined-Behavior (UB) Freedom (`100%` Safe Rust Core):**
   - **Zero Caller Padding Preconditions:** Replace `ff_combine_frame`'s `next + 64` `memcpy` overread (`parser.c:272-274`) with an exact-slice ring/vec accumulator (`Vec<u8>`) whose SIMD start-code scanner (`memchr` / `0x00_00_01` vector loop) processes `chunk[..chunk.len() / 32 * 32]` in SIMD and `chunk[aligned..]` scalarly, requiring **zero trailing padding bytes** on `&[u8]`.
   - **Eliminate Wraparound & Float-Cast UB:** Replace 32-bit `unsigned sum` in `vp9_superframe` with `usize::checked_add` capped at `MAX_PACKET_BYTES` (`i32::MAX as usize`); replace `setts` `double` + `llrint` with exact checked `i128` rational expression evaluation (`AVRational` timebase scaling via `av_rescale_q` equivalent); and decode `RPU_COEFF_FLOAT` via pure IEEE-754 integer bit extraction (`u32::from_bits` exponent/mantissa shift with explicit `NaN`/overflow error return).
2. **Level 2 — Panic-Freedom & Explicit Error Sum Types:**
   - Replace `av_parser_parse2`'s integer-clamped return contract (`if (index < 0) index = 0`) with a total sum type:
     ```rust
     pub enum ParseStep<'a> {
         Frame { consumed: usize, payload: Cow<'a, [u8]>, pts: Option<i64>, dts: Option<i64> },
         NeedMore { consumed: usize },
     }
     // Returning Result<ParseStep<'a>, ParserError> where OutOfMemory never silently drops pc->buffer!
     ```
   - Replace fixed `AV_PARSER_PTS_NB = 4` timestamp arrays with a bounded `VecDeque<(u64, TimestampPair)>` (with monotonic byte-offset pruning on frame emission), and enforce explicit output amplification budgets (`max_alloc_bytes`, rejecting pathological $O(S \cdot E)$ `h264_mp4toannexb` IDR/non-IDR ping-pong packets deterministically with `Err(BsfError::AmplificationLimitExceeded)`).
3. **Level 3 — Behavioral Equivalence & Provenance-Preserving Quotient Lenses:**
   - To achieve **strict byte-for-byte `GetPut`** on unmutated syntax while supporting stateful parameter-set edits, model `CodedBitstream` as a **State-Indexed Provenance-Preserving Lens**:
     - Pair active read/write parameter-set environments `(EnvIn, EnvOut)` explicitly in the type signature (`fn transform(&mut self, env_in: &mut CodecEnv, env_out: &mut CodecEnv, frag: &mut Fragment) -> Result<(), CbsError>`).
     - Attach lightweight wire-representation provenance metadata to each `Unit<Ast>`: `framing: FramingTag` (`AnnexB { leading_zeros: u16, trailing_zeros: u16 }` vs `LengthPrefixed { len_size: u8 }`), `obu_size_leb_bytes: Option<u8>`, and `dirty: bool` + `raw_slice: Bytes`. Untouched units (`!dirty` and `env_in == env_out` on referenced parameter sets) emit `raw_slice` verbatim in `O(1)` zero-copy time (`GetPut` holds identically!), while mutated units (`dirty == true`) serialize canonically under `env_out` and preserve unknown extension payloads via `BitVec` / `Bytes` tails (`quietvoid/dovi_tool` pattern).
4. **Level 4 — Spec Conformance & Multi-Pad Differential Fuzzing:**
   - Model the 3-tier side-data precedence lattice (`StreamGlobal < PacketContainer < InBandSei`) as an explicit algebraic join with CVS-persistence counters (`present_until_next_irap`) and lossless multi-message A/53 / T.35 collection (`Vec<T35Payload>` rather than truncating `cc_count` at `31`).
   - Add dedicated multi-pad fuzz harnesses exercising `PacketSync` (`lcevc_merge`) alongside single-pad BSFs, closing the `target_bsf_fuzzer.c:62-64` `AVERROR(ENOTSUP)` blind spot.

## Boundaries

- **Live Execution of `vp9_superframe` `> 4 GiB` Exploit (`not examined`):** The 32-bit `unsigned sum` wraparound in `libavcodec/bsf/vp9_superframe.c:38-69` is established directly from primary source inspection (`Basis: source + derived`); allocating `> 4.5 GiB` of synthetic VP9 invisible frames in RAM to trigger the out-of-bounds `memcpy` crash was intentionally not executed in the lightweight validation sandbox.
- **Bitrate / Cycle Throughput of All `69` Parsers and `57` BSFs (`not examined`):** This audit establishes exact structural classifications, memory-safety contracts, and byte-amplification bounds across all `69` `FFCodecParser`s and `57` `FFBitStreamFilter`s, rather than empirical GB/s throughput benchmarks across codec bitstreams.
- **VP8 `CodedBitstream` Serialization (`unsupported`):** `cbs_vp8.c` explicitly returns `AVERROR_PATCHWELCOME` on `.write_unit` (`lines 357-360`); bidirectional CBS rewriting does not exist for VP8 in upstream FFmpeg at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`.
- **Single-BSF Fuzz Harness Coverage of Multi-Pad Graph BSFs (`known not to apply`):** `tools/target_bsf_fuzzer.c` invokes `av_bsf_alloc()`, which returns `AVERROR(ENOTSUP)` for filters without `.filter` (`lcevc_merge`, `source`, `sink`). Passing `target_bsf_fuzzer` runs therefore provide zero assurance about `libavcodec/bsf/packetsync.c` or `lcevc_merge.c`.
- **Undocumented Dolby Vision RPU Modes (`unsupported` / `unknown`):** In `dovi_rpudec.c`, `NLQ_MU_LAW` (`lines 578-581`), `linear_interp_flag == 1` (`lines 604-611`), and `affected_dm_id != current_dm_id` (`lines 653-661`) are rejected due to absent public Dolby specification details (`unknown` wire semantics in public documentation, `unsupported` in FFmpeg).

## Evidence

### Primary Upstream Source Coordinates

1. **`FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, committed `2026-11-20T01:06:10Z`):**
   - `libavcodec/parsers.c:24-107`, `libavcodec/parser.h:35-65`, `libavcodec/parser.c:89-292`: All `69` `FFCodecParser` declarations, `AV_PARSER_PTS_NB = 4` timestamp ring (`lines 89-118`), `av_parser_parse2` negative-return clamping (`lines 171-200`), and `ff_combine_frame` `next + AV_INPUT_BUFFER_PADDING_SIZE` 64-byte caller overread (`lines 272-274`) + `ENOMEM` `pc->index = 0` reset (`lines 244, 268`).
   - `libavcodec/bitstream_filters.c:27-100`, `libavcodec/bsf.c:100-120`, `libavcodec/bsf/filters.h`, `libavcodec/bsf/packetsync.c`, `tools/target_bsf_fuzzer.c:55-75`: All `57` `FFBitStreamFilter` declarations, multi-pad `AVBitStreamFilterGraph` / `FFPacketSync` architecture, and `!ff_bsf(filter)->filter -> AVERROR(ENOTSUP)` fuzzer exit.
   - `libavcodec/bsf/h264_mp4toannexb.c:325-428`, `libavcodec/bsf/hevc_mp4toannexb.c:407-538`, `libavcodec/bsf/vvc_mp4toannexb.c:237-304`: Quadratic $O(S \cdot E)$ IDR/non-IDR `SPS+PPS` re-injection vs linear $2S + E$ single-injection and `MAX_PS_CHECKS_PER_PACKET` caps.
   - `libavcodec/bsf/vp9_superframe.c:38-69, 169`: Unchecked 32-bit `unsigned sum` / `unsigned sz` wraparound before `av_new_packet(out, sz)` + `memcpy`, and dropped intermediate cached packet side data.
   - `libavcodec/bsf/av1_frame_split.c:51-193`, `libavcodec/bsf/av1_frame_merge.c:26, 46-137`, `libavcodec/bsf/aac_adtstoasc.c:39-130`, `libavcodec/bsf/extract_extradata.c:96-260`, `libavcodec/bsf/setts.c:96, 210-225, 291-298`, `libavcodec/bsf/dovi_rpu.c:79-128`: Zero-copy OBU slicing vs CBS TU re-serialization, ADTS PCE extraction, `double`/`llrint` cross-ISA hazard + missing `.flush`, and `au->nb_units - 1` trailing-NAL bug.
   - `libavcodec/cbs.c:33-64, 179-186, 344-399`, `libavcodec/cbs_internal.h:85-145`, `libavcodec/cbs_bsf.c:154-160`, `libavcodec/cbs_h264.c:265-356, 733`, `libavcodec/cbs_h2645.c:245-404`, `libavcodec/cbs_av1.c:55-67, 127-194, 757-845`, `libavcodec/cbs_jpeg.c:364-404`, `libavcodec/cbs_vp8.c:357-360`: `10` `CodedBitstream` backends, dual `#define READ`/`WRITE` templates, `1 MiB -> 256 MiB` `PutBitContext` doubling, `(input, output)` state contexts, and all 5 `GetPut` violations.
   - `libavcodec/packet.h`, `libavcodec/packet_internal.h:39-83`, `libavutil/frame.h`, `libavcodec/decode.c:1569-1680`, `libavcodec/h2645_sei.c:250-290, 415-455`, `libavcodec/itut35.c:54-149`, `libavcodec/atsc_a53.c:45-125`, `libavcodec/dovi_rpudec.c:46-250, 363-465, 570-770`: `44` packet and `39` frame side-data enums, 3-tier `ff_sd_global_map` / `ff_decode_frame_props_from_pkt` / SEI override pipeline, ITU-T T.35 provider table, A/53 `'GA94'` `0x1F` truncation, and Dolby Vision RPU `RPU_COEFF_FLOAT`/`RPU_COEFF_FIXED` C11 UBs + extension dropping.
2. **`quietvoid/dovi_tool` (`41dae646193c12de152333ff5dbc33579cb9ef4a`, committed `2026-10-24T00:13:01Z`):**
   - `dolby_vision/src/rpu/dovi_rpu.rs:59-67` (`DoviRpu` struct): Preserves `remaining: Option<BitVec<u8, Msb0>>`, unknown `ExtMetadataBlock` bytes, and `trailing_zeroes: usize` across parse/modify/write cycles with MPEG-2 CRC-32 recomputation.
3. **Peer-Reviewed Literature & Normative Specifications:**
   - **Foster, Greenwald, Moore, Pierce, Schmitt (2007):** *Combinators for Bidirectional Tree Transformations: A Linguistic Approach to the View-Update Problem*, ACM TOPLAS 29(3), `doi:10.1145/1232420.1232424` (normative definitions of `GetPut`, `PutGet`, and quotient lenses).
   - **ITU-T H.264 (08/2024), ITU-T H.265 (09/2023), ITU-T H.266 (09/2023):** Annex B byte-stream start codes, RBSP `0x03` emulation prevention, parameter-set activation, and SEI (`MasteringDisplay` `{G,B,R}` primary ordering in H.265 Clause D.2.27).
   - **AOM AV1 v1.0.0 with Errata 1:** §4.10.3 `uvlc()`, §4.10.5 `leb128()` padded `obu_size` legality, and §5.3 OBU framing.
   - **SMPTE ST 2094-40:2020 (`doi:10.5594/SMPTE.ST2094-40.2020`) & ATSC A/53 Part 4:2009:** Normative ITU-T T.35 `0xB5`/`0x003C` HDR10+ and `0xB5`/`0x0031` `'GA94'` closed-caption bitstream formats.

## Revalidation

To revalidate this report against a newer `FFmpeg/FFmpeg` revision:

1. **Parser, BSF, CBS, and Side-Data Census Checks:**
   ```bash
   grep -c '^extern const FFCodecParser ' libavcodec/parsers.c          # expect 69
   grep -cE '^extern +const FFBitStreamFilter ' libavcodec/bitstream_filters.c # expect 57
   grep -c '&cbs_type_' libavcodec/cbs.c                               # expect 10
   ```
2. **Vulnerability & Hazard Diff Targets:**
   - **`parser.c` (`ff_combine_frame` & `av_parser_parse2`):** Check whether `memcpy(&pc->buffer[pc->index], *buf, next + AV_INPUT_BUFFER_PADDING_SIZE)` still overreads `*buf` by 64 bytes and whether `if (index < 0) index = 0;` still masks `AVERROR(ENOMEM)`.
   - **`bsf/vp9_superframe.c` (`stats`):** Check whether `unsigned sum` / `unsigned sz` has been widened to `uint64_t` / `size_t` with `INT_MAX - AV_INPUT_BUFFER_PADDING_SIZE` bounds checking before `av_new_packet(out, sz)`.
   - **`bsf/h264_mp4toannexb.c`:** Check whether `H264_NAL_SLICE` (`unit_type == 1`) still resets `s->new_idr = 1; s->sps_seen = s->pps_seen = 0;` inside a single packet (`O(S * E)` amplification).
   - **`bsf/setts.c` & `bsf/dovi_rpu.c`:** Check whether `setts.c` has added a `.flush` callback or guarded `llrint()` against `isnan`/`isinf`/out-of-range doubles, and whether `dovi_rpu_update_fragment_hevc` iterates backward across `au->units` instead of checking only `au->units[au->nb_units - 1]`.
   - **`dovi_rpudec.c` (`get_ue_coef` / `get_se_coef`):** Check whether `RPU_COEFF_FLOAT` (`fpart.f32 * (1LL << hdr->coef_log2_denom)`) validates finite in-range floats before integer conversion and whether `ipart * (1LL << hdr->coef_log2_denom)` uses `uint64_t` left-shift to avoid signed overflow UB.
   - **`tools/target_bsf_fuzzer.c`:** Check whether an `AVBitStreamFilterGraph` path has been added when `av_bsf_alloc()` returns `AVERROR(ENOTSUP)`.
