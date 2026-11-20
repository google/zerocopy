# ISOBMFF, Matroska, MPEG-TS, HLS/DASH Muxers: Multi-Stream DTS Interleaving, Faststart Relocation, T-STD Pacing, and CENC/CBCS Subsample Cryptography

## Summary

At upstream commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, `libavformat/allformats.c` registers **190 `FFOutputFormat` muxers** (`282,430` physical lines across `libavformat`, SONAME `v63.21.100`), virtually 100% of which are first-party C implementations (`0` SIMD assembly kernels; only `chromaprint` requires an external third-party C library). Unlike `libavformat`'s 373 demuxers (`tools/target_dem_fuzzer.c`), **upstream FFmpeg ships zero dedicated OSS-Fuzz muxer harnesses in `tools/Makefile`**. Six architectural invariants and verified edge-case hazards govern clean-room container muxing, live adaptive streaming, and ISO/IEC 23001-7 Common Encryption:

1. **Extreme Structural Concentration Beneath 190 Registered Muxers:** Exactly **77 of the 190 muxers (`40.5%`)** are headerless or thin-header elementary/PCM pass-through writers (`56` `rawenc.o` elementary stream muxers + `21` `pcmenc.o` raw PCM muxers), and **10** are diagnostic hash/pseudo-muxers (`framecrc`, `framemd5`, `null`, `tee`, `fifo`). Production multi-track multiplexing concentrates into five stateful engines: **`movenc.c`** (`9,902` lines, powering `9` ISOBMFF/QuickTime muxers: `mov`, `mp4`, `tgp`, `tg2`, `psp`, `ipod`, `ismv`, `f4v`, `avif`), **`matroskaenc.c`** (`3,804` lines, powering `matroska`, `matroska_audio`, `webm`), **`hlsenc.c`** (`3,265` lines), **`mpegtsenc.c`** (`2,562` lines), and **`dashenc.c`** (`2,300` lines).
2. **Bounded-Memory DTS Interleaving & Modular 64-Bit Tie-Breaking (`mux.c`):** `ff_interleave_packet_per_dts` (`libavformat/mux.c:984-1064`) maintains a single-linked priority queue with per-stream tail cursors (`sti->last_in_packet_buffer`), waiting until every active stream buffers at least one packet (`stream_count == nb_interleaved_streams`) before popping the minimum-DTS head. Deadlocks on sparse or stalled inputs are broken by `max_interleave_delta` (default `10,000,000` $\mu\text{s} = 10\text{ s}$, `lines 1015-1049`), which deliberately **excludes `AVMEDIA_TYPE_SUBTITLE` streams** from `delta_dts` computation (`line 1033`). Sub-microsecond tie-breaking under `audio_preload` (`interleave_compare_dts`, `lines 971-972`) multiplies timestamps in `uint64_t` that wrap modulo $2^{64}$ after `~35.6` minutes (`90 kHz` video vs. `48 kHz` audio), relying on an implicit $\mathbb{Z}/2^{64}\mathbb{Z}$ cancellation invariant ($|\Delta| < \mathrm{den}_1 \cdot \mathrm{den}_2 < 2^{62} < 2^{63}$) before casting back to signed `int64_t`.
3. **Verified Multi-Stream `stco` $\to$ `co64` Cascading Overwrite Bug in `movenc.c` `faststart`:** When `-movflags +faststart` relocates `moov` ahead of `mdat` at EOF, adding `moov_size` to chunk offsets can push 32-bit `stco` entries past `UINT32_MAX` (`4 GiB`), promoting tracks to 64-bit `co64` (`+4` bytes per chunk) and growing `moov`. While standalone `tools/qt-faststart.c:390-398` avoids cascading growth by upgrading **all** `stco` atoms globally whenever any single offset overflows, `movenc.c:9286-9309` (`compute_moov_size`) upgrades `stco` per stream (`co64_required`, `line 178`) using a hardcoded **2-pass unroll** (`moov_size`, `moov_size2`) rather than iterating to a Kleene fixed point. In a 2-stream `~4 GiB` file where relocating `moov` promotes stream 0 to `co64` in pass 1 and stream 0's `+4 * chunkCount` growth pushes stream 1 across `UINT32_MAX` in pass 2, `shift_data` shifts `mdat` by `moov_size2` while `mov_write_moov_tag` (`line 9451`) emits `moov_size2 + 4 * chunkCount_1` bytes—**overwriting the start of `mdat` on disk** (`40,000` bytes corrupted in our standalone C reproduction).
4. **Two-Mode Seekable vs. Pipe-Safe Container Serialization (`movenc.c` fMP4/CMAF & `matroskaenc.c` EBML):** Non-seekable live pipes cannot backpatch top-level atom/element lengths. ISOBMFF solves this via CMAF / fragmented MP4 (`FF_MOV_FLAG_CMAF` / `FF_MOV_FLAG_EMPTY_MOOV`, emitting an empty `moov` initialization header followed by self-contained `sidx` + `moof` [`mfhd` + `traf` (`tfhd`, 64-bit `tfdt`, version-1 signed-CTS `trun`)] + `mdat` fragments, `movenc.c:5924-6380`); Matroska/WebM (`matroskaenc.c:331-480, 2685`) solves it by writing RFC 8794 `EBML_UNKNOWN_LENGTH` (`0x01FFFFFFFFFFFFFF`) on `Segment` and `Cluster` masters when `is_live == 1`, whereas seekable files buffer level-1 elements in memory (`start_ebml_master_crc32`) to prepend IEEE CRC-32 checksums and backpatch a `Void`-reserved `SeekHead` + EOF `Cues`.
5. **Open-Loop MPEG-TS T-STD Buffer Enforcement (`mpegtsenc.c`) and File-Only HLS/DASH Rename Atomicity (`hlsenc.c`, `dashenc.c`):** `mpegtsenc.c` (`lines 1019-1023, 1446-1735`) synthesizes 42-bit `27 MHz` Program Clock References (`PCR`) from byte count in CBR mode (`mux_rate > 1`, adding `+11` bytes per ITU-T H.222.0 §2.4.3.5) and inserts `PID 0x1FFF` null packets when `(dts - pcr/300) > delay`, **but** when video encoder bursts violate CPB bounds (`dts < pcr / 300`, `lines 1729-1730`), `mpegtsenc.c` merely logs `"dts < pcr, TS is invalid"` and emits non-conformant TS packets. Similarly, `hlsenc.c` (`lines 1435, 1640, 1826`) and `dashenc.c` (`lines 1104, 1835`) provide atomic `write(.tmp) -> rename()` manifest/segment publication **only on local POSIX `file:` URLs** (without `fsync` prior to `rename`), falling back to non-atomic direct writes over HTTP PUT/POST ingest.
6. **Asymmetric CENC/CBCS Cryptography and Three Concrete Spec/Safety Defects (`movenccenc.c`, `mov.c`, `aes_ctr.c`):**
   - **Muxer vs. demuxer asymmetry:** `movenc.c` (`line 84, 8735`) encrypts **only** `cenc` (`AES-128-CTR`), lacking `cbc1`, `cens`, and `cbcs` muxing entirely, and `hlsenc.c:1837` explicitly rejects encrypted fMP4 (`"Encrypted fmp4 not yet supported"`). Conversely, `mov.c:9047-9061` decrypts all four ISO/IEC 23001-7 schemes (`cenc`, `cbc1`, `cens`, `cbcs`).
   - **Three concrete defects verified in source:** (a) `movenc.c:7520-7522` routes **HEVC** (`2`-byte NAL header) through `ff_mov_cenc_avc_write_nal_units` (`movenccenc.c:258-277`), leaving only `nal_length_size + 1` bytes clear—encrypting the second byte of every HEVC NAL header and encrypting non-VCL VPS/SPS/PPS/SEI NALs in violation of ISO/IEC 23001-7 §9.5 (plus signed shift UB `nalsize = (nalsize << 8) | *buf_in++` at `line 262`); (b) `mov.c:8954, 9026` (`cens_scheme_decrypt` and `cbcs_scheme_decrypt`) breaks out of the pattern loop whenever `rem_bytes < 16 * sample->crypt_byte_block`, leaving $\lfloor\text{rem\_bytes}/16\rfloor$ complete 16-byte AES blocks **undecrypted** when `crypt_byte_block > 1` and $16 \le \text{rem\_bytes} < 16 \cdot \text{crypt\_byte\_block}$ (violating ISO/IEC 23001-7 §9.6.1 / §10.4.2); and (c) `libavutil/aes_ctr.c:64-72` generates random CTR IVs from non-cryptographic `av_get_random_seed()`.

---

## Applicability

This report characterizes **`FFmpeg/FFmpeg`** (`libavformat` `v63.21.100`, `libavutil` `v61.21.100`, and `tools/qt-faststart.c`) at exact commit **`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`** (`2026-11-20T01:06:10Z`), evaluated against eight normative container, transport, streaming, and media-encryption standards listed in `REPORT.json`:
- **ISO/IEC 14496-12:2022** (ISOBMFF box hierarchy, `stco`/`co64`, `edts`/`elst`, `moof`/`traf`/`tfdt`/`trun`, `sidx`, `mfra`);
- **ISO/IEC 23001-7:2023** (Common Encryption `cenc`, `cbc1`, `cens`, and `cbcs` subsample/pattern schemes, `tenc`/`senc`/`saiz`/`saio`/`pssh`);
- **ISO/IEC 23000-19:2024** (CMAF track, switching-set, chunk, and fragment constraints unifying HLS and DASH fMP4 delivery);
- **ITU-T Rec. H.222.0 | ISO/IEC 13818-1:2023** (MPEG-2 Transport Stream 188-byte packetization, PES headers, `27 MHz` PCR, PSI tables, and T-STD buffer model);
- **IETF RFC 8794** (EBML variable-length integers `VINT`, master elements, and unknown-size semantics) and **IETF RFC 9559** (Matroska v1–v4 `Segment`, `SeekHead`, `Tracks`, `Cluster`, `SimpleBlock`, `BlockGroup`, and `Cues`);
- **IETF RFC 8216** (HTTP Live Streaming M3U8 playlists, `#EXT-X-KEY`, `#EXT-X-MAP`, `#EXT-X-TARGETDURATION`, segment atomicity) and **ISO/IEC 23009-1:2022** (MPEG-DASH MPD `SegmentTemplate` and `SegmentTimeline`).

**Companion corpus cross-references:** Pair this report with `isobmff-mp4-matroska-mpegts-hls-dash-demuxer-muxer-edge-cases-and-fuzz-hazards` (demuxer parsing hazards, index-table OOMs, and input fuzzing), `ffmpeg-c-abi-libav-struct-layout-callbacks-and-rust-ffi-compatibility-layer` (`AVIOContext` custom I/O callbacks and `AVPacket`/`AVBufferRef` lifetimes), `everparse-lowparse-strong-prefix-clens-and-nonmalleable-zero-copy-codecs` (verified non-malleable wire format combinators), and `ffmpeg-first-party-video-and-audio-encoders-ffv1-prores-dnxhd-flac-aac-opus` (encoder packet/extradata emission contracts).

---

## Findings

### 1. Exhaustive Census of All 190 `FFOutputFormat` Muxers and `AVIOContext` Sink Modes

**Basis:** source (`FFmpeg/FFmpeg` @ `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`: `libavformat/allformats.c:1-650`, `libavformat/Makefile`, `configure`, `libavformat/avio.h`, `libavformat/aviobuf.c`, `tools/Makefile`).

#### 1.1 Disjoint Architectural Partition of `libavformat`'s 190 Muxers

Unfolding `libavformat/Makefile` object bindings across all `190` `extern const FFOutputFormat ff_*_muxer;` symbols in `allformats.c` partitions the entire muxer surface into **10 disjoint classes**:

| Muxer Class | Count | Primary Implementation Files | Registered `FFOutputFormat` Names | Seekability Contract (`pb->seekable`) |
| :--- | ---: | :--- | :--- | :--- |
| **1. Raw Elementary Streams** | **56** | `rawenc.c` (`rawenc.o`) | `ac3`, `adx`, `amr`, `aptx`, `aptx_hd`, `avs2`, `avs3`, `cavsvideo`, `codec2raw`, `data`, `dfpwm`, `dirac`, `dnxhd`, `dts`, `eac3`, `evc`, `g722`, `g723_1`, `g726`, `g726le`, `gsm`, `h261`, `h263`, `h264`, `hevc`, `lcevc`, `m4v`, `mjpeg`, `mlp`, `mp2`, `mpeg1video`, `mpeg2video`, `obu`, `rawvideo`, `sbc`, `truehd`, `vc1`, `vvc`, *+18 legacy raw formats* | Pure sequential stream (`AVFMT_NOTIMESTAMPS`); zero seeking |
| **2. Raw PCM Formats** | **21** | `pcmenc.c` + `rawenc.c` | `pcm_{s,u}{8,16,24,32}{le,be}`, `pcm_f{32,64}{le,be}`, `pcm_alaw`, `pcm_mulaw`, `pcm_vidc` | Pure sequential stream; zero seeking |
| **3. ISOBMFF / QuickTime Family** | **9** | `movenc.c` (`9,902L`), `movenccenc.c` (`648L`), `movenc_ttml.c` (`318L`) | `mov`, `mp4`, `tgp` (`3gp`), `tg2` (`3g2`), `psp`, `ipod`, `ismv`, `f4v`, `avif` | Requires `AVIO_SEEKABLE_NORMAL` unless fragmented (`FF_MOV_FLAG_FRAGMENT` + `EMPTY_MOOV`) |
| **4. Adaptive / Segmented Streaming** | **8** | `hlsenc.c` (`3,265L`), `dashenc.c` (`2,300L`), `segment.c` (`1,136L`), `hlsplaylist.c` (`204L`) | `hls`, `dash`, `segment`, `stream_segment`, `smoothstreaming`, `hds`, `webm_chunk`, `webm_dash_manifest` | Multi-object sink (`io_open` / `io_close` callbacks + atomic `ff_rename` on `file:`) |
| **5. MPEG-2 TS & MPEG-1/2 PS** | **6** | `mpegtsenc.c` (`2,562L`), `mpegenc.c` | `mpegts`, `mpeg1system`, `mpeg1vcd`, `mpeg2dvd`, `mpeg2svcd`, `mpeg2vob` | Pure sequential 188-byte TS / pack stream; zero seeking |
| **6. Matroska / WebM (EBML)** | **3** | `matroskaenc.c` (`3,804L`) | `matroska` (`.mkv`), `matroska_audio` (`.mka`), `webm` (`.webm`) | Dual-mode: backpatches `SeekHead`/`Info`/`Tracks` when seekable; `EBML_UNKNOWN_LENGTH` on pipes (`is_live`) |
| **7. Dedicated Audio Containers** | **15** | `oggenc.c`, `flacenc.c`, `wavenc.c`, `aiffenc.c`, `cafenc.c`, `adtsenc.c` | `ogg`, `oga`, `ogv`, `opus`, `spx`, `flac`, `wav`, `w64`, `aiff`, `caf`, `adts`, `ast`, `tta`, `voc`, `wv` | `ogg`/`adts` stream sequentially; `wav`/`w64`/`aiff`/`flac` backpatch RIFF/FORM/STREAMINFO sizes & MD5 if seekable |
| **8. Real-Time RTP / WebRTC** | **5** | `rtpenc*.c`, `rtspenc.c`, `whip.c` | `rtp`, `rtp_mpegts`, `rtsp`, `sap`, `whip` | Packet-sized datagram framing (`max_packet_size` MTU bound) |
| **9. Hash, Tee & Fifo Meta-Muxers** | **10** | `hashenc.c`, `framehash.c`, `nullenc.c`, `tee.c`, `fifo.c` | `framecrc`, `framehash`, `framemd5`, `streamhash`, `uncodedframecrc`, `hash`, `md5`, `null`, `tee`, `fifo` | Zero-seek diagnostic / FATE oracle sinks (`fifo` spawns background writer thread) |
| **10. Broadcast, Legacy, Image & Subtitle** | **57** | `mxfenc.c`, `nutenc.c`, `avienc.c`, `flvenc.c`, `asfenc.c`, `iamfenc.c`, `img2enc.c`, *etc.* | `mxf`, `mxf_d10`, `mxf_opatom`, `gxf`, `nut`, `avi`, `asf`, `asf_stream`, `wtv`, `flv`, `swf`, `avm2`, `iamf`, `apv`, `ac4`, `lc3`, `ivf`, `webp`, `apng`, `gif`, `image2`, `image2pipe`, `yuv4mpegpipe`, `srt`, `webvtt`, `ttml`, `ass`, `scc`, `mcc`, `rcwt`, `sup`, `spdif`, `chromaprint`, *etc.* | Mixed (`mxf`/`nut`/`flv`/`mpegts`-like broadcast vs. RIFF `avi` `idx1` backpatching) |

---

### 2. `libavformat/mux.c`: Multi-Stream DTS Interleaving, Negative-TS Normalization, and Modular Arithmetic

**Basis:** source (`libavformat/mux.c:455-1465`, `libavformat/mux.h`, `libavformat/mux_utils.c`) + execution (standalone `-fsanitize=undefined` C probe, §Evidence).

#### 2.1 Timestamp Offset Normalization (`avoid_negative_ts`) and Monotonicity Guards

Before packets reach a container's `.write_packet` callback, `prepare_input_packet` and `compute_muxer_pkt_fields` (`mux.c:554-680`) enforce three core invariants:
1. **Uniform cross-stream non-negative shifting (`handle_avoid_negative_ts`, `mux.c:681-765`):** Codecs with encoder delay or B-frame reordering emit initial packets with `dts < 0` (e.g., AAC `-1024`, H.264/HEVC `-2` ticks), which formats lacking signed timestamps (`mpegts`, `matroska` unsigned cluster timestamps, `flv`, standard v0 `trun`) reject or misinterpret. When `avoid_negative_ts` resolves to `MAKE_NON_NEGATIVE` or `MAKE_ZERO` (`lines 458-466`), the first packet observed across all streams with `ts < 0` (or `ts != 0` under `MAKE_ZERO`) locks `si->ts_offset = av_rescale_q_rnd(-ts, st->time_base, AV_TIME_BASE_Q, AV_ROUND_UP)` (`AVOID_NEGATIVE_TS_KNOWN`, `line 727`), adding per-stream `sti->mux_ts_offset` uniformly across every stream so A/V sync is preserved. **Hazard (`lines 700-752`):** If a caller invokes unbuffered `av_write_frame` instead of `av_interleaved_write_frame` and delivers a positive-timestamp packet on stream 0 before a more-negative packet on stream 1, `si->ts_offset` locks prematurely, leaving stream 1 still negative and triggering `check_packet` / muxer failure.
2. **Strict / non-strict DTS monotonicity (`mux.c:630-665, 806`):** Unless `s->oformat->flags & (AVFMT_NOTIMESTAMPS | AVFMT_TS_NONSTRICT)`, `compute_muxer_pkt_fields` rejects any packet with `pkt->dts < sti->cur_dts` (or `pkt->dts <= sti->cur_dts` for non-subtitle streams with `pkt->duration == 0`) with `AVERROR(EINVAL)` (`"Application provided invalid, non monotonically increasing dts to muxer"`), and rejects `pkt->pts < pkt->dts` (`"pts < dts"`).

#### 2.2 DTS Priority Queue (`ff_interleave_packet_per_dts`) and `max_interleave_delta` Starvation Semantics

`av_interleaved_write_frame` (`mux.c:1268`) delegates to `s->oformat->interleave_packet` (defaulting to `ff_interleave_packet_per_dts`, `mux.c:984-1064`):
- **Queue structure (`ff_interleave_add_packet`, `mux.c:880-952`):** Packets are stored in a singly linked list `si->packet_buffer` sorted by `interleave_compare_dts`. Each stream caches `sti->last_in_packet_buffer`: a new packet on stream `i` begins insertion **at `sti->last_in_packet_buffer->next`** (`line 905`), guaranteeing within-stream FIFO order even if timestamps tie, and achieving $O(1)$ tail append when the new packet has the largest global DTS (`lines 931, 939`), degrading to $O(Q)$ linear scan over queued cross-stream packets otherwise.
- **Barrier vs. bounded-latency flush (`mux.c:998-1050`):** Normally `flush = 1` triggers only when `stream_count == fci->nb_interleaved_streams` (`line 1012`—every active stream has $\ge 1$ queued packet). Attachments (`AVMEDIA_TYPE_ATTACHMENT`), `VP8`, `VP9`, and `SMPTE_2038` streams are excluded from `noninterleaved_count` (`lines 1004-1008`) so sparse alt-ref/metadata tracks do not block startup. Once all active streams have been seen or accounted for (`line 1019`), if one stream stalls mid-stream, `delta_dts = max_i(last_dts_i) - top_dts` (`lines 1021-1040`, **skipping `AVMEDIA_TYPE_SUBTITLE` at `line 1033`**) forces `flush = 1` whenever `delta_dts > s->max_interleave_delta` (default `10s`).
  - **Clean-room hazard:** Because subtitles are skipped in `delta_dts` (`line 1033`) *yet* counted in `noninterleaved_count` (`line 1004`), a muxing pipeline with an active subtitle stream that produces zero packets for the first `30` seconds holds video and audio packets in `si->packet_buffer` until `delta_dts > max_interleave_delta` flushes them, and if `max_interleave_delta == 0` (unbounded mode), buffers unboundedly until OOM or first subtitle cue!
- **Modular 64-bit wraparound cancellation in `interleave_compare_dts` (`mux.c:954-982`):** When `s->audio_preload != 0` and microsecond-rescaled timestamps tie (`ts == ts2`, `line 970`), lines `971-972` evaluate exact cross-multiplied numerators in `uint64_t`:
  ```c
  ts = ((uint64_t)pkt->dts * st->time_base.num * AV_TIME_BASE - (uint64_t)preload * st->time_base.den) * st2->time_base.den
     - ((uint64_t)next->dts * st2->time_base.num * AV_TIME_BASE - (uint64_t)preload2 * st2->time_base.den) * st->time_base.den;
  ```
  For `1/90000` video and `1/48000` audio (`AV_TIME_BASE = 1,000,000`), each `uint64_t` product exceeds `INT64_MAX` after `2,135` seconds (`35.6` minutes) and wraps modulo $2^{64}$ over `40` times in a 24-hour broadcast. Nevertheless, because the `ts == ts2` guard ensures the true mathematical integer difference $D = E_1 - E_2$ satisfies $|D| < 1\,\mu\text{s} \cdot \mathrm{den}_1 \cdot \mathrm{den}_2 \le \mathrm{INT32\_MAX}^2 < 2^{62} < 2^{63}$, both `uint64_t` operands wrap by the same multiple of $2^{64}$ (modulo a single borrow), so `(int64_t)(u1 - u2)` recovers the exact signed difference $D$ under two's-complement conversion (verified against 128-bit `__int128` arithmetic in §Evidence). In a verified Rust rewrite, replacing this subtle modular trick with explicit `i128` arithmetic eliminates the delicate $|D| < 2^{63}$ proof obligation at negligible CPU cost.

---

### 3. `movenc.c`: Two-Pass `faststart` `stco`/`co64` Fixed-Point Bug, fMP4/CMAF, and `elst` Audio Priming

**Basis:** normative (`ISO/IEC 14496-12:2022` §§8.6.5, 8.7.5, 8.8; `ISO/IEC 23000-19:2024`) + source (`libavformat/movenc.c:178-225, 4371-4480, 5924-6395, 8480-9505`, `tools/qt-faststart.c:299-428`) + execution (`probe_muxers.c`, §Evidence).

#### 3.1 Multi-Stream `stco` $\to$ `co64` Cascading Overwrite Bug in `compute_moov_size`

In progressive ISOBMFF files (`ftyp` + `mdat` + `moov`), chunk offsets in each track's Sample Table (`stbl`) are absolute byte offsets from byte `0` of the file: `stco` stores 32-bit big-endian offsets ($\le \mathrm{UINT32\_MAX} = 4,294,967,295$), while `co64` stores 64-bit offsets (`movenc.c:178-223`):
```c
static int co64_required(const MOVTrack *track) {
    if (track->entry > 0 && track->cluster[track->entry - 1].pos + track->data_offset > UINT32_MAX)
        return 1;
    return 0;
}
```
When `-movflags +faststart` (`FF_MOV_FLAG_FASTSTART`) runs at `mov_write_trailer` (`movenc.c:9445-9453`), `shift_data(s)` (`line 9326`) calls `compute_moov_size(s)` (`lines 9286-9309`) to determine how many bytes to shift `mdat` forward on disk via `ff_format_shift_data`:
```c
moov_size = get_moov_size(s);
for (i = 0; i < mov->nb_tracks; i++)
    mov->tracks[i].data_offset += moov_size;
moov_size2 = get_moov_size(s);
if (moov_size2 != moov_size)
    for (i = 0; i < mov->nb_tracks; i++)
        mov->tracks[i].data_offset += moov_size2 - moov_size;
return moov_size2;
```
**Why this 2-pass unroll is unsound for $N \ge 2$ tracks:** Let $F(\Delta)$ be the serialized byte size of `moov` when every track's `data_offset` increases by $\Delta$:
$$F(\Delta) = M_{\mathrm{base}} + \sum_{k=0}^{N-1} \Bigl(16 + 4 \cdot C_k \cdot \bigl(1 + \mathbf{1}[\,\mathrm{last\_pos}_k + d_{k,0} + \Delta > 2^{32}-1\,]\bigr)\Bigr)$$
$F$ is a monotone non-decreasing step function with **up to $N$ discontinuities** (one per track promoting from `stco` to `co64`). By Kleene's fixed-point theorem, computing the least fixed point $\Delta^* = F(\Delta^*)$ from $\Delta_0 = 0$ requires up to **$N + 1$ evaluations** of $F$. `compute_moov_size` stops after **2 evaluations** (`moov_size = F(0)`, `moov_size2 = F(F(0))`), updates `data_offset` to $\Delta_2 = F(F(0))$, and returns `moov_size2 = \Delta_2` without checking whether $F(\Delta_2) > \Delta_2$!
- **Concrete failure trace (verified by execution in `probe_muxers.c`):** With 2 streams of $C_0 = C_1 = 10,000$ chunks each (`M_base + headers = 90,000` bytes with `stco`), where stream 0's last chunk sits at `UINT32_MAX - 10,000` and stream 1's last chunk sits at `UINT32_MAX - 110,000`:
  1. `moov_size = F(0) = 90,000`. Adding `+90,000` pushes stream 0 to `UINT32_MAX + 80,000` (`co64`), while stream 1 reaches `UINT32_MAX - 20,000` (still `stco`).
  2. `moov_size2 = F(90,000) = 130,000`. Lines `9304-9306` add `moov_size2 - moov_size = +40,000` to all tracks, pushing stream 1 to `UINT32_MAX + 20,000`!
  3. `shift_data` shifts `mdat` on disk by only **`130,000` bytes**, after which `mov_write_moov_tag` (`line 9451`) evaluates `co64_required` on the updated `data_offset`, promotes **both** streams to `co64`, and writes **`170,000` bytes** at `reserved_header_pos`—**clobbering the first `40,000` bytes of `mdat` payload** and desynchronizing every chunk offset in the file by `-40,000` bytes!
- **Contrast with `tools/qt-faststart.c:390-398`:** `qt-faststart.c` avoids this cascade by unconditionally upgrading **every** `stco` atom in `moov` to `co64` in one pass whenever `update_context.stco_overflow != 0` (`new_moov_size = *moov_atom_size + stco_offset_count * 8 - stco_data_size`). A clean-room muxer retaining space-optimal per-track `stco`/`co64` selection **must** replace `compute_moov_size`'s 2-step unroll with `while (cur != prev)` (guaranteed to terminate in $\le N + 1$ iterations).

*(Note: `movenc.c:9350, 9471-9477` also implements `FF_MOV_FLAG_HYBRID_FRAGMENTED`, which writes crash-safe fMP4 `moof`+`mdat` fragments during recording behind an initial `free`/`wide` placeholder and, upon clean `mov_write_trailer`, writes a classic `moov` at EOF and overwrites the initial placeholder into a single giant `mdat` hiding the internal `moof` boxes from classic MP4 readers.)*

#### 3.2 Fragmented MP4 / CMAF (`moof` / `tfdt` / `trun` / `sidx`) and `elst` Negative-CTS Audio Priming

1. **CMAF & fMP4 structural invariants (`movenc.c:5924-6265, 8503-8555`):** Enabling `-movflags +cmaf` (`FF_MOV_FLAG_CMAF`, `lines 8503-8506`) implies `FF_MOV_FLAG_FRAGMENT | FF_MOV_FLAG_EMPTY_MOOV | FF_MOV_FLAG_DEFAULT_BASE_MOOF | FF_MOV_FLAG_NEGATIVE_CTS_OFFSETS`:
   - `DEFAULT_BASE_MOOF` sets `default-base-is-moof` in `tfhd`, anchoring `trun.data_offset = moof_size + 8 + track->data_offset + track->cluster[first].pos` (`lines 5960-5961`) relative to the enclosing `moof`'s first byte rather than absolute file position—making every CMAF chunk independently addressable over HTTP byte-range or chunked transfer.
   - `tfdt` (`mov_write_tfdt_tag`, `lines 6102-6112`) always emits **version `1`** (64-bit `baseMediaDecodeTime = track->cluster[0].dts - track->start_dts`), preventing 32-bit timestamp rollover (`~13.25` hours at `90 kHz`) on 24/7 live streams.
   - `NEGATIVE_CTS_OFFSETS` emits **`trun` version `1`** (`line 5949`), making `sample_composition_time_offset` signed `int32_t` so B-frame video tracks maintain `PTS == DTS` on I/P frames (`CTS_offset <= 0` on reordered frames) without introducing synthetic startup composition delay—allowing `movenc.c:8548` to disable edit lists under CMAF where ISO/IEC 23000-19 discourages multi-entry presentation shifts.
   - `mov_write_sidx_tags` (`lines 6181-6265`) runs a 2-round sizing pass (`ffio_open_null_buf` in round 0, real `AVIOContext` in round 1) so each per-track `sidx` version-1 box accurately points `first_offset = pos + total_sidx_size - end_pos` (`line 6235`) past subsequent `sidx` boxes to the shared `moof`.
2. **`edts`/`elst` edit-list invariants & the `media_time == -1` trap (`movenc.c:4371-4479`):**
   - **Positive presentation delay (`delay > 0`, e.g., B-frame startup without negative CTS, `lines 4425-4439`):** Emits `entry_count = 2`: entry 0 is an empty delay edit (`segment_duration = delay`, **`media_time = -1`**) followed by entry 1 playing media from `start_ct`.
   - **Audio encoder priming / negative `start_dts < 0` (`delay <= 0`, e.g., AAC 1024/2112-sample MDCT overlap or Opus 312-sample pre-skip, `lines 4439-4455`):** Emits `entry_count = 1` with `media_time = start_ct = -FFMIN(start_dts, 0) >= 0` (explicitly rescaled to `48000` Hz for IAMF Opus at `lines 4448-4449`), instructing compliant decoders to decode from sample 0 and discard the first `start_ct` primed samples. Line `4444` enforces `av_assert0(av_rescale_rnd(start_dts, mov->movie_timescale, track->timescale, AV_ROUND_DOWN) <= 0)` and clamps via `-FFMIN(start_dts, 0)` specifically so a tiny positive `start_dts == 1` rounding to `delay == 0` in `movie_timescale` can **never** set `start_ct = -1` and accidentally turn the entire audio track into a silent empty edit!

---

### 4. `matroskaenc.c`, `mpegtsenc.c`, and `hlsenc.c`/`dashenc.c`: Streaming vs. Backpatching, T-STD Pacing, and Segment Rotation

**Basis:** normative (`IETF RFC 8794`, `IETF RFC 9559`, `ITU-T H.222.0:2023`, `IETF RFC 8216`, `ISO/IEC 23009-1:2022`) + source (`libavformat/matroskaenc.c:331-960, 2640-3495`, `libavformat/mpegtsenc.c:1019-1735, 2005-2550`, `libavformat/hlsenc.c:1366-1845, 2880-3255`, `libavformat/dashenc.c:209-565, 986-2290`).

#### 4.1 `matroskaenc.c`: EBML VINT Reservation vs. `EBML_UNKNOWN_LENGTH` Live Mode

- **RFC 8794 VINT length encoding (`matroskaenc.c:331-392`):** An $n$-byte EBML VINT ($1 \le n \le 8$) carries a leading marker bit `1 << (7*n)` and $7n$ payload bits. Because all-ones payload bits (`(1ULL << (7*n)) - 1`, e.g., `0xFF` for 1-byte or `0x01FFFFFFFFFFFFFF` for 8-byte) denote **unknown data size** (`put_ebml_size_unknown`, `line 331`), `ebml_length_size(length)` computes `ebml_num_size(length + 1)` (`line 359`), and `put_ebml_length` (`lines 384, 390`) executes `av_assert0(length < (1ULL << 56) - 1)` and `av_assert0(bytes >= needed_bytes)`.
- **Seekable backpatching (`!mkv->is_live`, `lines 798-960, 3335-3490`):** `mkv_start_seekhead` (`line 901`) writes a `put_ebml_void` placeholder (`MAX_SEEKHEAD_ENTRIES * MAX_SEEKENTRY_SIZE + 14` bytes) immediately inside `Segment`. Level-1 elements (`Info`, `Tracks`, `Chapters`, `Tags`, `Cluster`, `Cues`) serialize into dynamic memory buffers (`start_ebml_master_crc32`, `line 798`) so `end_ebml_master_crc32` (`line 811`) can compute an IEEE CRC-32 (`EBML_ID_CRC32`) over the exact payload and write minimal-width VINT sizes. At `mkv_write_trailer`, `Cues` is appended (`line 3335`), and `mkv_write_seekhead` (`line 3407`) seeks back to overwrite the `Void` space (filling any unused slack with a smaller trailing `Void` element, `line 953`).
- **Live streaming (`mkv->is_live == 1`, `line 2685`):** Suppresses `SeekHead` reservation, CRC-32 dynamic buffering of the root `Segment`, and EOF `Cues`, emitting `Segment` and `Cluster` masters with 8-byte `0x01FFFFFFFFFFFFFF` unknown lengths so bytes flush forward with zero `avio_seek` calls.

#### 4.2 `mpegtsenc.c`: `27 MHz` PCR Synthesis, Null-Packet Stuffing, and Open-Loop T-STD Limits

ITU-T H.222.0 requires `90 kHz` 33-bit PTS/DTS timestamps synchronized to a `27 MHz` Program Clock Reference (`PCR = pcr_base * 300 + pcr_ext`, `SYSTEM_CLOCK_FREQUENCY_DIVISOR = 300`, packed into 6 adaptation-field bytes by `write_pcr_bits`, `mpegtsenc.c:1446-1456`):
- **CBR byte-clock coupling (`mux_rate > 1`, `lines 1019-1023`):**
  ```c
  static int64_t get_pcr(const MpegTSWrite *ts) {
      return av_rescale(ts->total_size + 11, 8 * PCR_TIME_BASE, ts->mux_rate) + ts->first_pcr;
  }
  ```
  The `+ 11` byte offset is normative: H.222.0 §2.4.3.5 defines `PCR(i)` at the byte containing the last bit of `program_clock_reference_base` (`4`-byte TS header + `2`-byte adaptation length/flags + `5`-byte `pcr_base` = byte index `10`, i.e., `11` bytes elapsed).
- **PSI & PCR scheduling (`lines 1094-1156, 1413-1725`):** Retransmits `PAT`/`PMT` (`pat_period`), `SDT` (`sdt_period`), and `NIT`, and emits PCR every `pcr_period_ms` (default `PCR_RETRANS_TIME = 20 ms`, safely within DVB's `40 ms` and H.222.0's `100 ms` ceilings) either in the primary video PID's adaptation field or on a dedicated PCR-only PID (`mpegts_pcr_pid`, `lines 1144-1150, 1476`).
- **T-STD underflow gap (`lines 1668-1731`):** When `dts - pcr / 300 > delay` (`s->max_delay`), `mpegts_write_pes` stuffs `PID 0x1FFF` null packets (interleaved with scheduled PCR-only packets so PCR jitter never exceeds `pcr_period`) to prevent T-STD transport buffer (`TB_n` = 512 bytes) / multiplexing buffer (`MB_n`) **overflow**. However, `mpegtsenc.c` implements **no closed-loop leaky-bucket T-STD simulator**: if upstream encoder VBV bursts cause `total_size` to advance `pcr / 300` past `dts` (`dts < pcr / 300`, `lines 1729-1730`), `mpegtsenc.c` logs `AV_LOG_WARNING` (`"dts < pcr, TS is invalid\n"`) and emits late access units anyway—causing hardware broadcast decoders to drop frames on T-STD underflow.

#### 4.3 `hlsenc.c` and `dashenc.c`: Segment Rotation Atomicity Boundaries

- **Local POSIX rename atomicity vs. HTTP ingest (`hlsenc.c:1366, 1435, 1609, 1640, 1826`; `dashenc.c:1003, 1104, 1835`):** On `file:` URLs, `dashenc.c` unconditionally writes media segments (`.tmp`) and `.mpd`/`.m3u8` manifests to temporary paths and commits via `ff_rename` (`rename(2)`), ensuring HTTP readers polling local disk never observe truncated playlists or half-written `.m4s` segments. In `hlsenc.c`, playlist temp-rename defaults ON for live/event playlists (`!(pl_type == PLAYLIST_TYPE_VOD)`, `line 1609`), **but segment temp-rename requires explicit `-hls_flags temp_file`** (`HLS_TEMP_FILE`, `lines 1826, 2614, 2884`)! Furthermore:
  1. Neither `dashenc.c` nor `hlsenc.c` invokes `fsync(2)` on the temporary segment/manifest file descriptor prior to `rename(2)` or on the parent directory afterward—providing reader concurrency isolation, **not** power-loss crash durability.
  2. When publishing over `http://` / `https://` (`PUT`/`POST` to a CDN origin), `is_file_proto` is `0` (`hlsenc.c:1640` logs a warning if `HLS_TEMP_FILE` was requested); atomicity depends entirely on the remote HTTP origin buffering `PUT` bodies until clean chunked-transfer termination (`0\r\n\r\n`) and strictly ordering segment `PUT` completion before manifest `PUT` initiation.

---

### 5. ISO/IEC 23001-7 Common Encryption (`cenc` vs. `cbcs`): Asymmetric Coverage and Three Upstream Defects

**Basis:** normative (`ISO/IEC 23001-7:2023` §§8–10) + source (`libavformat/movenc.c:84, 7459-7539, 8735`, `libavformat/movenccenc.c:105-645`, `libavformat/mov.c:8660-9061`, `libavutil/aes_ctr.c:34-135`, `libavutil/encryption_info.c`, `libavformat/hlsenc.c:1670, 1837`).

#### 5.1 Four-Scheme Capabilities Matrix in FFmpeg (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`)

| ISO/IEC 23001-7 Scheme | Cipher & Mode | Pattern (`crypt:skip` 16B blocks) | IV Size & Subsample Chaining Rule | `mov.c` Demuxer Decrypt (`L9047`) | `movenc.c` / `movenccenc.c` Muxer Encrypt | `hlsenc.c` Support |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`cenc`** | AES-128-CTR | None (full protected range) | 8B or 16B; continuous CTR block counter across all subsamples of 1 sample | **Supported** (`cenc_scheme_decrypt`, `L9050`) | **Supported** (`cenc-aes-ctr`, `movenc.c:84, 8735`; 8B IV + 8B block ctr) | **Unsupported** for fMP4 (`hlsenc.c:1837`) |
| **`cbc1`** | AES-128-CBC | None (`BytesOfProtectedData % 16 == 0`) | 16B; continuous CBC IV chaining across subsamples of 1 sample | **Supported** (`cbc1_scheme_decrypt`, `L8838`) | **Unsupported** | **Unsupported** |
| **`cens`** | AES-128-CTR | Required (e.g., `1:9`) | 8B or 16B; continuous CTR block counter across encrypted blocks of 1 sample | **Partial — Defect 2** (`cens_scheme_decrypt`, `L8904`) | **Unsupported** | **Unsupported** |
| **`cbcs`** | AES-128-CBC | Required (e.g., `1:9` video, `0` or whole-block audio) | 16B constant IV; **resets IV to `sample->iv` at the start of every subsample** (`mov.c:9022`) | **Partial — Defect 2** (`cbcs_scheme_decrypt`, `L8975`) | **Unsupported** | **Unsupported** for fMP4 (`AES-128` TS whole-segment CBC only, `L1670`) |

#### 5.2 Three Concrete Cryptographic & Normative Defects Verified in Upstream Source

1. **Defect 1 — HEVC 2-Byte NAL Header Encryption & Signed Shift UB (`movenc.c:7520-7522`, `movenccenc.c:250-277`):**
   - In `movenc.c:7517-7522`, both `AV_CODEC_ID_H264` and `AV_CODEC_ID_HEVC` invoke the exact same function `ff_mov_cenc_avc_write_nal_units(s, &trk->cenc, nal_size_length, pb, pkt->data, size)`.
   - Inside `ff_mov_cenc_avc_write_nal_units` (`movenccenc.c:258, 272, 276`), FFmpeg writes `nal_length_size + 1` clear bytes, encrypts `nalsize - 1` bytes starting at `buf_in + 1`, and records `auxiliary_info_add_subsample(ctx, nal_length_size + 1, nalsize - 1)`.
   - While H.264 has a `1`-byte NAL unit header, **HEVC has a mandatory `2`-byte NAL unit header** (`ISO/IEC 23008-2` §7.3.1.2). ISO/IEC 23001-7 §9.5 normatively requires `BytesOfClearData` to include the length prefix **plus both bytes of the HEVC NAL header** (and requires non-VCL NAL units such as VPS, SPS, PPS, and SEI to remain entirely unencrypted in `BytesOfClearData`). `movenccenc.c` encrypts byte 2 of every HEVC NAL header (`nuh_layer_id` LSB + `nuh_temporal_id_plus1`) and encrypts in-band parameter sets, breaking compliant hardware CENC parsers/decryptors. Furthermore, `nalsize = (nalsize << 8) | *buf_in++;` (`line 262`) shifts signed `int nalsize` left by 8 on 4-byte NAL lengths—invoking pre-C23 signed-overflow UB if bit 23 is set before line `267` checks `nalsize <= 0`. *(By contrast, AV1 CENC in `ff_mov_cenc_av1_write_obus`, `movenccenc.c:287-360`, properly keeps OBU headers, Frame Headers, Tile Group Headers, and `<16`-byte trailing tile remainders clear, while VVC returns `AVERROR_PATCHWELCOME` at `movenc.c:7524`.)*
2. **Defect 2 — Partial `crypt_byte_block` Truncation in `cens` and `cbcs` Decryption (`mov.c:8953-8962, 9025-9034`):**
   - Both `cens_scheme_decrypt` (`line 8954`) and `cbcs_scheme_decrypt` (`line 9026`) execute:
     ```c
     while (rem_bytes > 0) {
         if (rem_bytes < 16 * sample->crypt_byte_block)
             break;
         av_aes_crypt(sc->cenc.aes_ctx, data, data, sample->crypt_byte_block, iv, 1);
         ...
     }
     ```
   - For the common `1:9` pattern (`crypt_byte_block == 1`), `16 * 1 == 16`, so `rem_bytes < 16` correctly skips only a trailing `<16`-byte partial AES block. However, for **any** valid ISO/IEC 23001-7 pattern with `crypt_byte_block > 1` (e.g., `5:5`, where `80` bytes are encrypted per `160`-byte stride), ISO/IEC 23001-7 §§9.6.1, 10.4.2 specifies that a trailing remainder satisfying $16 \le \text{rem\_bytes} < 16 \cdot \text{crypt\_byte\_block}$ **encrypts $\lfloor\text{rem\_bytes}/16\rfloor$ complete 16-byte AES blocks**, leaving only `rem_bytes % 16` (`< 16`) bytes clear. `mov.c` aborts the loop early and leaves up to `crypt_byte_block - 1` encrypted AES blocks ciphertext! Fix: encrypt `FFMIN(sample->crypt_byte_block, rem_bytes / 16)` blocks whenever `rem_bytes >= 16`.
3. **Defect 3 — Non-CSPRNG IV Seeding & Multi-Segment CTR Nonce Reuse (`libavutil/aes_ctr.c:64-100`, `movenccenc.c:147, 616`):**
   - `av_aes_ctr_set_random_iv` (`aes_ctr.c:64-72`) populates the 64-bit `Per_Sample_IV` from two 32-bit calls to `av_get_random_seed()`, and `av_aes_ctr_increment_iv` (`lines 95-100`) increments the big-endian 64-bit sample IV by `+1` per packet while resetting the low 64-bit block counter `counter[8..15]` to zero. In parallel/stateless segment packagers where separate worker processes initialize `movenc` with the same AES-128 key and either a colliding 64-bit random seed or a static `-encryption_iv` starting at `0`, distinct segments encrypt different plaintexts under identical `(Key, IV || BlockCounter)` pairs—yielding catastrophic AES-CTR keystream XOR recovery.

---

### 6. Clean-Room Verification & Zero-Copy Wire Architecture Implications

**Basis:** derived (synthesizing §§1–5 source invariants, execution results, and normative container specifications).

1. **Priority 1 & 2 (UB-Freedom and Panic-Freedom):**
   - Replace `matroskaenc.c`'s runtime `av_assert0` checks (`put_ebml_size_unknown`, `put_ebml_length`, `mkv_add_seekhead_entry` `MAX_SEEKHEAD_ENTRIES`) and `movenc.c`'s `av_assert0` checks (`mov_write_edts_tag` `line 4444`) with typed EBML VINT builders (`VintWidth` refinement type `1..=8`, payload `< 2^56 - 1`) and `checked_mul`/`i128` rational timestamp rescaling (`av_rescale_rnd` returns `INT64_MIN` on overflow in C, silently corrupting container timestamps if unchecked!).
   - Replace `interleave_compare_dts` (`mux.c:971-972`) `uint64_t` wraparound trick with exact `i128` cross-multiplication, and cap `si->packet_buffer` byte/packet footprint even when `AVMEDIA_TYPE_SUBTITLE` is active (`fixing mux.c:1033` unbounded queue growth when `max_interleave_delta == 0`).
2. **Priority 3 & 4 (Kleene Fixed-Point Faststart, Normative T-STD & CENC/CBCS Conformance):**
   - Implement `faststart` chunk relocation as a verified monotone lattice fixed-point loop `while (next_moov_size != cur_moov_size)` ($\le N + 1$ iterations for $N$ tracks), provably establishing `written_moov_bytes == shifted_mdat_bytes` and `forall t, c: offset(t, c) <= u32::MAX || uses_co64(t)`.
   - Implement both `cenc` (AES-128-CTR with CSPRNG or deterministic `(segment_epoch, packet_seq)` disjoint 64-bit IV partitioning) and **`cbcs` (AES-128-CBC pattern encryption)** on the muxer side—unlocking unified CMAF single-encode encrypted fMP4 delivery across DASH and HLS (`fixing hlsenc.c:1837`)—with codec-aware NAL/OBU framing that leaves all `2` bytes of HEVC/VVC NAL headers plus non-VCL parameter sets clear and handles `rem_bytes / 16` trailing pattern blocks per ISO/IEC 23001-7 §10.4.2.
   - Add an explicit optional leaky-bucket T-STD scheduler in `mpegts` muxing and optional `fsync`-before-`rename` durability in `hls`/`dash` local segment rotation.

---

## Boundaries

1. **Dedicated OSS-Fuzz muxer crash history (`not examined` as fuzz corpus, `unsupported` by upstream `tools/`):** Because `tools/Makefile` at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` builds no `target_mux_fuzzer`, muxer defects are underrepresented in public OSS-Fuzz trackers relative to `libavcodec`/`libavformat` demuxers; the `movenc.c` `faststart` overwrite and `movenccenc.c`/`mov.c` CENC/CBCS bugs documented here were established directly from source analysis and standalone execution probes.
2. **Side-channel constant-time guarantees of `libavutil/aes.c` (`known not to apply`):** `libavutil/aes.c` (invoked by `aes_ctr.c` and `mov.c` `cbcs_scheme_decrypt`) uses table-based S-box lookups in C unless hardware AES-NI / Armv8 Crypto extensions override it (note `libavutil` has minimal AES assembly compared to dedicated TLS libraries); a clean-room media CENC/CBCS engine handling high-value DRM keys must delegate AES-CTR/CBC to constant-time hardware AES-NI/VAES/Armv8-CE or verified constant-time primitives (see `fiat-crypto-hacl-evercrypt-vale-libcrux-and-verified-crypto-synthesis`).
3. **End-to-end hardware STB decoder behavior on `dts < pcr` MPEG-TS streams (`not examined` by hardware execution):** T-STD buffer underflow timing was verified against ITU-T H.222.0 §2.4.2 equations and `mpegtsenc.c:1729-1730` source logic without physical broadcast IRD hardware capture.
4. **External CDN HTTP `PUT` chunked-ingest atomicity (`unknown` without vendor spec):** Behavior of partially aborted HTTP `PUT` segment uploads depends on external origin server implementations (e.g., NGINX, Envoy, S3/GCS object stores) outside FFmpeg's repository.

---

## Evidence

### Primary Source Coordinates (`FFmpeg/FFmpeg` @ `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`)

- **Global muxer registry & build graph:** `libavformat/allformats.c:1-650` (`190` `ff_*_muxer` symbols), `libavformat/Makefile`, `configure` (`*_muxer_deps`, `*_muxer_select`), `tools/Makefile` (absence of `target_mux_fuzzer`).
- **Generic muxing & interleaving:** `libavformat/mux.c:457-550` (`avformat_write_header`, `avoid_negative_ts`), `lines 554-805` (`compute_muxer_pkt_fields`, `handle_avoid_negative_ts`), `lines 806-879` (`check_packet`), `lines 880-1080` (`ff_interleave_add_packet`, `interleave_compare_dts` modular `uint64_t` tie-breaker at `lines 971-972`, `ff_interleave_packet_per_dts`, `max_interleave_delta` and subtitle exclusion at `lines 1015-1049`), `lines 1221-1285` (`av_write_frame`, `av_interleaved_write_frame`).
- **ISOBMFF, `faststart`, CMAF & `elst`:** `libavformat/movenc.c:84-108` (`encryption_scheme`, `cmaf`, `faststart`, `frag_*` options), `lines 178-223` (`co64_required`, `mov_write_stco_tag`), `lines 4371-4479` (`mov_write_edts_tag`, `media_time = -1` empty edit vs. `-FFMIN(start_dts, 0)` priming), `lines 5924-6395` (`mov_write_trun_tag`, `mov_write_tfdt_tag`, `mov_write_traf_tag`, `mov_write_moof_tag_internal`, `mov_write_sidx_tag`, `mov_write_sidx_tags`, `mov_write_mfra_tag`), `lines 7459-7542` (H.264/HEVC/VVC/AV1 CENC dispatch), `lines 8482-8555` (`FF_MOV_FLAG_CMAF` expansion), `lines 9255-9356` (`get_moov_size`, `compute_moov_size` 2-pass unroll, `shift_data`, `mov_write_mdat_size`), `lines 9445-9504` (`mov_write_trailer`), `lines 9715-9902` (`9` `FFOutputFormat` definitions); `tools/qt-faststart.c:299-428` (`upgrade_stco_atom`, global `update_moov_atom`).
- **Matroska/WebM EBML:** `libavformat/matroskaenc.c:331-515` (`put_ebml_size_unknown`, `ebml_length_size`, `put_ebml_length`, `put_ebml_void`, `start_ebml_master`, `end_ebml_master`), `lines 787-960` (`mkv_add_seekhead_entry`, `start_ebml_master_crc32`, `end_ebml_master_crc32`, `mkv_start_seekhead`, `mkv_write_seekhead`), `lines 2685-2720` (`is_live` unknown-size `Segment`), `lines 3296-3495` (`mkv_write_trailer`, `Cues`, `SeekHead` backpatch), `lines 3719-3804` (`matroska`, `webm`, `matroska_audio`).
- **MPEG-TS, HLS & DASH:** `libavformat/mpegtsenc.c:1019-1032` (`get_pcr` `+ 11` byte offset), `lines 1094-1158` (`enable_pcr_generation_for_stream`, `select_pcr_streams`), `lines 1413-1735` (`retransmit_si_info`, `write_pcr_bits`, `mpegts_insert_pcr_only_pid`, `mpegts_write_pes`, `dts < pcr / 300` warning at `lines 1729-1730`); `libavformat/hlsenc.c:1366-1685` (`hls_rename_temp_file`, `use_temp_file` `file:`-only guard, `#EXT-X-KEY:METHOD=AES-128`), `lines 1826-1840` (`"Encrypted fmp4 not yet supported"`), `lines 3045-3255`; `libavformat/dashenc.c:209-565, 986-1225, 1835, 2125-2290`.
- **CENC/CBCS cryptography:** `libavformat/movenccenc.c:105-360` (`mov_cenc_write_encrypted`, `ff_mov_cenc_write_packet`, `ff_mov_cenc_avc_write_nal_units` `nal_length_size + 1` at `lines 258, 272, 276` & signed shift at `line 262`, `write_tiles` AV1 OBU clear/16B alignment), `lines 495-645` (`senc`, `saio`, `saiz`, `ff_mov_cenc_init`); `libavformat/mov.c:8838-9061` (`cbc1_scheme_decrypt`, `cens_scheme_decrypt` `line 8954`, `cbcs_scheme_decrypt` `lines 9022-9034`, `cenc_decrypt`); `libavutil/aes_ctr.c:46-135` (`av_aes_ctr_set_random_iv` at `lines 64-72`, `av_aes_ctr_increment_iv`, `av_aes_ctr_crypt`).

### Executed Standalone Verification Probe (`2026-11-20`, Linux x86_64, `gcc -O2 -Wall -Wextra -Werror -fsanitize=undefined`)

```c
/* probe_muxers.c — Reproduces movenc.c:9286-9309 multi-stream faststart stco->co64
 * 40,000-byte mdat overwrite vs. Kleene fixed-point iteration, plus mux.c:971-972
 * modular uint64 tie-breaking equivalence at 24-hour timestamps. */
#include <stdint.h>
#include <stdio.h>
#include <limits.h>

typedef struct {
    uint64_t last_chunk_pos;
    uint32_t chunk_count;
    int64_t  data_offset;
} SimTrack;

static int co64_required(const SimTrack *t) {
    return (t->last_chunk_pos + (uint64_t)t->data_offset) > UINT32_MAX;
}

static int get_moov_size(const SimTrack *tracks, int n, int base_moov_overhead) {
    int sz = base_moov_overhead;
    for (int i = 0; i < n; i++)
        sz += 16 + (int)tracks[i].chunk_count * (co64_required(&tracks[i]) ? 8 : 4);
    return sz;
}

static int ffmpeg_compute_moov_size(SimTrack *tracks, int n, int base_overhead) {
    int moov_size = get_moov_size(tracks, n, base_overhead);
    for (int i = 0; i < n; i++) tracks[i].data_offset += moov_size;
    int moov_size2 = get_moov_size(tracks, n, base_overhead);
    if (moov_size2 != moov_size)
        for (int i = 0; i < n; i++) tracks[i].data_offset += moov_size2 - moov_size;
    return moov_size2;
}

static int kleene_compute_moov_size(SimTrack *tracks, int n, int base_overhead, int *iters) {
    int prev = 0, cur = get_moov_size(tracks, n, base_overhead);
    *iters = 1;
    while (cur != prev) {
        int delta = cur - prev;
        for (int i = 0; i < n; i++) tracks[i].data_offset += delta;
        prev = cur;
        cur = get_moov_size(tracks, n, base_overhead);
        (*iters)++;
    }
    return cur;
}

int main(void) {
    SimTrack t_ff[2] = {
        { .last_chunk_pos = (uint64_t)UINT32_MAX - 10000ULL,  .chunk_count = 10000, .data_offset = 0 },
        { .last_chunk_pos = (uint64_t)UINT32_MAX - 110000ULL, .chunk_count = 10000, .data_offset = 0 }
    };
    SimTrack t_fp[2] = { t_ff[0], t_ff[1] };
    int base_overhead = 9968;

    int shifted_ff = ffmpeg_compute_moov_size(t_ff, 2, base_overhead);
    int actual_written_ff = get_moov_size(t_ff, 2, base_overhead);

    int iters = 0;
    int shifted_fp = kleene_compute_moov_size(t_fp, 2, base_overhead, &iters);
    int actual_written_fp = get_moov_size(t_fp, 2, base_overhead);

    printf("FASTSTART_FFMPEG_2PASS: shifted=%d written=%d mdat_overwrite_bytes=%d\n",
           shifted_ff, actual_written_ff, actual_written_ff - shifted_ff);
    printf("FASTSTART_KLEENE_FIXPT: shifted=%d written=%d mdat_overwrite_bytes=%d iters=%d\n",
           shifted_fp, actual_written_fp, actual_written_fp - shifted_fp, iters);

    const int64_t AV_TB = 1000000;
    int64_t num1 = 1, den1 = 90000, preload1 = 0;
    int64_t num2 = 1, den2 = 48000, preload2 = 500000;
    int mismatches = 0, wraps = 0;
    for (int step = -50; step <= 50; step++) {
        int64_t dts1 = 86400LL * 90000 + step;
        int64_t dts2 = 86400LL * 48000 + 24000;
        if ((dts1 * AV_TB) / den1 - preload1 == (dts2 * AV_TB) / den2 - preload2) {
            __int128 exact1 = ((__int128)dts1 * num1 * AV_TB - (__int128)preload1 * den1) * den2;
            __int128 exact2 = ((__int128)dts2 * num2 * AV_TB - (__int128)preload2 * den2) * den1;
            if (exact1 > INT64_MAX) wraps++;
            uint64_t u1 = ((uint64_t)dts1 * num1 * AV_TB - (uint64_t)preload1 * den1) * den2;
            uint64_t u2 = ((uint64_t)dts2 * num2 * AV_TB - (uint64_t)preload2 * den2) * den1;
            int64_t mod_diff = (int64_t)(u1 - u2);
            int cmp_mod = (0 > mod_diff) - (0 < mod_diff);
            int cmp_128 = (exact2 > exact1) - (exact2 < exact1);
            if (cmp_mod != cmp_128) mismatches++;
        }
    }
    printf("INTERLEAVE_MOD64_PROBE: tied_us_cases_wrapped=%d mismatches_vs_i128=%d\n",
           wraps, mismatches);
    return 0;
}
```

Observed output (`exit 0`, zero UBSan diagnostics):
```text
FASTSTART_FFMPEG_2PASS: shifted=130000 written=170000 mdat_overwrite_bytes=40000
FASTSTART_KLEENE_FIXPT: shifted=170000 written=170000 mdat_overwrite_bytes=0 iters=4
INTERLEAVE_MOD64_PROBE: tied_us_cases_wrapped=1 mismatches_vs_i128=0
```

---

## Revalidation

To revalidate these findings against a newer `FFmpeg/FFmpeg` revision `<NEW_SHA>`:
1. **Muxer census & fuzz-harness check (<5s):** Fetch `libavformat/allformats.c` and `tools/Makefile` at `<NEW_SHA>`, count `extern const FFOutputFormat ff_*_muxer;`, and check whether any `target_mux*_fuzzer` rule has been added to `tools/Makefile`.
2. **Faststart fixed-point & CENC/CBCS defect checks (<5s):**
   - Inspect `compute_moov_size` in `libavformat/movenc.c` to check whether the 2-pass `moov_size` / `moov_size2` unroll has been replaced by a `while` fixed-point loop, and re-run `probe_muxers.c`.
   - Inspect `libavformat/movenc.c` around `encryption_scheme` (whether `cbcs`, `cens`, or `cbc1` were added alongside `cenc-aes-ctr`), `AV_CODEC_ID_HEVC` CENC dispatch (whether HEVC still calls 1-byte-header `ff_mov_cenc_avc_write_nal_units`), `libavformat/hlsenc.c` around `"Encrypted fmp4 not yet supported"`, and `libavformat/mov.c` inside `cens_scheme_decrypt` / `cbcs_scheme_decrypt` (`rem_bytes < 16 * sample->crypt_byte_block`).
