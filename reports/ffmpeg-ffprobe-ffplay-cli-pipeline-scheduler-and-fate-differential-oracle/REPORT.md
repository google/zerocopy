# FFmpeg fftools Pipeline Scheduler, ffprobe/ffplay Architectures, and FATE Differential Equivalence Oracles

## Summary

Inspecting `FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) across `fftools/` and `tests/` establishes five load-bearing architectural findings for building CLI-compatible Rust multimedia tools and an automated differential oracle (`Basis: source + normative + execution`):

1. **The multithreaded transcode scheduler (`fftools/ffmpeg_sched.c`) isolates component threads around centralized DTS backpressure and deadlock-avoidance.** Every demuxer, decoder, filtergraph, encoder, and muxer runs on an independent OS thread communicating strictly through bounded `ThreadQueue` FIFOs (`DEFAULT_PACKET_THREAD_QUEUE_SIZE = 2`, `DEFAULT_FRAME_THREAD_QUEUE_SIZE = 2`, `fftools/ffmpeg_sched.h:257,262`). A single mutex-protected `schedule_update_locked()` pass (`ffmpeg_sched.c:1448-1539`) computes `trailing_dts(sch)` across active muxer streams, chokes demuxers/sources ahead by `>= SCHEDULE_TOLERANCE` (`100 ms`), and recursively walks `unchoke_downstream()` across diamond filtergraphs so stalled multi-input graphs do not deadlock. Multi-stream duration skew in encoders/muxers is absorbed by `SyncQueue` (`fftools/sync_queue.c`) with synthetic `overflow_heartbeat` timestamps when a stream lags past `buf_size_us`.
2. **Structured inspection (`ffprobe.c`) separates domain extraction from formatting via `AVTextFormatContext`.** `fftools/ffprobe.c` constructs a static section hierarchy (`sections[]`, `SECTION_ID_*`) and emits records into `fftools/textformat/avtextformat.{h,c}` backends (`default`, `compact`/`csv`, `flat`, `ini`, `json`, `xml`, `mermaid`). XML schema compliance against `doc/ffprobe.xsd` requires `-noprivate -of xml=q=1:x=1` (`tests/fate/ffprobe.mak:20`), rejecting `-unit` and `-prefix` (`tf_xml.c:57-70`) and filtering XML-invalid control characters (`ffprobe.c:3710-3711`).
3. **`ffplay.c` A/V synchronization is a compact three-clock control law entangled with SDL wall-clock and threading state.** Three `Clock` structs (`audclk`, `vidclk`, `extclk`) track `pts_drift` tagged by a seek `serial` (`fftools/ffplay.c:142-150,1597-1643`). Video pacing (`compute_target_delay`, `L1748-1776`) applies an asymmetric `[0.04s, 0.10s]` deadband, and non-master audio (`synchronize_audio`, `L2559-2588`) smooths drift via a 20-sample EWMA clamped to `+/-10%` sample adjustment. Extracting these equations into a pure virtual-time Rust state machine makes A/V sync deterministically testable without audio hardware or SDL.
4. **FATE's bit-exact and approximate oracles contain non-obvious arithmetic definitions that a differential harness must match verbatim.** `libavformat/crcenc.c:45,53` prints `CRC=0x%08x` using **Adler-32** initialized at `1` (`av_adler32_update`), *not* IEEE CRC-32; `tests/tiny_psnr.c` computes integer `int_sqrt`/fixed-point `log16` with `999.99` as the exact-match sentinel and scales `f32` differences by `2^24`; `tests/tiny_ssim.c` implements a fast overlapped `4x4`-sum approximation of Wang et al. (`10.1109/TIP.2003.819861`) weighted `4:1:1` across Y:U:V (`420p`) with a documented signed 32-bit overflow hazard above 9-bit depth; and vendored `libcheckasm` checks float similarity via `checkasm_float_near_ulp` (which rejects opposite-sign tiny values near zero while accepting identical-sign NaNs within `max_ulp`).
5. **A five-tier differential oracle prevents false failures on legitimate non-bit-exact paths while guaranteeing bit-exact regression coverage.** Compiling and executing verbatim `tiny_psnr.c` and `tiny_ssim.c` from `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` demonstrates how a `50`-LSB single-sample spike yields lower `stddev` (`0.78`) than ubiquitous `+/-1` LSB dither (`1.00`) while spiking `MAXDIFF` (`50` vs `1`), justifying separate `oneoff`, `stddev`, `framemd5`, rate-distortion, and `checkasm` verification tiers (`Basis: execution`).

## Applicability

This technical reference applies to `FFmpeg/FFmpeg` at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` covering:
- Command-line pipeline execution and scheduling (`fftools/ffmpeg_sched.{h,c}`, `fftools/sync_queue.{h,c}`, `fftools/thread_queue.{h,c}`, `fftools/ffmpeg_filter.c`);
- Structured media probing (`fftools/ffprobe.c`, `fftools/textformat/*.{h,c}`, `doc/ffprobe.xsd`);
- Interactive playback synchronization (`fftools/ffplay.c`);
- Regression and kernel validation infrastructure (`tests/Makefile`, `tests/fate-run.sh`, `tests/fate/*.mak`, `tests/tiny_psnr.c`, `tests/tiny_ssim.c`, `tests/audiomatch.c`, `tests/refcmp-metadata.awk`, `libavformat/hashenc.c`, `libavformat/crcenc.c`, `tests/checkasm/ext/`), including the SSIM algorithm of Wang et al. (`10.1109/TIP.2003.819861`) as approximated in `tests/tiny_ssim.c`.

Related corpus packages cover general differential oracle bisimulation (`reference-model-bisimulation-executable-semantics-and-differential-oracles`), IEEE-754 floating-point interval/NaN refinement (`ieee754-softfloat-dyadic-interval-gappa-certificates-and-nan-choice-refinement`), SIMD floating-point reassociation (`ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`), and bitstream security/codec DSP verification (`entropy-coded-media-bitstreams-video-codec-security-and-simd-decoders`, `webrtc-neteq-jitter-buffers-opus-silk-celt-hybrids-and-flac-lpc-overflows`).

## Findings

### 1. Multithreaded Transcode Pipeline Scheduler (`fftools/ffmpeg_sched.c`, `sync_queue.c`, `thread_queue.c`)

`Basis: source`

Upstream `ffmpeg` models transcoding as an acyclic directed graph (`Scheduler` in `fftools/ffmpeg_sched.h:33-86` and `fftools/ffmpeg_sched.c:283-318`) connecting six component roles—demuxers (`SCH_NODE_TYPE_DEMUX`), decoders (`DEC`), filtergraph inputs/outputs (`FILTER_IN`/`FILTER_OUT`), encoders (`ENC`), muxers (`MUX`), and inter-stream sync queues (`SQ_ENC`/`SQ_FRAME`). Each component runs on an isolated worker thread and communicates exclusively through the scheduler rather than directly with peer nodes (`ffmpeg_sched.h:81-85`).

#### Startup Topology Checks & Bounded Queues
- **Static cycle detection (`ffmpeg_sched.c:1568-1649,1767-1777`):** Before spawning worker threads, `sch_start()` runs `start_prepare()` -> `check_acyclic()`, performing an iterative depth-first walk (`CYCLE_NODE_NEW`, `CYCLE_NODE_STARTED`, `CYCLE_NODE_DONE`) across filtergraphs upstream via `src_filtergraph()`. Any cycle returns `AVERROR(EINVAL)` (`"Transcoding graph has a cycle"`), and unconnected filter inputs/outputs fail validation (`L1741-1756`).
- **Bounded inter-thread queues (`fftools/thread_queue.c`, `ffmpeg_sched.h:257,262`):** Edges enter `ThreadQueue` instances sized by default to `DEFAULT_PACKET_THREAD_QUEUE_SIZE = 2` and `DEFAULT_FRAME_THREAD_QUEUE_SIZE = 2` (up to `thread_queue_size` on muxers). `ThreadQueue` pairs an `AVFifo` ring buffer and object pool (`ObjPool`) under a `pthread_mutex_t`/`pthread_cond_t` monitor, supporting explicit `tq_choke()` backpressure (`ffmpeg_sched.c:1418-1446`).
- **Pre-muxing buffering & SDP barrier (`ffmpeg_sched.c:1180-1260`):** Before all streams in a muxer are initialized (`sch_mux_stream_ready`), packets accumulate in per-stream `PreMuxQueue` FIFOs capped by `data_threshold` and `max_packets` (`sch_mux_stream_buffering`). If SDP generation is enabled (`sdp_filename` or `sdp_auto`), `mux_init` (`L1210-1244`) holds *all* muxer threads until every muxer header is written and the SDP is emitted.

#### DTS-Driven Choking and Diamond-Graph Deadlock Avoidance
Because demuxing an interleaved file or reading independent inputs can advance one output stream arbitrarily far ahead of another—triggering unbounded memory growth or deadlock across shared demuxer/filtergraph splits—`schedule_update_locked(Scheduler *sch)` (`ffmpeg_sched.c:1448-1539`) implements a global pacing invariant under `sch->schedule_lock`:
1. `trailing_dts(sch)` (`L448-468`) scans every unfinished `SchMuxStream` across all muxers. If any active stream still has `last_dts_paced == AV_NOPTS_VALUE`, it returns `AV_NOPTS_VALUE`; otherwise it returns the minimum `last_dts_paced`.
2. All `demux[i].waiter` and `filters[i].waiter` instances reset `choked_next = 1` (`L1472-1473`).
3. For each unfinished muxer stream `ms` either still at `AV_NOPTS_VALUE` (when `dts == AV_NOPTS_VALUE`) or within `ms->last_dts_paced - dts < SCHEDULE_TOLERANCE` (`SCHEDULE_TOLERANCE = 100 * 1000` microseconds = `100 ms`, `L45,1486-1489`), `unchoke_for_stream(sch, ms->src, UNCHOKE_ALL)` unchokes its upstream demuxer or self-timed `lavfi` filtergraph (`fg->best_input == fg->nb_inputs`, `L1404-1408`).
4. **Diamond deadlock prevention (`L1342-1375,1389-1391,1497-1507`):** When unchoking a demuxer, `unchoke_for_stream` calls `unchoke_downstream` on *every* output stream of that demuxer; if a sibling stream feeds a multi-input `SchFilterGraph` blocked waiting for `fg->inputs[fg->best_input]`, `unchoke_downstream` recursively unchokes `fg->inputs[fg->best_input].src` (`L1368`). Additionally, lines `1499-1507` unchoke sources feeding filter inputs where `receive_finished && !send_finished` so upstream producers observe downstream EOF, and `UNCHOKE_ONCE` (`L1510-1524`) guarantees at least one non-exited source remains unchoked.

#### Multi-Stream Frame/Packet Alignment (`fftools/sync_queue.c`)
`SyncQueue` (`sync_queue.c:72-145,232-340`) enforces timestamp alignment across multiple streams (`SYNC_QUEUE_FRAMES` or `SYNC_QUEUE_PACKETS`) without needing OS thread choking:
- Each stream records `head_ts` (largest `pts + duration` or rescaled audio sample end). `head_stream` is the limiting stream with the smallest `head_ts` (`av_compare_ts`).
- Any finished stream records `head_finished_stream`; once another stream advances past `head_finished_stream` (`L255-259`), `finish_stream()` terminates it—implementing `-shortest` deterministically in timestamp space.
- If the gap between a stream's `head_ts` and its FIFO tail reaches `sq->buf_size_us` (`L314-317`), `overflow_heartbeat()` (`L272-340`) advances lagging streams' `head_ts` to `tail_ts + 1`, releasing queued frames/packets rather than exhausting memory.

**Clean Rust rewrite implication (`Basis: derived`):**
- *Accidental C complexity:* Sharing raw `pthread_mutex_t` / `atomic_int choked` waiters, manual `AVFifo` void-pointer containers, and manual `av_freep` cleanup across `ffmpeg_sched.c` is C heritage and causes subtle lock-ordering and initialization bugs.
- *Essential algorithmic core:* Bounded queues (`capacity = 2` default), cycle rejection, `100 ms` DTS pacing tolerance (`trailing_dts`), downstream multi-input filter unchoking, and `SyncQueue` `buf_size_us` overflow heartbeats are fundamental physical constraints of bounded-memory multi-rate media graphs. In Rust, replacing `ThreadQueue` + `SchWaiter` with bounded typed `sync_channel` / async actor mailboxes driven by an explicit `SchedulerState` actor (holding pure timestamp tables and emitting unchoke tokens) eliminates data races (`UB-freedom`) and panic paths while preserving exact scheduling progress guarantees.
- *Determinism caveat:* `sch_filter_receive` (`L2581-2630`) transitions between exact input polling (`*in_idx < fg->nb_inputs`) and non-blocking multi-input polling (`*in_idx == fg->nb_inputs`, `THREAD_QUEUE_FLAG_NO_BLOCK`), meaning arrival timing across *independent* inputs can affect which frame enters `fg->queue` first unless the filtergraph explicitly selects `best_input` deterministically by PTS!

### 2. Filtergraph Lifecycle and Reconfiguration (`fftools/ffmpeg_filter.c`)

`Basis: source`

`fftools/ffmpeg_filter.c` wraps `libavfilter` inside `FilterGraphThread` (`fgt`) and `InputFilterPriv` / `OutputFilterPriv`:
- **Dynamic reconfiguration (`L3211,3244-3310`):** When an input `AVFrame` changes format, resolution (`VIDEO_CHANGED`), color matrix (`MATRIX_CHANGED`), channel layout/rate (`AUDIO_CHANGED`), or downmix mode (`DOWNMIX_CHANGED`), `ffmpeg_filter.c` detects the mismatch against the configured link. Unless `IFILTER_FLAG_DROPCHANGED` (`L3293`) is active (which drops mismatched frames with a warning), the filtergraph flushes, drains, and executes `configure_filtergraph()`.
- **Timestamp-driven input selection (`L2501-2519`):** Multi-input filtergraphs determine `best_input` via `choose_out_time` / `av_buffersink_get_frame_flags` readiness and request that exact stream index from `sch_filter_receive` (`ffmpeg_sched.c:2596-2603`).
- **`sub2video` canvas heartbeat (`L290-398,1960-1968,3096-3165`):** Bitmap subtitles are rendered onto a pre-configured `AVFrame` canvas (`sub2video.frame`); video frames arriving on paired video inputs trigger `sub2video_heartbeat()` (`L3096`), emitting blank/updated subtitle frames whenever `pts2 >= sub2video.end_pts` or `initialize == 1` so `overlay` filters never stall waiting on sparse subtitle streams.
- **Per-frame option reinitialization (`L259-260,845-945,1177-1181`):** `OutputFilterPriv` parses queued `reinit_opts_fifo` (`ReinitOpts` keyed by PTS) to apply runtime filter commands.

### 3. `ffprobe.c` Structured Formatting (`fftools/textformat/`, `doc/ffprobe.xsd`)

`Basis: source`

At `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, `ffprobe` delegates all serialization to the standalone `fftools/textformat/` subsystem (`avtextformat.h`, `avtextformat.c`, `avtextwriters.h`, `tf_*.c`, `tw_*.c`):
- **Schema-driven section tree (`fftools/ffprobe.c:220-360`, `avtextformat.h:45-140`):** Every output unit (`packets`, `frames`, `streams`, `format`, `chapters`, `programs`, `stream_groups`, `program_version`, `library_versions`, `error`) is defined in `sections[]` with structural flags:
  - `AV_TEXTFORMAT_SECTION_FLAG_IS_WRAPPER` (`root`),
  - `AV_TEXTFORMAT_SECTION_FLAG_IS_ARRAY` (`streams`, `packets`, `frames`, `side_data_list`),
  - `AV_TEXTFORMAT_SECTION_FLAG_HAS_VARIABLE_FIELDS` (`tags`, `disposition`, side-data entries),
  - `AV_TEXTFORMAT_SECTION_FLAG_HAS_TYPE` + `get_type` (`packets_and_frames` element typing).
- **Formatter semantics & escaping traps:**
  - **JSON (`tf_json.c:61-155`):** `json_escape_str` escapes `"`, `\`, `\b`, `\f`, `\n`, `\r`, `\t`, and any unsigned byte `< 32` as `\u00%02x` (`L77-78`). It uses a flat 4-space indentation (`compact` / `c=1` collapses nested objects onto single lines), and emits `"type": "..."` inside array elements when `parent_section->flags & AV_TEXTFORMAT_SECTION_FLAG_NUMBERING_BY_TYPE` (`L118`).
  - **XML (`tf_xml.c:32-212`, `doc/ffprobe.xsd`, `ffprobe.c:3710-3711`):** `xml_init` enforces that `xsd_strict` (`-of xml=q=1:x=1`) sets `fully_qualified = 1` (`ffprobe:` namespace + `xsi:schemaLocation`) and errors out (`AVERROR(EINVAL)`) if `-unit` or `-prefix` are set (`tf_xml.c:57-69`). `ffprobe.c:3710-3711` enables `AV_UTF8_FLAG_EXCLUDE_XML_INVALID_CONTROL_CODES` exclusively for the XML formatter so invalid XML 1.0 control bytes in container tags are sanitized rather than failing `xmllint --schema doc/ffprobe.xsd`.
  - **Compact / CSV (`tf_compact.c:39-100`):** `c_escape_str` backslash-escapes control characters and `item_sep` (`|`), whereas `csv_escape_str` implements RFC 4180 quoting (`""` doubling) whenever any byte in `{sep, '"', '\n', '\r'}` appears (`L62-79`).
- **Differential normalization rule (`Basis: derived`):** Upstream `ffprobe` `-show_program_version` and `-show_library_versions` embed FFmpeg build/compiler strings and `LIBAV*_VERSION_INT` (`ffprobe.c:3715-3718`), while `format.filename` echoes paths unless `-print_filename` is pinned (as done in `tests/fate/ffprobe.mak:11`). A differential oracle between a Rust probe tool and `ffprobe` must run with `-bitexact -noprivate` (or canonicalize JSON by stripping `program_version`/`library_versions` and normalizing non-deterministic codec-tag strings where explicitly exempted).

### 4. `ffplay.c` A/V Sync Clock Control Law

`Basis: source`

`fftools/ffplay.c` coordinates live decoding and SDL output via three `Clock` structures (`audclk`, `vidclk`, `extclk`, defined at `L142-150`):
- **Clock representation & serial fencing (`L1597-1643`):**
  - `get_clock(c)` checks `if (*c->queue_serial != c->serial) return NAN;` (`L1599-1600`) to immediately invalidate stale clocks across seeks. Otherwise, when unpaused, `clock(t) = c->pts_drift + t - (t - c->last_updated) * (1.0 - c->speed)` (`L1605`), where `c->pts_drift = pts - t_update` (`L1613`).
  - `get_master_sync_type` (`L1645-1658`) defaults to `AV_SYNC_AUDIO_MASTER`, falling back to `AV_SYNC_EXTERNAL_CLOCK` if no audio stream exists (or `AV_SYNC_AUDIO_MASTER` if `VIDEO_MASTER` lacks a video stream). `sync_clock_to_slave` (`L1637-1643`) snaps `extclk` if `|clock - slave_clock| > AV_NOSYNC_THRESHOLD` (`10.0` seconds, `L89`).
- **Video pacing (`compute_target_delay`, `L83-89,1748-1776`):** When video is slaved (`!= AV_SYNC_VIDEO_MASTER`), `diff = get_clock(&is->vidclk) - get_master_clock(is)`:
  - Deadband threshold: `sync_threshold = max(0.04, min(0.1, delay))` (`AV_SYNC_THRESHOLD_MIN = 0.04`, `AV_SYNC_THRESHOLD_MAX = 0.1`, `L1761`).
  - If `|diff| < max_frame_duration`:
    - `diff <= -sync_threshold` (video behind): `delay = max(0.0, delay + diff)` (`L1763-1764`).
    - `diff >= sync_threshold && delay > 0.1` (`AV_SYNC_FRAMEDUP_THRESHOLD`): `delay = delay + diff` (`L1765-1766`).
    - `diff >= sync_threshold` (normal frame rates): `delay = 2 * delay` (repeat previous frame once, `L1767-1768`).
- **Audio drift compensation (`synchronize_audio`, `L92,100,2559-2588`):** When audio is slaved to video or external clock, `synchronize_audio` accumulates `audio_diff_cum = diff + coef * audio_diff_cum` across `AUDIO_DIFF_AVG_NB = 20` callbacks; once warmed up, if `|avg_diff| >= audio_diff_threshold`, it adjusts `wanted_nb_samples = nb_samples + (int)(diff * freq)` clamped to `[0.9 * nb_samples, 1.1 * nb_samples]` (`SAMPLE_CORRECTION_PERCENT_MAX = 10`).

**Clean Rust rewrite implication (`Basis: derived`):** Direct wall-clock SDL testing of `ffplay.c` is inherently timing-sensitive and host-dependent. Separating `Clock` + `compute_target_delay` + `synchronize_audio` + frame-drop logic into a pure, no-SDL Rust `SyncController` trait parameterized by an explicit monotonic `now_us: i64` (or deterministic `f64` tick) enables exhaustive property testing and 1:1 trace comparison against extracted traces from `ffplay.c`'s equations.

### 5. `FATE` Regression Suite & `checkasm` Oracle Anatomy

`Basis: source + normative + execution`

`tests/Makefile`, `tests/fate-run.sh`, and `tests/fate/*.mak` orchestrate FFmpeg's regression harness, while `tests/checkasm/` validates SIMD assembly kernels.

#### `FATE` Modes, Determinism Flags, and the Adler-32 `crc` Trap
`tests/fate-run.sh:15-24,405-408,805-816` enforces reproducibility via `LC_ALL=C` (`L3`), deterministic options `COMMON_OPTS="-flags +bitexact -idct simple -sws_flags +accurate_rnd+bitexact -fflags +bitexact"`, `ENC_OPTS="$COMMON_OPTS -threads 1 -dct fastint"`, and `DEC_OPTS="$COMMON_OPTS -threads $threads"` (`L406-408`). Note that encoders force `-threads 1` and `-dct fastint` specifically to eliminate multi-threaded VBV/rate-control and DCT nondeterminism! Output verification dispatches on `$cmp`:

| FATE `CMP` / Tool | Source Location | Exact Semantics / Edge Case | Verification Tier |
| :--- | :--- | :--- | :--- |
| `diff` / `rawdiff` / `oneline` | `tests/fate-run.sh:93-95,807-808,811` | `diff -u -b` (ignores whitespace changes in `diff`) or exact byte diff (`rawdiff`). | Bit-exact / CLI text |
| `framemd5` / `framehash` | `libavformat/hashenc.c:119-143,317-411`, `fate-run.sh:221-223` | Emits `#tb`, `#media_type`, `#codec_id`, `#dimensions`, `#sar`, `#extradata`, then per packet/frame `stream_index, dts, pts, duration, size, hash` + v2 side-data hashes (`S=n, size, hex`). Big-endian `AV_PKT_DATA_PALETTE` normalized to LE (`hashenc.c:128-132`). | Bit-exact frame+timestamp+side-data |
| `crc` | `libavformat/crcenc.c:32-67`, `fate-run.sh:225-227` | Computes **Adler-32** via `av_adler32_update(crcval, pkt->data, pkt->size)` initialized to `1`, formatted as `CRC=0x%08x\n` (`AVFMT_NOTIMESTAMPS`). **Not** IEEE 802.3 CRC-32! | Bit-exact raw payload (timestamp-blind) |
| `oneoff` (`tiny_psnr`) | `tests/fate-run.sh:66-87`, `tests/tiny_psnr.c:133-263` | Parses `MAXDIFF` and byte counts; `compare()` fails if `\|val - cmp_target\| > fuzz` (`fuzz=1` default) or `\|size1 - size2\| > size_tolerance`. | Bounded per-sample integer/float error |
| `stddev` (`tiny_psnr`) | `tests/fate-run.sh:66-83,89-91`, `tests/tiny_psnr.c:228-260` | Parses `stddev` (RMSE); `compare()` checks `\|stddev - cmp_target\| <= fuzz` symmetrically around `cmp_target` (e.g., `fate-acodec-dca2` sets `CMP_TARGET = 534`, `fate-acodec-ra144` sets `CMP_TARGET = 4777` in `tests/fate/acodec.mak:132-159`). | Bounded aggregate RMSE |
| `audiomatch` | `tests/audiomatch.c:37-123`, `fate-run.sh:709-719` | Cross-correlates `s16le` signals across `pos in [-16384, +16384]`; requires `\|1.0 - bestc/sigamp\| <= 0.161`. Tolerates encoder/decoder priming delay. | Delay-tolerant perceptual audio |
| `metadata` (`refcmp-metadata.awk`) | `tests/refcmp-metadata.awk:1-60` | Line-by-line `key=value` comparison; numeric values allow relative error `\|val/ref_val - 1\| <= fuzz` (`fuzz=0.1` default). | Filter metadata / float stats |
| `null` | `tests/fate-run.sh:785-787,813` | Relies solely on process exit code `0` (used by `fate-checkasm-*` and `fate-api-*`). | Self-checking harness |

#### `tiny_psnr.c` and `tiny_ssim.c` Arithmetic & Executed Probe Findings
Inspecting and running verbatim `tests/tiny_psnr.c` and `tests/tiny_ssim.c` (compiled with `gcc 15.2.0 -O2 -lm`) surfaces critical oracle details (`Basis: source + execution`):
- **`tiny_psnr.c` integer vs. float paths (`L180-260`):**
  - For `u8`/`s16`: skips RIFF/WAVE headers (`L154-166`), computes exact integer `sse`, `int_sqrt` RMSE scaled by `F = 100` (`stddev`), fixed-point `log16` PSNR (`1000 * F - 1 = 999.99` when `sse == 0`, `L234`), and `MAXDIFF`.
  - For `f32`/`f64`: accumulates `double sse_d`, scales both `dev` and `maxdist` by `scale = (1ULL << 24)` (`16,777,216`) for `f32` or `(1ULL << 32)` for `f64` (`L247,255,258`), and prints `PSNR:inf` when `sse_d == 0`. Note `maxdist` truncates `maxdist_d * scale` to `uint64_t` (`L255`), so sub-`0.5e-7` `f32` differences can report `MAXDIFF: 0` while `stddev` remains non-zero (`> 0.00`).
- **Verbatim execution (`tiny_psnr`, `Basis: execution`):**
  - Exact `s16` (`4096` samples, `8192` bytes): `stddev:    0.00 PSNR:999.99 MAXDIFF:    0 bytes:     8192/     8192`
  - `s16` `+/-1` LSB dither: `stddev:    1.00 PSNR: 96.33 MAXDIFF:    1 bytes:     8192/     8192`
  - `s16` single `50`-LSB spike: `stddev:    0.78 PSNR: 98.47 MAXDIFF:   50 bytes:     8192/     8192` (demonstrating why `stddev` alone masks single-sample faults while `MAXDIFF` catches them!)
  - `f32` `+/-1e-6` perturbation: `stddev:     13.69 PSNR:1391.53 MAXDIFF:        17 bytes:    16384/    16384` (verifying the `2^24` scaling factor: `1e-6 * 2^24 ≈ 16.78`).
- **`tiny_ssim.c` fast SSIM & 10-bit overflow ceiling (`L26-176`):**
  - Approximates Wang et al.'s `11x11` Gaussian-weighted SSIM (`doi: 10.1109/TIP.2003.819861`) using overlapped `8x8` window sums built from `4x4x2` block accumulators (`ssim_4x4x2_core`, `L46-73`) and `ssim_end1` (`L75-97`).
  - For `BIT_DEPTH <= 9`, `ssim_end1` computes `vars` and `covar` in signed `int`; a source comment (`L77-79`) warns that 10-bit inputs reach `ss * 64 = 4,286,582,784`, overflowing signed 32-bit `int` (requiring `#if BIT_DEPTH > 9 typedef float type;`).
  - `print_results` (`L162-175`) reports `4:2:0` overall `PSNR` across `1.5 * w * h` pixels and weights `All` SSIM as `(4*Y + U + V) / 6`.
- **Verbatim execution (`tiny_ssim` on 3 frames of `64x64` YUV420p, `Basis: execution`):**
  - Exact: `Total 3 frames | PSNR Y:inf  U:inf  V:inf  All:inf | SSIM Y:1.00000 U:1.00000 V:1.00000 All:1.00000 (inf)`
  - `+/-1` LSB on Y: `Total 3 frames | PSNR Y:48.131  U:inf  V:inf  All:49.892 | SSIM Y:0.99570 U:1.00000 V:1.00000 All:0.99713 (25.42721)`
  - `+/-4` `4x4` checkerboard on Y: `Total 3 frames | PSNR Y:36.090  U:inf  V:inf  All:37.851 | SSIM Y:0.93610 U:1.00000 V:1.00000 All:0.95740 (13.70586)`

#### `checkasm` Kernel Harness (`tests/checkasm/ext/`)
`tests/checkasm/` embeds `libcheckasm` (`ext/include/checkasm/{checkasm.h,test.h,utils.h}`, `ext/src/{checkasm.c,function.c,signal.c,stackguard.c,utils.c}`) to verify SIMD kernels against C reference functions across every active CPU feature flag bitmask:
1. **Deterministic PRNG & regression isolation (`utils.h:55-58`, `checkasm.c:598`):** Calls `checkasm_srand(cfg.seed)` before each test function so different ISA variants receive identical randomized inputs.
2. **ABI & memory safety traps (`test.h:272-279`, `signal.c:107-175`, `stackguard.c:41-76`):** `checkasm_call_checked()` enables signal handlers (`SIGILL`, `SIGFPE`, `SIGBUS`, `SIGSEGV`) recovering via `siglongjmp`, pushes/pops stack guard cookies (`"stack clobbered"`), and verifies callee-saved registers and buffer padding redzones (`checkasm_check2d_padded`).
3. **Float tolerance corner case (`tests/checkasm/ext/src/utils.c:662-717`):** `checkasm_float_near_ulp(a, b, max_ulp)` rejects any `a, b` with opposing sign bits unless `a == b` (`-0.0 == +0.0`, `L669-672`), meaning `-1e-38` vs `+1e-38` fails even when `max_ulp = 4` unless callers invoke `float_near_abs_eps_ulp(a, b, eps, max_ulp)` (`L705-709`, as in `tests/checkasm/float_dsp.c:46`). Conversely, two quiet NaNs with identical sign bits and payloads within `max_ulp` pass `float_near_ulp` (`L674`) because `llabs(x.i - y.i) <= max_ulp`, whereas `float_near_abs_eps` (`fabsf(a - b) < eps`, `L692`) returns `0` on NaN.

### 6. Five-Tier Differential Behavioral Equivalence Oracle Architecture

`Basis: derived`

Mapping FATE's mechanisms onto a clean-room Rust rewrite across the four-level verification priority hierarchy (1. UB-freedom, 2. Panic-freedom, 3. Behavioral equivalence & SIMD-vs-scalar equivalence, 4. Functional spec conformance) yields five distinct differential oracle tiers:

| Oracle Tier | Scope (Codecs, Containers, CLI, Kernels) | Comparison Method vs. Upstream `FFmpeg` | Determinism / Normalization Rules | Priority Stack Coverage |
| :--- | :--- | :--- | :--- | :--- |
| **Tier 1: Bit-Exact Media & Hash** | Lossless codecs (`ffv1`, `flac`, `png`, `pcm_*`, `rawvideo`), integer-exact decoders (`h264`, `hevc`, `av1` bit-exact profiles), demuxers, muxers (`nut`, `matroska`, `mp4`, `wav`) | `framemd5 -bitexact` (v2 format: frame bytes + `dts`/`pts`/`duration`/`size` + `side_data` hashes) & `crc` (Adler-32) & raw demux `packet` comparison | Force `-flags +bitexact -fflags +bitexact -idct simple -sws_flags +accurate_rnd+bitexact -threads 1` when upstream frame/slice threading alters metadata ordering; canonicalize big-endian palette formats (`hashenc.c:128`). | Priorities 1–4 simultaneously (exact output implies conformance on tested vectors). |
| **Tier 2: Float-Bounded DSP & Decoders** | Floating-point audio decoders (`aac`, `mp3`, `vorbis`, `opus`, `ac3`), resamplers (`swresample`), float filters (`amix`, `afir`) | `tiny_psnr` `f32`/`s16` dual gate: both `MAXDIFF <= max_eps` (catches single-sample bugs) AND `stddev <= max_rmse` (catches systemic bias), plus `audiomatch` (`eps = 0.161`) if priming delay differs. | Never rely on `stddev` alone without `MAXDIFF` (per executed probe); track explicit FMA/reassociation error bounds (`-ffp-contract=off` vs target FMA). | Priorities 1–3; distinguishes numeric reassociation from semantic bugs. |
| **Tier 3: Lossy Encoders (Spec + RD)** | Video/audio lossy encoders (`mpeg2video`, `h264`, `vp9`, `av1`, `aac`, `opus`) | Do **not** require compressed bitstream byte-equality for clean Rust encoders unless targeting bit-exact `-threads 1` preset parity; verify: (a) clean decode by *both* upstream `ffmpeg` and reference decoders with 0 errors/warnings, (b) `tiny_ssim` (`All >= min_ssim`, `PSNR >= min_psnr`) & bitrate within +/-epsilon at matched QP/rate-control target. | Run reference decoder over Rust encoder output *and* Rust decoder over upstream encoder output (cross-codec roundtrip). | Priorities 1–4 without over-constraining encoder heuristics. |
| **Tier 4: CLI & Structured Metadata** | `ffprobe` (`json`, `xml`, `compact`, `csv`, `flat`, `ini`), `ffmpeg` stream mapping/filtergraph CLI, `ffplay` sync law | Canonicalized `ffprobe -bitexact -noprivate -of json` AST diff + `xmllint --schema doc/ffprobe.xsd` on `-of xml=q=1:x=1`; virtual-time trace diff on extracted `ffplay` `SyncController` state transitions. | Strip `program_version`, `library_versions`, and host paths (`-print_filename`); normalize float precision formatting (`printf` vs Rust `ryu`) via numeric tolerance in AST diff. | Priorities 1–3 on tool surfaces and pipeline scheduling (`SyncQueue`/`trailing_dts`). |
| **Tier 5: Kernel SIMD vs. Scalar** | Every `x86_64`/`aarch64`/`riscv64` SIMD/asm kernel vs. pure Rust scalar reference | Dual validation: (a) FFI `checkasm`-compatible differential runner testing every ISA dispatch level against scalar Rust + redzone/signal/register-clobber checks (`float_near_abs_eps_ulp` handling zero crossings & NaNs explicitly), plus (b) machine-checked SIMD-vs-scalar equivalence proofs on critical integer/bit-exact kernels. | Seeded PRNG (`checkasm_srand`), padded input/output buffers (`+64` tail), explicit NaN equivalence policy (quiet NaN bit-preservation vs canonicalization). | Priorities 1–3 at instruction/kernel granularity. |

**Why this separation resolves historical C accidents (`Basis: derived`):** Upstream FATE encodes `CMP_TARGET = 534` (`fate-acodec-dca2`) or `4777` (`fate-acodec-ra144`) against decades-old C reference files whose exact RMSE reflects arbitrary historical fixed-point tables rather than specification bounds. A clean Rust rewrite should pass *two* checks: (1) direct upstream differential comparison under Tiers 1–5 (recording any exact upstream FATE deviations where Rust matches the normative ITU/ISO spec more closely than legacy FFmpeg), and (2) internal cross-ISA self-consistency (`Rust scalar` vs `Rust SIMD`) via Tier 5.

## Boundaries

- **Full `ffmpeg` / `ffprobe` / `ffplay` binary execution (`not examined`):** Local execution probed verbatim compiled `tests/tiny_psnr.c` and `tests/tiny_ssim.c` binaries from `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`; full `ffmpeg`, `ffprobe`, `ffplay`, and `checkasm` binaries were not built or run against upstream FATE sample media files in this workspace.
- **Individual `tests/fate/*.mak` rule census (`not examined` beyond representative modules):** `tests/fate/` contains 126 `.mak` files at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`; this inspection examined `tests/Makefile`, `tests/fate-run.sh`, `tests/fate/{acodec,vcodec,ffprobe,checkasm,api}.mak`, and partial grep outputs across `filter-audio.mak`, not all 126 `.mak` files exhaustively.
- **External library rate-control determinism (`unknown` / `not examined`):** Multithreaded lookahead/rate-control nondeterminism inside third-party encoders (`libx264`, `libx265`, `SVT-AV1`) invoked by `fftools` was not measured experimentally.
- **Hardware-accelerated filtergraph negotiation (`not examined`):** Specific `hw_frames_ctx` / `AVHWDeviceContext` pool negotiation paths inside `fftools/ffmpeg_hw.c` and `ffmpeg_filter.c` were not audited beyond observing `IFILTER_FLAG_DROPCHANGED` and dynamic `configure_filtergraph()` triggers.
- **`crc` muxer collision with IEEE CRC-32 (`known not to apply`):** Using an off-the-shelf IEEE 802.3 CRC-32 implementation for FATE `crc` tests is known to fail (`libavformat/crcenc.c:24,45` uses Adler-32).
- **10-bit+ precision in `tests/tiny_ssim.c` (`unsupported` by default build):** Default `BIT_DEPTH 8` compilation (`tests/tiny_ssim.c:39,77-88`) supports only 8-bit `4:2:0` planar YUV and explicitly warns that 10-bit block sums overflow signed 32-bit `int`.

## Evidence

### Primary Upstream Sources

1. **`FFmpeg/FFmpeg` at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (observed `2026-11-20`):**
   - Pipeline scheduler, thread queues & sync queues: `fftools/ffmpeg_sched.h:33-86,250-290` (`DEFAULT_PACKET_THREAD_QUEUE_SIZE 2`, `DEFAULT_FRAME_THREAD_QUEUE_SIZE 2`); `fftools/ffmpeg_sched.c:45` (`SCHEDULE_TOLERANCE (100 * 1000)`), `382-403`, `448-488` (`trailing_dts`, `progressing_dts`), `1180-1260` (`PreMuxQueue`, `mux_init`), `1331-1446` (`unchoke_downstream`, `unchoke_for_stream`, `choke_demux`), `1448-1539` (`schedule_update_locked`), `1568-1649` (`check_acyclic`), `1740-1815` (`start_prepare`, `sch_start`), `2581-2655` (`sch_filter_receive`); `fftools/thread_queue.c:1-175`; `fftools/sync_queue.c:40-145,232-340` (`overflow_heartbeat`).
   - Filtergraph lifecycle: `fftools/ffmpeg_filter.c:259-260,290-398,845-942,1177-1181,1960-1968,2187-2330,2501-2519,3096-3165,3211-3300`.
   - `ffprobe` & `textformat`: `fftools/ffprobe.c:220-360,3475-3530,3699-3755`; `fftools/textformat/avtextformat.h:45-140`; `fftools/textformat/tf_json.c:33-155`; `fftools/textformat/tf_xml.c:32-212`; `fftools/textformat/tf_compact.c:39-100`; `doc/ffprobe.xsd:1-80`.
   - `ffplay` synchronization: `fftools/ffplay.c:83-160,1597-1675,1748-1815,2559-2635`.
   - FATE & hash muxers: `tests/Makefile:1-60,209-230`; `tests/fate-run.sh:1-125,217-290,350-415,650-853`; `tests/fate/ffprobe.mak:1-27`; `tests/fate/acodec.mak:4,105-159`; `tests/fate/vcodec.mak:1-49`; `tests/fate/api.mak`; `tests/fate/checkasm.mak`; `tests/refcmp-metadata.awk:1-60`; `tests/audiomatch.c:37-128`; `libavformat/crcenc.c:24-68`; `libavformat/hashenc.c:51-412`.
   - `tiny_psnr` & `tiny_ssim`: `tests/tiny_psnr.c:33,95-324`; `tests/tiny_ssim.c:24-244`.
   - `checkasm`: `tests/checkasm/checkasm.h`, `tests/checkasm/checkasm.c`, `tests/checkasm/float_dsp.c:28-75`, `tests/checkasm/ext/include/checkasm/test.h:252-490`, `tests/checkasm/ext/include/checkasm/utils.h:48-169,238-455,516-745`, `tests/checkasm/ext/src/checkasm.c:580-675,1040-1180`, `tests/checkasm/ext/src/function.c:37-148`, `tests/checkasm/ext/src/signal.c:40-175`, `tests/checkasm/ext/src/stackguard.c:35-76`, `tests/checkasm/ext/src/utils.c:662-717`.
2. **Normative SSIM Reference (`doi: 10.1109/TIP.2003.819861`):**
   - Zhou Wang, Alan C. Bovik, Hamid R. Sheikh, and Eero P. Simoncelli, "Image Quality Assessment: From Error Visibility to Structural Similarity," *IEEE Transactions on Image Processing*, vol. 13, no. 4, pp. 600–612, Apr. 2004 (cited in `tests/tiny_ssim.c:23-24`).

### Reproducible Execution Probes (`Basis: execution`, `2026-11-20`)

Compiled verbatim `tests/tiny_psnr.c` and `tests/tiny_ssim.c` from `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` using `gcc (Debian 15.2.0-14) 15.2.0 -O2 -lm` on `x86_64-unknown-linux-gnu` (providing a 4-line configure-equivalent `libavutil/avconfig.h` with `AV_HAVE_BIGENDIAN 0` and `AV_HAVE_FAST_UNALIGNED 1` alongside pinned `libavutil/{attributes,bswap,intfloat,intreadwrite,macros}.h` and `libavutil/x86/{bswap,intreadwrite}.h`).

1. **`tiny_psnr` on synthesized 4096-sample `s16le` (`int(12000 * sin(i * 0.07))`) and `f32le` (`0.5 * sin(i * 0.07)`) inputs:**
   ```text
   $ ./tiny_psnr ref.s16 ref.s16 s16
   stddev:    0.00 PSNR:999.99 MAXDIFF:    0 bytes:     8192/     8192
   $ ./tiny_psnr ref.s16 lsb1.s16 s16      # +/-1 LSB alternating perturbation
   stddev:    1.00 PSNR: 96.33 MAXDIFF:    1 bytes:     8192/     8192
   $ ./tiny_psnr ref.s16 spike.s16 s16     # single +50 LSB sample spike at sample 100
   stddev:    0.78 PSNR: 98.47 MAXDIFF:   50 bytes:     8192/     8192
   $ ./tiny_psnr ref.f32 eps.f32 f32       # +/-1e-6 perturbation
   stddev:     13.69 PSNR:1391.53 MAXDIFF:        17 bytes:    16384/    16384
   ```
2. **`tiny_ssim` on synthesized 3-frame `64x64` YUV420p (`18432` bytes):**
   ```text
   $ ./tiny_ssim ref.yuv ref.yuv 64x64
   Total 3 frames | PSNR Y:inf  U:inf  V:inf  All:inf | SSIM Y:1.00000 U:1.00000 V:1.00000 All:1.00000 (inf)
   $ ./tiny_ssim ref.yuv lsb1.yuv 64x64    # +/-1 LSB checkerboard on Y plane
   Total 3 frames | PSNR Y:48.131  U:inf  V:inf  All:49.892 | SSIM Y:0.99570 U:1.00000 V:1.00000 All:0.99713 (25.42721)
   $ ./tiny_ssim ref.yuv blur.yuv 64x64    # +/-4 4x4 block perturbation on Y plane
   Total 3 frames | PSNR Y:36.090  U:inf  V:inf  All:37.851 | SSIM Y:0.93610 U:1.00000 V:1.00000 All:0.95740 (13.70586)
   ```

## Revalidation

1. **Scheduler & `textformat` drift check:** Diff `fftools/ffmpeg_sched.{h,c}`, `fftools/sync_queue.c`, `fftools/textformat/*.c`, and `doc/ffprobe.xsd` against any newer `FFmpeg/FFmpeg` revision to verify whether `SCHEDULE_TOLERANCE`, default queue depths, `SyncQueue` overflow handling, or `ffprobe` section IDs/flags changed.
2. **`FATE` & `checkasm` oracle drift check:** Recompile `tests/tiny_psnr.c` and `tests/tiny_ssim.c` and diff `tests/fate-run.sh`, `libavformat/hashenc.c`, `libavformat/crcenc.c`, and `tests/checkasm/ext/src/utils.c` (`checkasm_float_near_*`) when updating the pinned reference FFmpeg commit.
3. **Cross-implementation differential smoke test:** Once a clean Rust CLI/codec binary exists, run `ffmpeg -bitexact` and the Rust equivalent side-by-side through `framemd5`, `tiny_psnr` (`oneoff` + `stddev`), `ffprobe -bitexact -noprivate -of json`, and `xmllint --schema doc/ffprobe.xsd` on a pinned FATE subset to confirm oracle coverage across all five tiers.
