# FFmpeg Codebase Architecture, Runtime CPU Dispatch, and Multi-ISA Assembly Corpus Census

## Summary

At `FFmpeg/FFmpeg` revision `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (`RELEASE` `8.0.git`), the repository contains `11,284` tracked blob files totaling `94,826,996` bytes and `2,217,903` lines of source text across seven core libraries (`libavutil`, `libavcodec`, `libavformat`, `libavfilter`, `libavdevice`, `libswscale`, `libswresample`), CLI frontends (`fftools`), utilities (`tools`), tests (`tests`, including `tests/checkasm`), and build infrastructure (`configure`, `ffbuild`). Legacy `libpostproc` is completely absent (`0` references in `configure`); its filters (`pp`, `fspp`, `uspp`, `pp7`) reside in `libavfilter`. `libavcodec` alone accounts for `2,788` files (`46,489,936` bytes; `1,176,821` LOC)—more than half of all C/assembly lines in the tree.

FFmpeg separates handwritten SIMD optimization from portable C decoders through three distinct mechanisms:
1. **External stand-alone assembly** (`.asm` for x86 NASM/YASM via `libavutil/x86/x86inc.asm`, `.S` for GAS on AArch64, ARM, RISC-V, LoongArch, and 1 legacy file on PPC): across first-party libraries (excluding vendored `tests/checkasm/ext/`), FFmpeg ships `186` x86 `.asm` files (`83,442` LOC with `942` `cglobal` kernels), `72` AArch64 `.S` files (`51,610` LOC; `846` exported and `167` local `function` kernels), `73` ARM `.S` files (`31,014` LOC; `534` `function` kernels), `74` RISC-V `.S` files (`12,386` LOC; `310` `func` kernels using `650` `vset*vl*` VLA instructions), `12` LoongArch `.S` files (`15,304` LOC; `230` `function` kernels), and `1` PPC `.S` file (`147` LOC).
2. **Compiler SIMD intrinsics in `.c` files** rather than `.S` files on architectures whose ABI or vector register conventions historically favored C intrinsics: `mips` (`85` arch `.c` files, `94,482` LOC, `35` `msa.h` consumers, `0` `.S` files), `ppc` (`60` arch `.c` files, `11,035` LOC, `53` `altivec.h` consumers), `loongarch` (`46` arch `.c` files, `32,815` LOC alongside `lsxintrin.h`/`lasxintrin.h`), and `wasm` (`4` `.c` files, `1,221` LOC, `wasm_simd128.h`).
3. **Inline GNU `__asm__` in hot serial paths** (`567` inline-asm sites in first-party libraries, concentrated in `libavcodec/mips/` Loongson MMI `221` sites, `libswscale/x86/rgb2rgb.c` `102` sites, `libavcodec/ppc/` `50` sites, `libavcodec/x86/` `52` sites, and branchless `get_cabac_inline_*` in `libavcodec/{x86,aarch64,mips,loongarch}/cabac.h`) where indirect vtable calls would stall branch predictors or C compilers fail to preserve carry-flag/register schedules.

Runtime dispatch centers on `av_get_cpu_flags()` (`libavutil/cpu.c`), which caches hardware/OS capability detection in a relaxed `atomic_int` (`cpu_flags`) and applies OS state-save checks (`xgetbv` XCR0 gating for AVX/AVX-512 on x86; `getauxval`/`riscv_hwprobe`/`sysctlbyname`/Win32 `IsProcessorFeaturePresent` on AArch64 and RISC-V) plus microarchitectural slow-unit flags (`AVXSLOW`, `SSE2SLOW`, `ATOM`, `SLOW_GATHER`). Codec and filter contexts register `DSPContext` structs containing flat tables of C function pointers initialized to scalar C implementations and progressively overwritten tier-by-tier in `ff_*_init_<isa>()` routines. Differential correctness, ABI callee-saved register/stack-canary preservation, x87 `EMMS`/AVX `VZEROUPPER` hygiene, and buffer guard-band integrity (`BUF_RECT`) are continuously verified by `103` test modules in `tests/checkasm/` backed by vendored `libcheckasm` (`tests/checkasm/ext/`). For a clean-room verified Rust rewrite, the primary architectural boundary is between the **replaceable C DSP vtable dispatch and memory-layout conventions** (which can become monomorphized traits or static feature-gated dispatch over safe slice views) and the **irreducible ISA-level semantics** of `~2,550+` handwritten SIMD kernels and entropy-coding inline assembly blocks.

## Applicability

All quantitative counts, file paths, symbol signatures, and line references in this report apply strictly to `FFmpeg/FFmpeg` at commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (tree snapshot dated `2026-11-20`, `RELEASE` `8.0.git`).

- **ISA and build-configuration scope:** File and line counts measure the complete tracked source tree regardless of host configure flags. Runtime behavior (`av_get_cpu_flags`, `DSPContext` initialization, `checkasm` trampolines) reflects default enabled `HAVE_*_EXTERNAL` and `HAVE_*_INLINE` configurations on ELF, Mach-O, and Windows PE/COFF (Win64) ABIs as encoded in `configure`, `libavutil/`, `libavcodec/`, and `tests/checkasm/`.
- **Clean-room verification context:** Structural invariants (`linesize` negative strides, `AV_INPUT_BUFFER_PADDING_SIZE`, `STRIDE_ALIGN`, `DSPContext` granularity, `x86inc.asm` ABI registers) are analyzed against a four-tier verification priority stack: (1) UB-freedom, (2) Panic-freedom, (3) behavioral and SIMD-vs-scalar equivalence, and (4) normative codec/container conformance.
- **Cross-corpus scope:** ISA semantic formalizations, inline assembly contracts, and SIMD vector-width subtleties build on existing corpus findings in `rust-inline-assembly-contracts-relocations-and-simd-correspondence`, `asl-l3-lnsym-and-isa-verification-frameworks-lean-adaptation`, `sail-isa-models-lean-backend-and-rv64d-decoding-framing`, `rvv-lmul-vtype-hazards-arm-sme-streaming-za-tiles-and-ffload-speculation`, `x86-avx512-short-loop-regression-and-vector-width-profitability`, and `portable-simd-repr-simd-legalization-and-cross-arch-cost-certificates`.

## Findings

### 1. Monorepo Component Split, Library Layering, and Dependency DAG

Basis: source

At commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, FFmpeg organizes `11,284` tracked blob files (`94,826,996` bytes; `2,217,903` text LOC across `.c`, `.h`, `.asm`, `.S`, `.glsl`, `.cl`, `.cu`, `.mak`, docs, and tests) into seven shared/static libraries, `fftools`, and supporting trees:

| Directory | Files | Bytes | Text LOC | Major ABI (`version*.h`) | Primary Architectural Role |
| :--- | ---: | ---: | ---: | :---: | :--- |
| `libavcodec` | 2,788 | 46,489,936 | 1,176,821 | 63 | Decoders, encoders, parsers, BSFs (`60` files), CBS (`40` files), `hwaccels`, DSP tables |
| `tests` | 5,855 | 12,331,937 | 57,444 | — | FATE regression refs, `checkasm` (`103` test modules + `59` files in `tests/checkasm/ext/`), API tests |
| `libavfilter` | 831 | 11,583,198 | 313,990 | 12 | Audio/video filter graph (`AVFilterGraph`), Vulkan/OpenCL/CUDA/Metal shaders |
| `libavformat` | 745 | 9,782,770 | 282,408 | 63 | Muxers, demuxers, `AVIOContext` transport protocols (`file`, `http`, `tls`, etc.) |
| `libavutil` | 466 | 4,371,146 | 123,528 | 61 | Common primitives (`AVFrame`, `AVBufferRef`, `av_malloc`, `cpu`, `av_tx` FFT/MDCT, `hwcontext`) |
| `libswscale` | 169 | 3,454,403 | 81,960 | 10 | Pixel format conversion & scaling (`SwsContext`, declarative `SwsOp`/`graph` IR, Vulkan) |
| `doc` | 114 | 3,027,165 | 82,998 | — | Texinfo manuals, API docs, build guides |
| `fftools` | 57 | 1,495,795 | 42,941 | — | `ffmpeg`, `ffprobe`, `ffplay` CLI apps + DAG transcode `Scheduler` (`ffmpeg_sched.{h,c}`) |
| `libavdevice` | 78 | 795,171 | 22,422 | 63 | OS capture/playback devices (wraps `libavformat`/`libavcodec` muxer/demuxer ABI) |
| `<root>` | 18 | 529,494 | 10,059 | — | `configure`, `Makefile`, `Changelog`, `MAINTAINERS`, `RELEASE`, license texts |
| `tools` | 60 | 407,945 | 9,034 | — | Standalone tools and OSS-Fuzz targets (`target_dec_fuzzer.c`, `target_dem_fuzzer.c`, etc.) |
| `libswresample` | 51 | 372,329 | 9,411 | 7 | Audio sample-rate, channel-layout, and sample-format conversion |
| `compat` | 25 | 129,851 | 3,863 | — | Platform libc/C11/atomics/CUDA/Vulkan compatibility shims |
| `.forgejo` / `ffbuild` / `presets` / `fairy` | 27 | 55,856 | 1,024 | — | CI workflows, pkg-config/linker `.v` scripts, `libx264`/codec presets |

Exact inter-library dependency DAG verified from `configure`:
- **`libavutil` (`LIBAVUTIL_VERSION_MAJOR = 61`, `MINOR = 21` in `libavutil/version.h`)**: Root of the DAG (`no av*_deps`). Supplies memory allocation (`av_malloc`), atomic refcounting (`AVBufferRef`), `AVFrame`, `AVRational`, `av_tx` transforms, hardware device contexts (`AVHWDeviceContext`), and `av_get_cpu_flags()`.
- **`libswresample` (`MAJOR = 7`) and `libswscale` (`MAJOR = 10`)**: Depend solely on `avutil` (`swresample_deps="avutil"`, `swscale_deps="avutil"`). Notably, `libswscale` is transitioning toward an explicit composable micro-op graph (`libswscale/ops.h`, lines 36–70, defining `SwsOpType`: `SWS_OP_READ`, `SWS_OP_WRITE`, `SWS_OP_SWAP_BYTES`, `SWS_OP_SWIZZLE`, `SWS_OP_UNPACK`, `SWS_OP_PACK`, `SWS_OP_LSHIFT`, `SWS_OP_RSHIFT`, `SWS_OP_CLEAR`, `SWS_OP_CONVERT`, `SWS_OP_MIN`, `SWS_OP_MAX`, `SWS_OP_SCALE`, `SWS_OP_LINEAR`, `SWS_OP_DITHER`, `SWS_OP_FILTER_H`, `SWS_OP_FILTER_V`, `SWS_OP_LUT_3D`) alongside `swscale_vulkan`.
- **`libavcodec` (`MAJOR = 63`)**: Depends only on `avutil` (`avcodec_deps="avutil"`). Internally modularizes bitstream filters (`libavcodec/bsf/`: `60` files), Coded Bitstream (CBS) structural parsers/writers (`libavcodec/cbs*`: `40` files), modern large codecs (`libavcodec/vvc/`: `34` files), and hardware acceleration glue (`libavcodec/vulkan*`: `67` files including `47` `.glsl` compute shaders; `d3d11`/`d3d12`/`dxva`: `24` files; `vaapi`: `22` files; `nvdec`/`nvenc`/`cuvid`: `17` files; `videotoolbox`: `5` files).
- **`libavformat` (`MAJOR = 63`)**: Depends on `libavcodec` and `libavutil` (`avformat_deps="avcodec avutil"`) because demuxers reuse codec parsers (`AVCodecParserContext`), bitstream filters, and `AVPacket` / codec parameter structs (`AVCodecParameters`).
- **`libavfilter` (`MAJOR = 12`)**: Base dependency `avfilter_deps="avutil"`, with optional filter-level edges into `libavcodec`/`libavformat`/`libswscale`/`libswresample` plus GPU shader sources (`22` `.glsl`, `14` `.cl` OpenCL, `10` `.cu` CUDA, `1` `.metal`).
- **`libavdevice` (`MAJOR = 63`)**: Depends on `libavformat`, `libavcodec`, and `libavutil` (`avdevice_deps="avformat avcodec avutil"`).
- **`fftools`**: Orchestrates all libraries via an explicit acyclic multithreaded pipeline `Scheduler` (`fftools/ffmpeg_sched.h`, lines 31–101), isolating demuxer, decoder, filtergraph, encoder, and muxer threads behind scheduler message queues to prevent direct cross-stage coupling.

### 2. Quantitative Multi-ISA Assembly and Intrinsics Census

Basis: source

Every ISA-specific directory in `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` was enumerated across all libraries and tests. In first-party libraries (excluding `tests/checkasm/ext/src/`, which adds `2` x86 `.asm`, `3` ARM `.S`, `2` RISC-V `.S`, `2` LoongArch `.S`, and `3` arch `.c`/`.h` files for the vendored test harness itself), the complete `(Library × ISA)` footprint is:

| Library / Scope | ISA | `.asm` / `.S` Files | `.asm` / `.S` LOC | Arch `.c` Files | Arch `.c` LOC | Arch `.h` Files | Arch `.h` LOC |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `libavcodec` | `x86` | 115 (`.asm`) | 57,414 | 83 | 11,777 | 17 | 1,456 |
| `libavcodec` | `aarch64` | 49 (`.S`) | 40,452 | 38 | 4,009 | 7 | 625 |
| `libavcodec` | `arm` | 61 (`.S`) | 28,413 | 48 | 3,836 | 19 | 1,006 |
| `libavcodec` | `riscv` | 61 (`.S`) | 10,491 | 43 | 2,842 | 5 | 370 |
| `libavcodec` | `loongarch` | 9 (`.S`) | 12,004 | 33 | 26,062 | 12 | 1,673 |
| `libavcodec` | `mips` | 0 | 0 | 82 | 93,944 | 27 | 4,020 |
| `libavcodec` | `ppc` | 1 (`.S`) | 147 | 48 | 6,833 | 24 | 695 |
| `libavcodec` | `wasm` | 0 | 0 | 3 | 1,180 | 2 | 87 |
| `libavfilter` | `x86` | 42 (`.asm`) | 10,734 | 41 | 2,797 | 0 | 0 |
| `libavfilter` | `aarch64` | 4 (`.S`) | 1,585 | 4 | 286 | 0 | 0 |
| `libavfilter` | `riscv` | 3 (`.S`) | 268 | 4 | 131 | 0 | 0 |
| `libavutil` | `x86` | 12 (`.asm`) | 6,676 | 7 | 909 | 9 | 902 |
| `libavutil` | `aarch64` | 9 (`.S`) | 3,640 | 5 | 766 | 7 | 512 |
| `libavutil` | `arm` | 4 (`.S`) | 1,238 | 5 | 525 | 6 | 376 |
| `libavutil` | `riscv` | 6 (`.S`) | 970 | 5 | 383 | 4 | 466 |
| `libavutil` | `loongarch` | 0 | 0 | 1 | 61 | 3 | 2,027 |
| `libavutil` | `mips` | 0 | 0 | 3 | 538 | 7 | 3,524 |
| `libavutil` | `ppc` | 0 | 0 | 4 | 447 | 6 | 476 |
| `libavutil` | `wasm` | 0 | 0 | 1 | 41 | 0 | 0 |
| `libswscale` | `x86` | 14 (`.asm`) | 7,061 | 7 | 5,894 | 1 | 1,231 |
| `libswscale` | `aarch64` | 8 (`.S`) | 5,490 | 10 | 4,234 | 4 | 878 |
| `libswscale` | `arm` | 6 (`.S`) | 921 | 2 | 237 | 0 | 0 |
| `libswscale` | `loongarch` | 3 (`.S`) | 3,300 | 12 | 6,692 | 1 | 240 |
| `libswscale` | `ppc` | 0 | 0 | 8 | 3,755 | 1 | 51 |
| `libswscale` | `riscv` | 4 (`.S`) | 657 | 3 | 200 | 0 | 0 |
| `libswresample` | `x86` | 3 (`.asm`) | 1,557 | 4 | 383 | 0 | 0 |
| `libswresample` | `aarch64` | 2 (`.S`) | 443 | 3 | 217 | 0 | 0 |
| `libswresample` | `arm` | 2 (`.S`) | 442 | 3 | 217 | 0 | 0 |
| **Total (first-party libs)** | **All 8 ISAs** | **425** | **193,803** | **552** | **179,614** | **163** | **20,636** |

*(Note: `libavdevice/riscv` and `libavformat/riscv` each contain 1 stub `.c` file + `Makefile` of `1` LOC; `libavcodec/tests/{x86,aarch64,arm,ppc}` each contain 1 `.c` unit test; `tests/checkasm/ext/src/` adds 9 `.asm`/`.S` and 5 `.c`/`.h` harness files.)*

#### Architecture-by-Architecture Breakdown

1. **`x86` (`186` first-party `.asm` files, `83,442` LOC; `942` `cglobal` functions):**
   - **Macro abstraction (`libavutil/x86/x86inc.asm`, `1,978` lines):** Nearly every external x86 kernel is written once against `x86inc.asm` (`m0..m31`, `r0..r15`, `mmsize` = `8`/`16`/`32`/`64`) and instantiated across vector widths via `INIT_MMX`, `INIT_XMM`, `INIT_YMM`, and `INIT_ZMM` (`x86inc.asm`, lines 1085–1145). `cglobal` (`x86inc.asm`, lines 820–861) handles ELF/Mach-O/COFF symbol mangling, `.note.gnu.property` CET shadow-stack ELF notes (lines 906–921), stack probing (`PROBE_STACK`, lines 389–397), Win64 shadow space and `xmm6..xmm15` callee-save spilling (`WIN64_PUSH_XMM`/`WIN64_SPILL_XMM`, lines 525–605), automatic AVX VEX-prefix lowering (`RUN_AVX_INSTR`, lines 1352–1420), and `vzeroupper` emission (`vzeroupper_required = (mmsize > 16 && (ARCH_X86_64 == 0 || xmm_regs_used > 16 || notcpuflag(avx512)))`, line 374, coupled with `AVX512_MM_PERMUTATION` lines 1074–1083 which maps `m0..m15` to `zmm16..zmm31` on x86-64 so AVX-512 kernels using `<= 16` registers avoid `vzeroupper` entirely!).
   - **Instruction-set distribution across `890` `INIT_*` macro invocations in first-party `.asm` files:** `INIT_XMM`: `701`, `INIT_YMM`: `150`, `INIT_ZMM`: `23`, `INIT_MMX`: `16`. By leading ISA feature tag: `sse2` (`364`), `ssse3` (`114`), `avx2` (`109`), `avx` (`100`), `sse4` (`49`), `sse` (`44`), `avx512icl` (`20`), parameterized `cpuname`/`%1` (`20`), `fma3` (`16`), `sse3` (`11`), `avx512` (`7`), `mmxext` (`5`), `mmx` (`4`), `fma4` (`3`), `xop` (`3`), `aesni` (`1`), `clmul` (`1`).

2. **`aarch64` (`72` `.S` files, `51,610` LOC; `846` exported + `167` local `function` kernels):**
   - `libavutil/aarch64/asm.S` (`492` lines) defines `function name, export=0/1`, PAC/BTI link-register signing (`AARCH64_SIGN_LINK_REGISTER`), and scoped `.arch_extension` toggles (`ENABLE_DOTPROD`, `ENABLE_I8MM`, `ENABLE_SVE`, `ENABLE_SVE2`, `ENABLE_SME`, `ENABLE_SME2`, lines 43–138).
   - Over `90%` of exported kernels target baseline NEON (`1,002` `neon`-tagged `function` definitions/files), augmented by specialized 8-bit matrix/dot extensions (`48` `i8mm`, `5` `dotprod`, `4` `crc`). Currently, SVE and SME in `aarch64/*.S` are minimal (`libavutil/aarch64/cpu_sve.S` and `cpu_sme.S` probe hardware vector length via `cntb x0`), while `1` file includes `<arm_neon.h>` intrinsics.

3. **`arm` (`73` first-party `.S` files, `31,014` LOC; `534` `function` entries):**
   - `libavutil/arm/asm.S` (`430` lines) supports both ARM and Thumb-2 (`CONFIG_THUMB`) unified syntax (`.arch armv5te`/`armv6`/`armv6t2`/`armv7-a`). Kernel breakdown by target tag: `410` NEON (`armv7-a`), `67` ARMv6 (`armv6`/`armv6t2`), `18` generic ARM, `8` ARMv5TE, `5` VFP, and `26` other/helper entries.

4. **`riscv` (`74` first-party `.S` files, `12,386` LOC; `310` `func` entries):**
   - `libavutil/riscv/asm.S` (`257` lines) introduces a structured extension-scoped `func sym, exts...` macro (`lines 51–71`) that wraps every kernel in `.option push` / `.option arch, +<ext>` / `.option pop`, plus `parse_vtype` / LMUL selection helpers (`lines 107–150`).
   - Vector-Length Agnostic (VLA) RVV 1.0 dominates (`291` `rvv`-tagged functions using `650` `vset*vl*` instructions: `434` `vsetvli`, `207` `vsetivli`, `9` `vsetvl`). Per-function extension targets span `zve32x` (`135`), `zve32x, zba` (`64`), `zve32f, zba` (`20`), `zve64x` (`20`), `zve64x, zba` (`9`), `zve32x, b` (`9`), `zve32x, zbb, zba` (`7`), `zbb` (`6`), `zve32f, b` (`6`), `zve64d, zba` (`5`), `zve64x, b` (`4`), and vector bitmanip `zve32x, zvbb, zba` (`3`).

5. **Intrinsics-dominant and legacy architectures (`loongarch`, `mips`, `ppc`, `wasm`):**
   - **`loongarch`**: Hybrid split—`12` `.S` files (`15,304` LOC, `230` `function` macros across `hevc_mc.S` `128`, `h264qpel.S` `27`, `h264dsp.S` `16`, `libswscale/loongarch/` `31`, and others) plus `46` `.c` files (`32,815` LOC) using LSX/LASX intrinsics (`lsxintrin.h`, `lasxintrin.h`, and `libavutil/loongarch/loongson_intrinsics.h`).
   - **`mips`**: `0` `.S` files; all `85` arch `.c` files (`94,482` LOC) use either `<msa.h>` C SIMD intrinsics (`35` files) or inline Loongson MMI / MIPS DSP assembly (`221` inline `__asm__` blocks across `33` `libavcodec/mips/*.c` files).
   - **`ppc`**: `1` `.S` file (`libavcodec/ppc/asm.S`, `147` LOC); all SIMD kernels live in `60` `.c` files (`11,035` LOC) using `<altivec.h>` (`53` files) plus `50` inline `__asm__` sites (`41` in `libavcodec/ppc/me_cmp_altivec.c`).
   - **`wasm`**: `0` `.S` files; `4` `.c` files (`1,221` LOC) using `<wasm_simd128.h>` (`2` files).

6. **Inline GNU `__asm__` across all libraries (`567` sites):**
   - Outside `mips/` and `ppc/`, inline `__asm__` persists in two performance-critical niches: (a) **legacy scalar/RGB swscale x86 paths** (`102` sites in `libswscale/x86/rgb2rgb.c`, `21` in `libswscale/x86/swscale_template.c`), and (b) **entropy-coding & scalar bit/math macros** (`libavcodec/x86/cabac.h` `4` blocks, `libavcodec/aarch64/cabac.h` `1` block, `libavcodec/x86/mathops.h` `11` blocks including `MULL`/`MULH`/`NEG_SSR32`/`NEG_USR32`/`mid_pred`, `libavutil/arm/intmath.h` `11` blocks, `libavutil/riscv/intmath.h` `7` blocks).

### 3. Runtime CPU Feature Detection (`av_get_cpu_flags`) and OS State Gating

Basis: source

Runtime dispatch is decoupled from codec logic through `av_get_cpu_flags()` (`libavutil/cpu.c`, lines 56–117) and bitmasks in `libavutil/cpu.h` (lines 32–109):

- **Thread-safe lazy initialization and override:** `cpu_flags` is a file-scope `atomic_int` initialized to `-1`. On first call, `av_get_cpu_flags()` loads `cpu_flags` with `memory_order_relaxed`; if `-1`, it invokes the compile-time selected `ff_get_cpu_flags_<arch>()` (`libavutil/cpu.c`, lines 59–79) and stores the bitmask. `av_force_cpu_flags(int arg)` (`lines 81–107`) lets tests (`checkasm`) or callers mask features dynamically (and on x86 warns and implies `AV_CPU_FLAG_MMX` if SSE/AVX flags are forced without MMX).
- **x86 CPUID + XCR0 OS-Save Gating (`libavutil/x86/cpu.c`, lines 95–272):**
  1. Checks `EFLAGS.ID` toggleability on 32-bit x86 before running `cpuid` (`lines 80–91`, `107–108`).
  2. Leaf `1` detects `CMOV`, `MMX`, `MMXEXT`, `SSE`..`SSE4.2`, `CLMUL`, `AESNI`. Crucially, AVX (`AV_CPU_FLAG_AVX = 0x4000`) and `FMA3` require **both** `ECX[27:28]` (`OSXSAVE` + `AVX`) **and** `xgetbv(0)` XCR0 bits `[2:1] == 0x6` (`XMM` + `YMM` OS state saving enabled, `lines 141–149`).
  3. Leaf `7` (`subleaf 0`) requires `AV_CPU_FLAG_AVX` for `AVX2`; `AVX-512` (`AV_CPU_FLAG_AVX512 = 0x100000`) requires `xcr0_lo & 0xe0 == 0xe0` (opmask `k0..k7`, `ZMM_Hi256`, `Hi16_ZMM` OS state), `AVX2`, and `EBX` `F | CD | BW | DQ | VL` (`0xd0030000`, `lines 158–161`). Ice Lake subset (`AV_CPU_FLAG_AVX512ICL = 0x200000`) further checks `VNNI | IFMA | VBMI | VBMI2 | VPOPCNTDQ | BITALG | GFNI | VAES | VPCLMULQDQ` (`EBX & 0xd0200000` and `ECX & 0x5f42`, `lines 162–165`). `AVX-VNNI` (`subleaf 1` `EAX[4]`) also requires OS `YMM` state (`lines 176–184`), whereas `BMI1`/`BMI2` do not (`lines 170–175`).
  4. Vendor/microarchitecture penalty flags (`lines 200–267`): Sets `AV_CPU_FLAG_SSE2SLOW` (AMD without SSE4a; Intel Banias/Dothan/Yonah where `SSE2` is XOR-disabled by default), `AV_CPU_FLAG_AVXSLOW` (AMD Bulldozer/Jaguar families `0x15`/`0x16` lacking 256-bit execution units), `AV_CPU_FLAG_SLOW_GATHER` (AMD Zen 3 and earlier `family <= 0x19`, Intel `family == 6 && model < 143` due to GDS mitigation), `AV_CPU_FLAG_ATOM` (`model == 28`), and `AV_CPU_FLAG_SSSE3SLOW` (Conroe `model < 23`). Macros in `libavutil/x86/cpu.h` (`EXTERNAL_AVX2_FAST`, `EXTERNAL_AVX_FAST`) check `HAVE_<EXT>_EXTERNAL && (flags & AV_CPU_FLAG_<EXT>) && !(flags & AV_CPU_FLAG_<SLOW>)` (`libavutil/cpu_internal.h`, lines 26–41).
- **AArch64 (`libavutil/aarch64/cpu.c`, lines 39–254):** Combines static compiler predefines (`__ARM_FEATURE_*`) with OS probes: Linux/FreeBSD `AT_HWCAP`/`AT_HWCAP2` via `ff_getauxval()` (`lines 43–70`), Apple `sysctlbyname("hw.optional.arm.FEAT_*")` (`lines 83–107`), OpenBSD `CTL_MACHDEP` `CPU_ID_AA64ISAR{0,1}`, and Windows `IsProcessorFeaturePresent(PF_ARM_*)`. Runtime scalable vector lengths are queried via `ff_aarch64_sve_length()` (`cntb x0` in `cpu_sve.S`) and `ff_aarch64_sme_length()` (`smstart; cntb x0; smstop` in `cpu_sme.S`).
- **RISC-V (`libavutil/riscv/cpu.c`, lines 52–153):** Queries Linux `riscv_hwprobe` syscall (`RISCV_HWPROBE_KEY_BASE_BEHAVIOR`, `IMA_EXT_0`, `CPUPERF_0`)—falling back to `getauxval(AT_HWCAP)`—and enforces a minimum 128-bit vector width (`ff_get_rv_vlenb() >= 16`, `line 71`) for runtime `Zve32x` dispatch (`csrr vlenb` in `libavutil/riscv/cpu.h`, lines 48–58).
- **Alignment Query (`av_cpu_max_align()`, `libavutil/cpu.c`, lines 289–308; `x86/cpu.c`, lines 274–301):** Returns `64` on AVX-512, `32` on AVX/AVX2, `16` on SSE/NEON/WASM-SIMD128, and `8` otherwise, driving buffer allocation alignment.

### 4. `DSPContext` Function-Pointer Table Initialization and Dispatch Overhead

Basis: source

FFmpeg dispatches nearly all block/pixel/audio DSP kernels through per-context structs of C function pointers (`H264DSPContext`, `VVCInterDSPContext`, `VVCIntraDSPContext`, `SwsContext`, `AudioDSPContext`, etc.) initialized via a uniform **progressive-overwrite pattern**:

1. **Unconditional C baseline:** `ff_h264dsp_init(H264DSPContext *c, int bit_depth, int chroma_format_idc)` (`libavcodec/h264dsp.c`, lines 66–154) first populates every function pointer slot (`weight_pixels_tab[4]`, `biweight_pixels_tab[4]`, `v/h_loop_filter_*`, `idct_add*`, `add_pixels*_clear`, `startcode_find_candidate`) with bit-depth-specialized pure C functions (`H264_DSP(8|9|10|12|14)`).
2. **Architecture tail call (`lines 155–169`):** Dispatches via `#if ARCH_<ISA>` to `ff_h264dsp_init_<isa>(c, bit_depth, chroma_format_idc)`.
3. **Monotonic feature-tier overwrite:** Each `ff_*_init_<isa>` reads `int cpu_flags = av_get_cpu_flags();` and overwrites subsets of pointers sequentially from oldest to newest ISA tier:
   - In `libavcodec/x86/h264dsp_init.c` (lines 180–334): `EXTERNAL_SSE2` overwrites `idct8_add`, `weight_pixels_tab[0..2]`, `deblock_*` -> `EXTERNAL_SSSE3` overwrites `biweight_pixels_tab[0..2]` -> `EXTERNAL_AVX` overwrites `deblock_*_avx` and `idct_add_8_avx`.
   - In `libavcodec/aarch64/h264dsp_init_aarch64.c` (lines 109–166): `have_neon(cpu_flags)` overwrites 8-bit and 10-bit loop filters, weights, and IDCTs.
   - In `libavcodec/riscv/h264dsp_init.c` (lines 101–233): checks `AV_CPU_FLAG_RVB_BASIC` for `startcode_find_candidate_rvb`, `AV_CPU_FLAG_RVV_I32` + `ff_rv_vlen_least(128)` for loop filters, `AV_CPU_FLAG_RVB` + `zvl128b` for 16-wide weights, and `AV_CPU_FLAG_RVV_I64` for 8-wide weights.
4. **Multi-dimensional dispatch tables in modern codecs:** `libavcodec/vvc/dsp.h` (lines 47–186) scales this pattern up to 4D function pointer arrays (`put[2 /*luma,chroma*/][7 /*log2(w)-1*/][2][2]`, `itx[VVC_N_TX_TYPE][VVC_N_TX_SIZE]`) across `VVCInterDSPContext`, `VVCIntraDSPContext`, `VVCItxDSPContext`, `VVCLMCSDSPContext`, `VVCLFDSPContext`, `VVCSAODSPContext`, and `VVCALFDSPContext`.
5. **Granularity and why entropy coding stays inline:** Indirect function-pointer calls amortize cleanly over `4×4` to `64×64` pixel blocks, deblocking edges, or 1D/2D `av_tx` transforms (`10s` to `1,000s` of cycles per call). Conversely, bitstream entropy primitives like CABAC (`get_cabac_inline_x86` in `libavcodec/x86/cabac.h`, lines 177–209; `get_cabac_inline_aarch64` in `libavcodec/aarch64/cabac.h`, lines 30–100) execute ~5–15 instructions per bit with tight loop-carried dependencies on `(low, range, bytestream, *state)` and therefore remain `av_always_inline` GNU `__asm__` macros rather than `DSPContext` entries.

### 5. The `checkasm` Differential Equivalence and ABI-Clobber Harness

Basis: source

`tests/checkasm/` comprises `103` top-level test suites registered in `tests/checkasm/checkasm.c` (lines 57–330) built atop vendored `libcheckasm` (`tests/checkasm/ext/`, `59` files). Its verification guarantees extend far beyond value equality:

1. **Tier-by-tier differential chaining (`tests/checkasm/ext/src/checkasm.c`, lines 552–614; `tests/checkasm/checkasm.c`, lines 333–428):** `checkasm` runs `check_cpu_flag(NULL)` first (masking off all SIMD bits in `cpuflags[]` so `C` implementations execute and populate `checkasm_key_ref`), then iterates through `cpuflags[]` in ascending ISA order (`MMX` -> `MMXEXT` -> ... -> `AVX512ICL` on x86; `ARMV8` -> `NEON` -> `DOTPROD` -> `I8MM` -> `SVE` -> ... on AArch64; `RVI` -> `RV_zbb` -> `RV_zve32x` -> ... on RISC-V). Each time `check_func(ptr, ...)` sees a distinct function pointer, `call_ref(...)` invokes the **highest previously validated** implementation and `call_new(...)` invokes the newly registered kernel under strict trampoline checking.
2. **ABI & microarchitectural-state trampoline enforcement (`tests/checkasm/ext/src/x86/checkasm.asm`, lines 150–340; `arm/checkasm_64.S`, lines 100–287; `riscv/callcheck.S`; `loongarch/checkasm.S`):**
   - **Upper-32-bit GPR poisoning (`x86_64`):** `CLOBBER_UPPER` (`0xdeadbeef00000000`, `x86/checkasm.asm`, lines 143–171, 196) writes `0xdeadbeef` into the upper 32 bits of integer arguments to catch assembly kernels reading 64-bit `rNq` instead of zero-extended 32-bit `rNd` parameters.
   - **Callee-saved GPR and Win64 XMM verification:** Loads fixed 64-bit and 128-bit sentinel patterns (`n7..n14`, `x6..x15` on Win64) before `call t0` and aborts (`failed to preserve register`) if any callee-saved GPR or `xmm6..xmm15` is clobbered (`lines 204–309`). Analogous sentinel checks verify `x19..x28` and `d8..d15` on AArch64 (`arm/checkasm_64.S`, lines 100–120), `s0..s8`/`fs0..fs7` on LoongArch, and GPR/FPR/V-CSR invariants on RISC-V.
   - **64-byte stack canary redzone (`x86/checkasm.asm`, lines 183–231):** Writes `not return_address` across 8 qwords immediately above stack-passed arguments and verifies exact preservation after return (`stack corruption`).
   - **x87 FPU (`emms`) and AVX (`vzeroupper`) state checks (`lines 311–336`):** Inspects `fstenv` x87 tag word (`== 0xffff` unless `declare_func_emms` is used) and executes `xgetbv(0)` checking `XCR0` YMM dirty bit (`test al, 0x04`)—aborting with `"missing vzeroupper"` if an AVX/AVX2 kernel returns with dirty upper YMM state.
3. **2D guard-band buffer checking (`tests/checkasm/ext/include/checkasm/utils.h`, lines 516–772):** `BUF_RECT(type, name, w, h)` allocates `((h) + 32) * (CHECKASM_ROUND(w, 64) + 64) + 64` elements (`16` guard lines top/bottom, `64+` guard elements left/right), initialized with pathological byte patterns (`INITIALIZE_BUF_RECT`), and `checkasm_check_rect_padded` checks both active `(w × h)` pixels and surrounding guard bands (`padding = 8`) to catch out-of-bounds SIMD stores. Floating-point buffers use ULP-bounded comparison (`checkasm_check_impl_float_ulp`).
4. **Hardware cycle-counter benchmarking (`test.h`, lines 587–627; `ext/src/checkasm.c`, lines 386–494):** Uses `CHECKASM_PERF_ASM` (`rdtsc`/`cntvct`/cycle CSR) in 32× unrolled loops with online `4×` outlier trimming, subtracts calibrated `nop_cycles`, alternates input/output buffers via `checkasm_alternate()` to measure throughput rather than loop-carried latency, and triggers `checkasm_simd_warmup()` to prevent AVX frequency-scaling skew.

### 6. Core Structural Invariants and Clean-Rewrite Verification Implications

Basis: source + derived

Three low-level memory and ABI contracts permeate `libavutil`, `libavcodec`, `libavfilter`, and `libswscale`:
1. **`AV_INPUT_BUFFER_PADDING_SIZE = 64` (`libavcodec/defs.h`, line 40):** Every encoded packet or extradata buffer passed to bitstream/CABAC readers must be padded with `64` trailing zero bytes so 32/64-bit lookahead loads (`movzwl` in `x86/cabac.h` line 46, `AV_RB32`/`AV_RB64` in `get_bits.h`) never fault when crossing buffer end.
2. **Signed `int linesize` & negative-stride vertical inversion (`libavutil/frame.h`, lines 496–524):** `AVFrame.data[i]` may point to the *last* scanline while `linesize[i]` is *negative* (`ptrdiff_t stride` in DSP signatures), requiring signed pointer arithmetic (`pix + y * stride`) rather than unsigned offsets. `linesize` is aligned to `av_cpu_max_align()` (`64` for AVX-512, `32` for AVX2, `16` for SSE/NEON).
3. **`STRIDE_ALIGN` (`libavcodec/internal.h`, lines 39–47):** Compile-time alignment macro (`64` if `HAVE_SIMD_ALIGN_64`, else `32` or `16` or `8`) governing internal picture-buffer planes, plus `avpriv`/`AVFrame` rule (`frame.h`, lines 490–492) that filters and `libswscale` may read up to `16` bytes past plane boundaries.

**Verification Priority Stack Assessment (Derived):**

| Priority Tier | Legacy FFmpeg C / Asm Reality | Clean-Room Verified Rust Rewrite Implication |
| :--- | :--- | :--- |
| **1. UB-Freedom** | Relies on unchecked raw pointer arithmetic (`int` `linesize` -> `ptrdiff_t`), unguarded 64-byte packet tail reads, `SUINT` workarounds, and `193,803` LOC of handwritten `.asm`/`.S` + `567` inline `__asm__` sites. | Rust safe slices/typed buffers eliminate spatial UB in demuxers/headers (`libavformat`, `libavcodec` CBS, `fftools`), which are **historical C accidents**. Conversely, external `.asm`/`.S` SIMD kernels (`~2,550+` functions) and `cabac` inline asm remain **hardware-mandated FFI/asm TCB surfaces** requiring formal ISA models (`x86_64`, `aarch64`, `riscv64`) or verified portable SIMD lowering. |
| **2. Panic-Freedom** | C omits bounds checks or aborts on fatal programmer invariants (`av_assert0`). Naive Rust slice indexing (`buf[i]`) and signed arithmetic convert C UB into runtime panics on malformed media. | Every bitstream slice, negative-stride frame view, and `DSPContext` index must carry proven bounds invariants (e.g., `slice::chunks_exact` / explicit checked bounds returning `Result<_, DecodeError>`) so adversarial inputs never trigger `panic!`. |
| **3. Behavioral & SIMD-vs-Scalar Equivalence** | `DSPContext` C fallback vs SIMD variants is empirically differential-tested by `checkasm` (`103` suites) on random seeds (`checkasm_rand`) + `BUF_RECT` padding, NOT exhaustively proven. | Replacing `DSPContext` runtime vtables with Rust traits + `is_x86_feature_detected!`/`cpufeatures` preserves identical dynamic dispatch while enabling **static machine-checked equivalence proofs** between pure scalar Rust reference kernels and SIMD/asm implementations (replacing sampling-based `checkasm` coverage with exhaustive quantifier-free/SMT/Lean proofs). |
| **4. Spec Conformance** | Tested via FATE (`5,855` files in `tests/`) against reference bitstreams; `libavcodec` mixes spec parsing and decoder state machines in monolithic C files. | `libavcodec/cbs*` (`40` files) and `libswscale/ops.h` demonstrate that FFmpeg itself is moving toward declarative IRs and separate syntax/semantic layers—matching a clean Rust split between verified bitstream parsers and verified DSP kernels. |

## Boundaries

- **Runtime cycle and microarchitectural throughput measurements (`not examined`):** All architectural counts, macro expansions, and dispatch invariants were obtained via static source inspection of `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`. Actual `checkasm --bench` cycle ratios across AVX2, AVX-512ICL, NEON, SVE, and RVV hardware were not executed in this investigation.
- **Third-party external codecs and binary GPU blobs (`not examined`):** External library bindings (`libx264`, `libx265`, `libdav1d`, `libvpx`, `libaom`, `libopus`, `zlib`, `openssl`) and vendor runtime drivers (`NVDEC`, `VA-API`, `VideoToolbox`, `MediaCodec`) live outside FFmpeg's tree and were excluded from the file/LOC census beyond FFmpeg's `libavcodec/*` wrapper counts.
- **Line-count vs macro-expansion multiplicity (`known not to apply` as executed binary size):** On `x86`, a single `.asm` kernel wrapped in `INIT_XMM sse2` / `INIT_XMM ssse3` / `INIT_YMM avx2` expands into multiple compiled functions (`942` `cglobal` declarations instantiate more than `942` binary symbols when iterated inside `%macro` loops, whereas compiled binary object sizes depend on `--disable-mmx`/`--disable-avx512`/architecture flags).
- **Non-x86 `checkasm` `check_vzeroupper` / `emms` invariants (`known not to apply`):** `check_vzeroupper` and `fstenv` tag-word checks in `tests/checkasm/ext/src/x86/checkasm.asm` are x86-specific; AArch64, RISC-V, and LoongArch `checkasm` trampolines verify GPR, FPR/vector CSRs, and stack redzones only.
- **WASM runtime dynamic CPU detection (`unsupported`):** As observed in `libavutil/wasm/cpu.c` (lines 25–32), WebAssembly lacks runtime CPU feature probing; `AV_CPU_FLAG_SIMD128` is strictly a compile-time `#if HAVE_SIMD128` flag.

## Evidence

- **Primary source repository:** `FFmpeg/FFmpeg`, pinned commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (committed `2026-11-20T01:06:10Z`), tree fetched via GitHub REST API (`11,417` total entries, `11,284` blobs, `94,826,996` bytes) and unpacked from the pinned commit tarball on `2026-11-20`.
- **Library versions & DAG (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`):**
  - `RELEASE` (`8.0.git`), `libavutil/version.h` (`LIBAVUTIL_VERSION_MAJOR 61`, `MINOR 21`, `MICRO 100`), `libavcodec/version_major.h` (`63`), `libavformat/version_major.h` (`63`), `libavfilter/version_major.h` (`12`), `libavdevice/version_major.h` (`63`), `libswscale/version_major.h` (`10`), `libswresample/version_major.h` (`7`).
  - `configure` (`*_deps` declarations; `0` occurrences of `postproc`).
  - `libswscale/ops.h` (lines 36–70, `SwsOpType`); `fftools/ffmpeg_sched.h` (lines 31–101, `Scheduler` DAG).
- **Assembly abstraction & ISA detection sources:**
  - `libavutil/x86/x86inc.asm` (1,978 lines; `required_stack_alignment`, `vzeroupper_required` line 374, `PROLOGUE`/`WIN64_SPILL_XMM` lines 482–621, `cglobal` lines 820–861, `INIT_CPUFLAGS`/`INIT_MMX`/`INIT_XMM`/`INIT_YMM`/`INIT_ZMM` lines 944–1145, `RUN_AVX_INSTR` lines 1352–1420).
  - `libavutil/aarch64/asm.S` (492 lines), `libavutil/arm/asm.S` (430 lines), `libavutil/riscv/asm.S` (257 lines), `libavcodec/loongarch/loongson_asm.S` (945 lines).
  - `libavutil/cpu.h` (lines 32–154), `libavutil/cpu.c` (lines 56–327), `libavutil/cpu_internal.h` (lines 26–66), `libavutil/x86/cpu.c` (lines 80–301), `libavutil/x86/cpu.h` (lines 25–109), `libavutil/aarch64/cpu.c` (lines 27–264), `libavutil/aarch64/cpu.h` (lines 25–48), `libavutil/aarch64/cpu_sve.S` (lines 1–29), `libavutil/aarch64/cpu_sme.S` (lines 1–31), `libavutil/riscv/cpu.c` (lines 52–153), `libavutil/riscv/cpu.h` (lines 30–80), `libavutil/wasm/cpu.c` (lines 25–41).
- **`DSPContext`, inline asm, `checkasm`, and structural invariants:**
  - `libavcodec/h264dsp.h` (lines 42–137), `libavcodec/h264dsp.c` (lines 66–170), `libavcodec/x86/h264dsp_init.c` (lines 180–335), `libavcodec/aarch64/h264dsp_init_aarch64.c` (lines 109–166), `libavcodec/riscv/h264dsp_init.c` (lines 101–233), `libavcodec/vvc/dsp.h` (lines 47–186).
  - `libavcodec/x86/cabac.h` (lines 45–209), `libavcodec/aarch64/cabac.h` (lines 30–100), `libavcodec/x86/mathops.h` (lines 34–150).
  - `libavcodec/defs.h` (line 40, `AV_INPUT_BUFFER_PADDING_SIZE 64`), `libavcodec/internal.h` (lines 39–47, `STRIDE_ALIGN`), `libavutil/frame.h` (lines 479–525, `AVFrame.data`/`linesize`).
  - `tests/checkasm/checkasm.h` (lines 33–160), `tests/checkasm/checkasm.c` (lines 57–429), `tests/checkasm/ext/include/checkasm/test.h` (lines 77–664), `tests/checkasm/ext/include/checkasm/utils.h` (lines 483–775, `BUF_RECT`), `tests/checkasm/ext/src/checkasm.c` (lines 552–614), `tests/checkasm/ext/src/x86/checkasm.asm` (lines 143–420), `tests/checkasm/ext/src/arm/checkasm_64.S` (lines 100–120), `tests/checkasm/ext/src/riscv/callcheck.S` (lines 34–90), `tests/checkasm/ext/src/loongarch/checkasm.S` (lines 59–90).

## Revalidation

To reproduce or revalidate the structural and assembly census against another `FFmpeg/FFmpeg` revision `<REV>`:

1. **Recompute exact file/byte/LOC and ISA matrices from the tarball of `<REV>`:**
   ```bash
   curl -sSL --http1.1 "https://github.com/FFmpeg/FFmpeg/archive/<REV>.tar.gz" -o /tmp/ffmpeg.tar.gz
   mkdir -p /tmp/ffmpeg_rev && tar -xzf /tmp/ffmpeg.tar.gz -C /tmp/ffmpeg_rev --strip-components=1
   python3 - <<'PY'
   import collections, pathlib, re
   src = pathlib.Path("/tmp/ffmpeg_rev")
   isas = ("x86", "aarch64", "arm", "riscv", "ppc", "loongarch", "mips", "wasm")
   for isa in isas:
       files = [p for p in src.rglob("*") if p.is_file() and isa in p.parts[1:-1] and "tests" not in p.parts[:1]]
       asm = [p for p in files if p.suffix in (".asm", ".S")]
       c_files = [p for p in files if p.suffix == ".c"]
       asm_loc = sum(len(p.read_bytes().splitlines()) for p in asm)
       c_loc = sum(len(p.read_bytes().splitlines()) for p in c_files)
       print(f"{isa:10s}: asm/S={len(asm):3d} ({asm_loc:6d} LOC), arch.c={len(c_files):3d} ({c_loc:6d} LOC)")
   PY
   ```
2. **Verify x86 `xgetbv`/XCR0 gating, `AV_INPUT_BUFFER_PADDING_SIZE`, and `checkasm` ABI invariants:**
   Inspect `libavutil/x86/cpu.c` for `xgetbv` XCR0 bitmasks (`0x6` for AVX, `0xe0` for AVX-512), `libavcodec/defs.h` for `AV_INPUT_BUFFER_PADDING_SIZE`, and run on a configured build host:
   ```bash
   ./configure --enable-gpl && make -j"$(nproc)" tests/checkasm/checkasm
   ./tests/checkasm/checkasm --verbose
   ```
   A clean exit (`0`) across all registered `checkasm` suites establishes bit-exact / ULP-bounded parity and ABI/stack-redzone/register/state preservation for the configured host ISA.
