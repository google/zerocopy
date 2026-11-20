# AVX-512 EVEX Opmask and Armv9 SVE2/SME2 Scalable-Vector Object-Level Lifting and Pass-2 ISA Correspondence

## Summary

Extending object-level binary lifting and sandboxed Pass-2 instruction-set correspondence from fixed-width 128/256-bit SIMD (`SSE2`–`AVX2`, `NEON`) to masked 512-bit **`x86-64` `AVX-512ICL` / `AVXVNNI`** and scalable **`Armv9-A` `SVE2` / `SME2`** media kernels exposes sharp decoder, ABI, and specification-slicing boundaries across upstream multimedia codebases and formal ISA models (`Basis: source + normative + execution + derived`):

1. **x86-64 `EVEX` and `AVX-VNNI` Formal Model Gap (`Basis: source + execution`):**
   - Neither `awslabs/s2n-bignum` (`280a220986a0bc6249248187717a771153d073db`) nor ACL2 `x86isa` (`acl2/acl2@08bec1884997560686932229dbfe458c1bba34bf`, `rems-project/sail-x86-from-acl2@0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf`) currently decodes and executes a single `AVX-512ICL` or `AVX-VNNI` media opcode end-to-end. In ACL2 `x86isa`, `evex-decode-and-execute` (`evex-opcodes-dispatch.lisp:202-343`) decodes the 4-byte `0x62` prefix and `inst-listing.lisp` enumerates `1,375` `:EVEX` entries, yet **zero (`0`)** supply a semantic execution function (`NIL` in all `1,375` rows, falling through to `"Opcode Unimplemented in x86isa!"`), while `VPDPBUSD` and `VPSHUFBITQMB` have `0` entries altogether. Conversely, `awslabs/s2n-bignum` mechanizes the complete reusable `EVEX` semantic and address-scaling substrate in HOL Light—`zmm0..zmm31`, `kmask0..kmask7`, `evex_mask`, `apply_evex_masking`, `evex_src`, `evex_tuple_disp_scale`, `read_EVEX`, and `read_EVEX_ModRM` (`x86/proofs/{instruction,decode,x86}.ml`)—but has **not yet wired `[0x62:8]` into `decode_aux`** (`decode.ml:777-860`) or `[0x50:8]` (`VPDPBUSD`) into `VEXM_0F38` (`decode.ml:860-1015`).
   - Closing x86-64 `AVX-512ICL` and `AVXVNNI` at Pass 2 requires pairing XED's authoritative per-iform legality tables (`intelxed/xed@0bcb6237345c5066726dcc08b3d87928df3b5b26`)—which catch `#UD` traps that even `GNU objdump 2.47` mis-disassembles, such as illegal `EVEX.b = 1` broadcast on byte-granular `VPERMB` (`62 e2 55 d2 8d 67 01`)—with an explicit extension of `s2n-bignum`'s `EVEX` combinators covering `VPDPBUSD`/`VPDPWSSD` (both `VEX` and `EVEX`), `VPERMB`, `VPERMI2B`/`VPERMT2B`, `VPTERNLOGD`/`Q`, `VPMADD52LUQ`/`HUQ`, `VPSHUFBITQMB`, `VPMULTISHIFTQB`, `VMOVDQU8/16/32`, `VPCMPUB`, and `VEX`-coded `KMOVB/W/D/Q`.

2. **Armv9 `SVE2` / `SME2` Correspondence: Finite Power-of-Two `SVL` Specialization vs. Sliced `sail-arm` Extraction (`Basis: source + normative + derived`):**
   - Monolithic `sail -lean` extraction of `rems-project/sail-arm` (`5416ef6b43e9527c38dc71fb752259c1d01a47e1`) injects `sorryAx` via `lean/ArmExtras.lean:19-23` solely because all `22` `while`/`repeat` termination measures in `src/termination_measures.sail:43-116` (including `ImplementedSVEVectorLength`, `ImplementedSMEVectorLength`, and `decode_max_smeveclen`) are guarded under `$iftarget coq`. An exhaustive scan of all `195,233` lines of `v8_base.sail`, `instrs64_sve.sail`, and `instrs64_sme.sail` proves that **`instrs64_sme.sail` (`42,546` lines) contains `0` `while`/`repeat` loops** and **`instrs64_sve.sail` (`95,548` lines) contains exactly `1`** (`execute_PNEXT_P_P_P__:31051`), because every scalable lane loop uses bounded `foreach` and every decoder already case-splits over the **5 power-of-two vector lengths `{128, 256, 512, 1024, 2048}`** (`prelude.sail:349`).
   - By contrast, unpatched `UQ-PAC/ASLp` (`92e4fd949402056e16e3747e66922060be57ecc8`) unconditionally lowers `Stmt_While` and `Stmt_Repeat` to `assert FALSE` (`libASL/dis.ml:1413-1416`)—breaking `Implemented{SVE,SME}VectorLength` for every `VL > 128` unless `CurrentVL` is stubbed—rejects dynamic bit-slice offsets in `ZT0` `LUTI2`/`LUTI4` (`libASL/rASL_check.ml:266`), and carries proprietary Arm XML redistribution constraints when run over raw MRA XML. Consequently, **per-opcode EL0 slicing of `BSD-3-Clause-Clear` `rems-project/sail-arm`** (with MMU/FP `while` walkers excluded and `4`-line `Nat` termination proofs on `Implemented{SVE,SME}VectorLength`) provides a `100%` `sorry`-free Pass-2 Lean 4 oracle, while **finite case-splitting over the `5` architectural SME `SVL` powers of two** (`256..2048` bits for 4-vector `.d` kernels) discharges Pass-1 kernel equivalence without inductive `VL` quantifiers.

3. **Three Concrete Upstream Armv9 `SME2` Bugs Uncovered in `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (`Basis: source + normative + execution`):**
   - **`SVL == 128` `SIGILL` (`Error_Undefined`) Trap:** `libavcodec/aarch64/vvc/inter_sme2.S:232, 239, 264, 272, 292, 300, 516, 523` executes 4-register 64-bit `zip {z12.d-z15.d}, {z12.d-z15.d}`, whose normative semantics (`execute_ZIP_MZ_Z_4`, `instrs64_sme.sail:35049-35051`) throws `Error_Undefined()` whenever `VL < 4 * 64 = 256` bits, yet `libavcodec/aarch64/vvc/dsp_init.c:327, 382, 438` dispatches `alf_filter_luma_{8,10,12}_sme2` without checking `SVL >= 256` bits (`ff_aarch64_sme_length() >= 32`).
   - **AAPCS64 `TPIDR2_EL0` Lazy-Save Violation and First-Strip `ZA` Pixel Corruption:** `sme_entry` (`libavutil/aarch64/asm.S:352-361`) executes `smstart` without checking `TPIDR2_EL0` or calling `__arm_tpidr2_save` (`ARM-software/abi-aa@9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7`, `aapcs64/aapcs64.rst:2648-2654`). When entered with dormant caller `ZA` state (`PSTATE.ZA == 1`, `TPIDR2_EL0 != NULL`), `SetPSTATE_ZA(0b1)` (`v8_base.sail:29627`) is a no-op that **does not zero `_ZA`**, causing `inter_sme2.S` (which executes `zero {za}` only at the *end* of the inner loop at lines `341` and `626`) to accumulate VVC Adaptive Loop Filter dot products onto the caller's live `ZA` bytes (`127/256` pixels corrupted at `SVL = 512`), before `sme_exit`'s `smstop` wipes `ZA` while leaving `TPIDR2_EL0` non-null.
   - **Callee-Saved `d8..d15` Clobber in `ff_aarch64_sme_length`:** `libavutil/aarch64/cpu_sme.S:26-31` executes bare `smstart; cntb x0; smstop; ret` without saving `d8..d15`, zeroing AAPCS64 callee-saved `d8..d15` via `ResetSVEState()` (`v8_base.sail:9504-9507`) instead of executing streaming-free `rdsvl x0, #1`.

---

## Applicability

This report governs relocatable object-level binary lifting (`.o` / `.obj`), instruction-decoder legality checking, ABI frame verification, and two-pass TCB correspondence (`Pass 1` symbolic kernel verification + `Pass 2` sandboxed golden ISA replay) for masked 128/256/512-bit `x86-64` (`AVX-512F/CD/BW/DQ/VL`, `AVX-512ICL`, `AVX-VNNI`) and scalable `Armv9-A` (`SVE`, `SVE2`, `SME`, `SME2`, `SME_I16I64`) user-space media kernels.

Relationships among examined subjects in `REPORT.json`:
- **`FFmpeg/FFmpeg`** (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) and **`videolan/dav1d`** (`2a0775ca5ea055450bdfbfe81758a3c9e001f58a`) define the concrete production multimedia instruction census, macro frameworks (`libavutil/x86/x86inc.asm`, `libavutil/aarch64/asm.S`), VVC SME2 Adaptive Loop Filter kernels (`libavcodec/aarch64/vvc/inter_sme2.S`), and AV1 AVX-512ICL / SVE2 kernels (`src/x86/{cdef,filmgrain,looprestoration,mc}_avx512.asm`, `src/arm/64/mc16_sve.S`).
- **`joshlf/anneal`** (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) defines the two-pass TCB architecture (`trusted/audit/TrustedBoundary.lean` and `trusted/audit/src/lib.rs`) whose Pass-2 `CorrOrigin` sandboxed replay mechanism connects compact Pass-1 `BitVec` evaluators to external golden ISA models.
- **`intelxed/xed`** (`0bcb6237345c5066726dcc08b3d87928df3b5b26`), **`awslabs/s2n-bignum`** (`280a220986a0bc6249248187717a771153d073db`), **`acl2/acl2`** (`08bec1884997560686932229dbfe458c1bba34bf`), and **`rems-project/sail-x86-from-acl2`** (`0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf`) are audited against **Intel SDM (`325462`)** to establish exact x86-64 `EVEX` / `AVX-VNNI` coverage and fail-closed extension rules.
- **`rems-project/sail-arm`** (`5416ef6b43e9527c38dc71fb752259c1d01a47e1`), **`UQ-PAC/ASLp`** (`92e4fd949402056e16e3747e66922060be57ecc8`, **FMCAD 2023** DOI `10.34727/2023/isbn.978-3-85448-060-0_36` and **SAS 2024** DOI `10.1007/978-3-031-74776-2_4`), **`leanprover/LNSym`** (`49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`), and **`ARM-software/abi-aa`** (`9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7`) are audited against **Arm ARM (`ARM DDI 0487`)** and **ITU-T H.266 (`VVC`)** for `SVE2`/`SME2` lifting and `TPIDR2_EL0` ABI soundness.

Companion corpus packages cited rather than duplicated:
- `x86-64-and-aarch64-simd-isa-formalizations-sail-asl-acl2-hol-k-comparison` for baseline SSE2/AVX2/NEON model comparisons and `PSHUFB` vs `TBL` / `PMADDUBSW` vs `VPDPBUSD` lane-level traps;
- `object-level-asm-lifting-core-arch-llvm-lowering-and-pass2-isa-correspondence` for `core::arch` MIR-to-object lowering, baseline ELF/COFF/Mach-O relocation formulas, `endbr64`/`BTI` CFI landing pads, Win64 `.pdata`/`.xdata` unwind checking, and RVV `sail-riscv-lean` patches;
- `ffmpeg-codebase-architecture-cpuflags-dispatch-and-asm-corpus-census` and `vvc-h266-qtbt-mtt-lfnst-alf-lmcs-and-scoreboard-ctu-dag-anatomy` for global FFmpeg dispatch tables and VVC H.266 decoder pipeline structure;
- `riscv-rvv-ppc-vsx-loongarch-and-wasm-simd-isa-formalizations` for non-x86/Arm vector ISAs.

---

## Findings

### 1. FFmpeg and dav1d Masked and Scalable-Vector Media Workload Census

`Basis: source + normative`

An exhaustive scan of all `188` `x86/*.asm` files, `72` `aarch64/*.S` files, and architecture `cpu.{c,h}` / `dsp_init.c` dispatchers in `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, paired with `videolan/dav1d@2a0775ca5ea055450bdfbfe81758a3c9e001f58a` (`src/x86/*_avx512.asm`, `src/arm/64/mc16_sve.S`), establishes the exact hardware capability bundles and instruction inventory that an object-level verifier must cover:

1. **x86-64 Capability Bundles and OS `XCR0` State Gating (`FFmpeg` `libavutil/x86/cpu.c:143-184`, `x86inc.asm:966-967`, XED `datafiles/icl/icl-chips.txt:20-56`):**
   - **`AV_CPU_FLAG_AVX512` (Skylake-X baseline):** Requires OS `XGETBV(0)` `(xcr0_lo & 0xe6) == 0xe6` (`XMM` bit 1, `YMM_Hi128` bit 2, `opmask k0..k7` bit 5, `ZMM_Hi256` bit 6, `Hi16_ZMM` `zmm16..zmm31` bit 7; `cpu.c:144, 159`) plus `CPUID.(EAX=7,ECX=0):EBX & 0xd0030000 == 0xd0030000` (`AVX512F`, `AVX512DQ`, `AVX512CD`, `AVX512BW`, `AVX512VL`; `cpu.c:160`). Sets `av_cpu_max_align()` to `64` bytes (`cpu.c:278-279`).
   - **`AV_CPU_FLAG_AVX512ICL` (Ice Lake / Zen 4+ media target):** Adds `EBX` bit 21 (`AVX512_IFMA`, mask `0xd0200000`) and `ECX & 0x5f42 == 0x5f42` (`AVX512_VBMI` bit 1, `AVX512_VBMI2` bit 6, `GFNI` bit 8, `VAES` bit 9, `VPCLMULQDQ` bit 10, `AVX512_VNNI` bit 11, `AVX512_BITALG` bit 12, `AVX512_VPOPCNTDQ` bit 14; `cpu.c:163`). Almost all FFmpeg integer media AVX-512 kernels gate on `HAVE_AVX512ICL_EXTERNAL` rather than Skylake-X `AVX512` because cross-lane byte permutation (`vpermb`, `vpermi2b`) and 8-bit/16-bit dot products (`vpdpbusd`, `vpdpwssd`) only enter at `AVX512ICL`.
   - **`AV_CPU_FLAG_AVXVNNI` (Alder Lake / Raptor Lake / Arrow Lake VEX dot-product extension):** Gates on `AV_CPU_FLAG_AVX` (`(xcr0_lo & 0x6) == 0x6`, **no** `XCR0[7:5]` opmask/ZMM state required!) and `CPUID.(EAX=7,ECX=1):EAX[4]` (`0x10`, `cpu.c:177-183`). Although `libavutil/x86/cpu.h:49, 80` defines `X86_AVXVNNI` and `EXTERNAL_AVXVNNI`, `FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` currently contains **zero (`0`)** first-party `.asm` or `.c` DSP consumers of `AVXVNNI`; supporting it in clean-room Rust `core::arch` (`#[target_feature(enable = "avxvnni")]`) or NASM (`{vex} vpdpbusd`) allows 256-bit VNNI acceleration on hybrid Alder/Raptor Lake CPUs where `AVX-512` is fused off.

2. **Concrete x86-64 `AVX-512` / `AVX-512ICL` Instruction Census Across FFmpeg and dav1d:**
   - **Dot Products (`AVX512_VNNI` / `AVX_VNNI`):** `vpdpbusd` (`u8 * i8 -> i32` 4-way MAC in `libavcodec/x86/vp9mc.asm:861-865, 952-953, 1404-1494`, `libavcodec/x86/hevc/mc.asm:1288-1289`, `dav1d` `src/x86/{cdef,ipred,looprestoration}_avx512.asm:201, 233, 211`) and `vpdpwssd` with embedded 32-bit broadcast (`vpdpwssd m%2, m%1, [o(pw_%5)] {bcstd}` in `libavcodec/x86/vp9itxfm_avx512.asm:159`).
   - **Full-Crossbar Byte & Qword Permutations (`AVX512_VBMI` / `AVX512F`):** `vpermb` (`68` sites across `libavcodec/x86/{bitpacked,vp9mc,vp9itxfm_avx512,hevc/mc,v210enc}.asm` and `libswscale/x86/rgb_2_rgb.asm`; note `v210enc.asm:59`: `vpermb does not set bytes to zero when the high bit is set unlike pshufb`), two-source overwriting `vpermi2b` / `vpermt2b` (`libswscale/x86/rgb_2_rgb.asm:231`, `dav1d` `src/x86/{cdef,filmgrain,mc}_avx512.asm:177, 319-322, 1144`), and `vpermi2q` / `vpermt2q` (`vp9itxfm_avx512.asm:547-556, 768-826`).
   - **3-Input Bitwise Truth-Table Logic (`AVX512F`):** `vpternlogd` (`libavcodec/x86/v210enc.asm:331` with `0xd8`; `dav1d` `src/x86/looprestoration_avx512.asm:205` `vpternlogd m16, m0, [r0+r10+0], 0xe4 ; c ? a : b`) and `vpternlogq` (`libavfilter/x86/vf_colordetect.asm:54` with `0xF6`).
   - **Bit-Shuffle to Opmask & Sub-Byte Bitfield Extract (`AVX512_BITALG` / `AVX512_VBMI`):** `vpshufbitqmb k1, m8, m2` (`dav1d` `src/x86/cdef_avx512.asm:254, 265, 268`, extracting 64 arbitrary bit positions from eight 64-bit lanes directly into a 64-bit opmask `k1`) and masked `vpmultishiftqb m14{k7}, m13, m8` (`FFmpeg` `vp9itxfm_avx512.asm:193-196, 281-282, 757-758`).
   - **52-Bit Unsigned Integer Fused Multiply-Add (`AVX512_IFMA`):** `vpmadd52luq` / `vpmadd52huq` (bundled in `AV_CPU_FLAG_AVX512ICL` via `EBX[21]` and `icl-chips.txt:26-28`; used in external crypto/checksum pipelines and high-precision polynomial evaluators, with `0` current video-pixel sites in `FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`).
   - **Predicated Byte/Word/Dword Loads, Stores, Comparisons, and Opmask Moves (`AVX512BW` / `AVX512DQ`):** `vmovdqu8 m0{k2}{z}, [srcq]` (`bitpacked.asm:220`), `vmovdqu16 [ydstq + wq]{k1}, m6` (`rgb_2_rgb.asm:232`), `vmovdqu32 m1{k7}{z}, [srcq + wq]` (`rgb_2_rgb.asm:81`), `vpcmpub k7, m13, m10, 6` (`vp9itxfm_avx512.asm:446`), `vpblendmb` / `vpblendmd` (`ops_common.asm:222`, `v210.asm:173`), and VEX-encoded `kmovb k1, r6d` (`vp9mc.asm:1192`).

3. **Concrete Armv9 `SVE2` and `SME2` Census Across FFmpeg and dav1d:**
   - Despite declaring `AV_CPU_FLAG_SVE` and `AV_CPU_FLAG_SVE2` (`libavutil/aarch64/cpu.c:56-59`) and `ff_aarch64_sve_length` (`libavutil/aarch64/cpu_sve.S:26-29`), `FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` contains **zero (`0`)** non-streaming SVE/SVE2 DSP `.S` kernels in `libavcodec/aarch64/`, `libavfilter/aarch64/`, or `libswscale/aarch64/`; non-streaming SVE2 in the FFmpeg ecosystem enters via `videolan/dav1d@2a0775ca5ea055450bdfbfe81758a3c9e001f58a` (`src/arm/64/mc16_sve.S:33-325`, interleaving `ptrue p0.b, vl16`, `whilelt p1.h, wzr, w`, `ld1sb {z7.h}, p0/z`, and `sdot z0.d, z16.h, z7.h[0..1]` with 128-bit NEON `zip1/2`, `tbl`, `uzp1`, and `sqrshrun`).
   - Conversely, FFmpeg jumps directly to **Armv9.2-A `SME2` + `SME_I16I64`** in `libavcodec/aarch64/vvc/inter_sme2.S:25-651`, implementing `ff_vvc_alf_filter_luma_{8,10,12}_sme2` inside Streaming SVE + `ZA` active mode (`smstart` .. `smstop`) using multi-vector `add`, 4-way `zip`, `sclamp`, 4-vector `sdot za.d[w10, idx]` (`i16 -> i64`), `mova` (`ZA` array to 4 `Z` registers), 4-vector narrowing `sqrshr`, `zero {za}`, and predicated `ld3h`/`ld1b`/`ld1h`/`st1b`/`st1h`.

---

### 2. x86-64 EVEX 4-Byte Decoding, Opmask Semantics, Tuple Scaling, and #UD Boundaries

`Basis: normative + source + execution`

An object-level lifter for `AVX-512ICL` and `AVXVNNI` cannot treat `EVEX` (`0x62`) as a wider `VEX` prefix. Direct inspection of `intelxed/xed@0bcb6237345c5066726dcc08b3d87928df3b5b26` (`datafiles/avx512f/{avx512-evex-dec,evex-maps,avx512-disp8,avx512-kregs,avx512-reg-table-mask}.txt`, `datafiles/{vnni/vnni,avx-vnni/avx-vnni,avx512vbmi/vbmi,avx512ifma/ifma,bitalg/bitalg,avx512-skx/skx}-isa.xed.txt`) and assembly execution on Linux `x86_64` (`gcc (Debian 15.2.0-14) 15.2.0`, `GNU Binutils 2.47`) establishes six mandatory decoding and legality invariants:

#### 2.1 Four-Byte `EVEX` (`0x62 P0 P1 P2`) vs. Three-Byte `VEX` (`0xC4`) and Two-Byte `VEX` (`0xC5`)

In 64-bit mode (`CS.L = 1`), `0x62` introduces a 4-byte prefix `[0x62, P0, P1, P2]` preceding `[opcode, ModR/M, SIB?, disp8/32?, imm8?]`, subject to immediate prefix-level `#UD` if preceded by any `LOCK` (`0xF0`), `66h`, `F2h`, `F3h`, or `REX` (`0x40..0x4F`) prefix (`acl2/acl2` `evex-opcodes-dispatch.lisp:241-250`, `s2n-bignum` `decode.ml:384-395`):
- **`P0 = [R : 1 | X : 1 | B : 1 | R' : 1 | 0 : 1 | mmm : 3]` (note bit 3 in `AVX512F`/`ICL` must be `0`, extended to `B4` only in `APX`):** `R, X, B, R'` are stored **bitwise inverted** (`1` = 0, `0` = +8/+16). For SIMD destinations in `ModR/M.reg`, the 5-bit register index (`0..31`) is `(~R' << 4) | (~R << 3) | reg`. For SIMD register operands in `ModR/M.rm` (`ModR/M.mod == 0b11`), the 5-bit index is `(~X << 4) | (~B << 3) | rm` (`s2n-bignum` `decode.ml:297`), whereas for GPR base/index addressing (`ModR/M.mod != 0b11` or GPR `rm`), `EVEX.X` extends only `SIB.index` (`decode.ml:308`). `mmm` selects opcode map `1` (`0F`), `2` (`0F38`), `3` (`0F3A`), `5` (`MAP5` FP16), or `6` (`MAP6` FP16); `mmm ∈ {0, 4, 7}` raises `#UD`.
- **`P1 = [W : 1 | vvvv : 4 | 1 : 1 | pp : 2]`:** Bit 2 (`UBIT=1` in XED) **must equal `1`** in 64-bit mode (`0` raises `#UD`). The 5-bit `NDS`/`NDD` register index is `(~V' << 4) | (~vvvv)`. `pp` encodes synthetic mandatory prefix `00=NP`, `01=66`, `10=F3`, `11=F2`.
- **`P2 = [z : 1 | L'L : 2 | b : 1 | V' : 1 | aaa : 3]`:** `z` selects merging (`0`) vs zeroing (`1`); `L'L` selects vector length `00=128`, `01=256`, `10=512` (`11` raises `#UD` unless `b = 1` enables static rounding `{rn-sae}`..`{rz-sae}` on register-register `512`-bit FP ops, `avx512-evex-dec.txt:19-24`); `b` (`BCRC`) enables embedded broadcast `{1toN}` on memory operands or `{sae}` on scalar/512-bit FP register ops; `V'` is inverted bit 4 of `vvvv` (or inverted bit 4 of VSIB index in gather/scatter); `aaa` selects opmask `k0..k7`.

Two dual-space encoding subtleties affect `AVX-512ICL` and `AVXVNNI` kernels directly:
1. **`VPDPBUSD` Dual `VEX` / `EVEX` Encoding (`avx-vnni-isa.xed.txt:29-81` vs `vnni-isa.xed.txt:30-115`):** Assembling `{vex} vpdpbusd ymm1, ymm2, ymm3` emits 5 bytes `c4 e2 6d 50 cb` (`VEX.256.66.0F38.W0 50 /r`, limited to `xmm0..15`/`ymm0..15`, unmasked, no embedded broadcast, full byte displacement), whereas `{evex} vpdpbusd ymm1, ymm2, ymm3` emits 6 bytes `62 f2 6d 28 50 cb` (`EVEX.256.66.0F38.W0 50 /r`, supporting `zmm0..31`, `{k1}`/`{k1}{z}`, `{1to8}`/`{1to16}` 32-bit broadcast, and `disp8 * N` scaling).
2. **Opmask Moves and Logic Are `VEX`-Encoded, Not `EVEX`-Encoded (`skx-isa.xed.txt:27489-27567`):** Instructions manipulating `k0..k7` directly (`kmovb/w/d/q`, `kortest*`, `kunpck*`, `kand*`, `kor*`, `kxor*`, `kshift*`) use 2-byte/3-byte **`VEX` prefixes** (`c5 f9 92 c8` for `kmovb k1, eax`, `PATTERN: VV1 0x92 V66 V0F ... W0 VL128`). An object lifter that enables `k0..k7` only inside its `0x62` `EVEX` decoder fails immediately on `vp9mc.asm:1192` (`kmovb k1, r6d`).

#### 2.2 `k0..k7` Dual Semantics, Implicit Opmask-Destination Zeroing, and `#UD` Legality Matrix

XED's `datafiles/avx512f/avx512-reg-table-mask.txt:20-69` and per-iform `PATTERN` constraints show that `k0` and `EVEX.z` obey four distinct rules depending on operand role:

| Operand / Instruction Class | `EVEX.aaa = 000` (`k0`) Behavior | `EVEX.aaa = 001..111` (`k1..k7`) with `z = 0` | `EVEX.z = 1` (`{z}`) Legality & Semantics | Register-Index Extension Bits (`EVEX.R`, `EVEX.R'`, `VEX.vvvv[3]`) |
| :--- | :--- | :--- | :--- | :--- |
| **Vector register write (`VPDPBUSD`, `VPERMB`, `VPTERNLOGD`, `VPMADD52LUQ`, `VMOVDQU8` load)** | **Unmasked sentinel:** `k0` register value is **ignored**; behaves as all-ones mask (`MASK1()`). **`z = 1` (`{k0}{z}`) raises `#UD`!** | **Merging (`{k1}`):** Inactive elements (`k[i] = 0`) retain prior `dst[i]`; bits `[511:VL]` zeroed. | **Valid (`{k1}{z}`):** Inactive elements (`k[i] = 0`) zeroed (`dst[i] := 0`); bits `[511:VL]` zeroed. | 5-bit `ZMM` index `(~R' << 4) \| (~R << 3) \| reg` (`0..31` all legal). |
| **Masked memory store (`VMOVDQU8/16/32/64 [mem]{k1}, zmm`, `skx-isa.xed.txt:8714`)** | **Unmasked store:** All `VL / esize` elements written to memory. **`z = 1` raises `#UD`!** | **Predicated store:** Only active bytes/elements (`k[i] = 1`) written and fault-checked in memory; inactive lanes suppress page/alignment faults (`MEMORY_FAULT_SUPPRESSION`). | **`#UD` (`ZEROING=0`):** Zeroing a memory destination is architecturally illegal (`62 41 7f c9 7f 61 01` traps). | `ModR/M.reg` encodes source `ZMM` (`0..31`); base/index GPRs use `B`/`X`. |
| **Opmask-destination EVEX compare / bit-shuffle (`VPCMPUB k7{k1}`, `VPSHUFBITQMB k5{k6}`, `bitalg-isa.xed.txt:292`)** | `EVEX.aaa = 000`: Unmasked write to destination `k_dst` (**including `k0`** if `ModR/M.reg = 000`!). | **Implicit zero-masking despite `z = 0`!** Where `k_mask[i] = 0`, **`k_dst[i] := 0`** (never preserves old `k_dst[i]`); upper bits `[63 : VL/esize]` of `k_dst` are also zeroed! | **`#UD` (`ZEROING=0`):** Setting `EVEX.z = 1` (`62 d2 25 c6 8f 68 01`) raises `#UD`! | `MASK_R()` requires `REXR4=0` (`EVEX.R'=1`) and `REXR=0` (`EVEX.R=1`); `R'=0` or `R=0` raises **`#UD`** (`62 c2 25 46 8f 68 01`). |
| **Gather / Scatter (`VGATHER*` / `VSCATTER*`)** | **`#UD` (`MASKNOT0()`):** `EVEX.aaa = 000` is rejected (`XED_REG_ERROR`); also `#UD` if index, mask, and dest alias improperly. | Predicated element gather/scatter, clearing each completed bit `k[i] := 0` on completion. | Gather allows `z ∈ {0, 1}`; Scatter requires `z = 0` (`#UD` if `z = 1`). | `EVEX.V'` extends VSIB vector index (`zmm0..31`). |
| **`VEX` opmask ops (`KMOVB/W/D/Q`, `KUNPCK*`, `KAND*`)** | `k0` is an **ordinary readable and writable 64-bit register** (`kmovb k0, eax` writes `k0[7:0]` and zeroes `k0[63:8]`). | N/A (`VEX` has no `EVEX.aaa` field). | N/A (`VEX` has no `EVEX.z` field). | `MASK_N64()` requires `VEX.vvvv[3] = 1` (`~vvvv < 8`), else `#UD`; `EVEX.B` / `VEX.B` ignored in `MASK_B()`. |

Two consequences of this matrix are critical for formal soundness:
- First, `k0` is **not** a hardwired constant register like AArch64 `XZR` or RISC-V `x0`: `kmovd k0, eax` and `vpcmpub k0, zmm1, zmm2, 0` genuinely mutate `k0` (`kmovd eax, k0` reads that mutated value back), even though `EVEX.aaa = 0b000` bypasses `k0` and supplies `0xFFFF_FFFF_FFFF_FFFF`.
- Second, modeling opmask-destination instructions (`VPCMP*`, `VPSHUFBITQMB`) by passing their result through a generic `Merge_mask k` helper when `EVEX.z = 0` (`apply_evex_masking` in `s2n-bignum` `x86.ml:2626`) would be **unsound**, because hardware unconditionally **zeroes** masked-off bits (`k_dst[i] = k_mask[i] & bit_res[i]`) while simultaneously raising `#UD` if `EVEX.z = 1`.

#### 2.3 Compressed `disp8 * N` Tuple Scaling, Relocation Addends, and the GNU `objdump` `VPERMB` Disassembler Bug

When `ModR/M.mod == 0b01` under `EVEX`, the 1-byte signed displacement `disp8` is multiplied by a tuple-size scale factor $N \in \{1, 2, 4, 8, 16, 32, 64\}$ determined jointly by the opcode's `TUPLE_TYPE`, `EVEX.W`, `EVEX.L'L` (`VL`), and `EVEX.b` (`bcast`, `avx512-disp8.txt:52-130`, `s2n-bignum` `decode.ml:176-201`). Assembling and inspecting `evex_encoding_probe.o` and `evex_reloc_illegals.o` (`Basis: execution`) demonstrates three concrete binary-lifting hazards:

1. **Single-Bit `EVEX.b` Flip Changes Memory Offset by `16x`:**
   - `vpdpbusd zmm16{k1}, zmm17, ZMMWORD PTR [rsi + 0x40]` encodes as `62 e2 75 41 50 46 01` (`P2 = 0x41`: `b = 0`, `Full_Tuple`, $N = 64$, so `disp8 = 0x01` $\implies +64$ bytes).
   - `vpdpbusd zmm16{k1}, zmm17, DWORD PTR [rsi + 0x40]{1to16}` encodes as `62 e2 75 51 50 46 10` (`P2 = 0x51`: `b = 1`, `Full_Tuple` with `W = 0` broadcast, $N = 4$, so `disp8 = 0x10` $\implies +64$ bytes, whereas `62 e2 75 51 50 46 01` addresses `[rsi + 0x04]`!).
2. **Trailing Immediate Shifts `R_X86_64_PC32` Addends on `VPTERNLOGD`:**
   - In `evex_reloc_illegals.o`, `vpdpbusd zmm16{k1}, zmm17, DWORD PTR [rip + tap_const]{1to16}` (`10` bytes, no immediate) emits `R_X86_64_PC32 tap_const - 0x4` at `disp32` offset `0x06`, whereas `vpternlogd zmm23{k3}{z}, zmm24, DWORD PTR [rip + tap_const]{1to16}, 0xe4` (`11` bytes, trailing `imm8 = 0xe4` at byte `10`) emits **`R_X86_64_PC32 tap_const - 0x5`** at `disp32` offset `0x10` (and `IMAGE_REL_AMD64_REL32_1` on Win64 COFF). Computing $\text{EA} = S + A + (\text{RIP}_{\text{next}} - P)$ handles both `-4` ($10 - 6 = 4$) and `-5` ($11 - 6 = 5$) uniformly; hardcoding $+4$ misbinds `vpternlogd` constant pools by 1 byte.
3. **Empirical Disassembler Bug in `GNU objdump 2.47` on Illegal `VPERMB` Broadcast (`Basis: execution + source`):**
   - Because `VPERMB` (`0F38 8D`) has 8-bit element granularity (`DISP8_FULLMEM`, `ESIZE_8_BITS()`), embedded broadcast is architecturally illegal (`BCRC=0` in `intelxed/xed` `datafiles/avx512vbmi/vbmi-isa.xed.txt:52, 82, 112`), and `GNU as 2.47` rightly rejects `vpermb zmm20{k2}{z}, zmm21, DWORD PTR [rdi+4]{1to16}` with `Error: operand size mismatch for 'vpermb'`.
   - Yet when fed raw bytes `.byte 0x62, 0xe2, 0x55, 0xd2, 0x8d, 0x67, 0x01` (`P2 = 0xd2`, setting `EVEX.b = 1` on `VPERMB`), **`GNU objdump 2.47` (`libopcodes`) fails to reject `b = 1` and disassembles the `#UD` byte sequence as `vpermb zmm20{k2}{z},zmm21,DWORD BCST [rdi+0x4]`**! An object-level binary lifter **must never** rely on text disassembly (`objdump`/`llvm-objdump`); it must decode raw section bytes against XED's exact `BCRC=0` / `ZEROING=0` / `MASK_R` tables.

#### 2.4 `zmm16..zmm31` and `k0..k7` Volatility Across System V AMD64 and Windows x64 ABIs

Under **both** the System V AMD64 psABI and the Microsoft x64 Calling Convention:
- **`zmm16..zmm31` (all 512 bits) and `k0..k7` (all 64 bits) are caller-saved (volatile)**—even on Windows x64, where the low 128-bit halves `xmm6..xmm15` remain callee-saved (non-volatile) while `ymm0..ymm15[255:128]` and `zmm0..zmm15[511:128]` are volatile.
- Moreover, Intel and AMD microarchitectures track dirty upper-YMM state (`XINUSE[2]`, read via `mov ecx, 1; xgetbv; test al, 0x04` in `FFmpeg` `tests/checkasm/ext/src/x86/checkasm.asm:323-334`) **only** on `ymm0..ymm15` / `zmm0..zmm15`. Touching `xmm16..xmm31`, `ymm16..ymm31`, or `zmm16..zmm31` exclusively leaves `XINUSE[2] == 0`, incurring zero legacy-SSE transition penalty without executing `vzeroupper`.
- FFmpeg's `libavutil/x86/x86inc.asm:374, 1073-1145` exploits both invariants simultaneously via `AVX512_MM_PERMUTATION`: under `INIT_YMM avx512icl` and `INIT_ZMM avx512icl`, logical `m0..m15` are swapped with hardware `zmm16..zmm31` (`AVX512_MM_PERMUTATION 0`), and under `INIT_XMM avx512icl` on `WIN64`, logical `m6..m15` are swapped with volatile `xmm22..xmm31` (`AVX512_MM_PERMUTATION 6`, `line 1108`), allowing `%define vzeroupper_required (mmsize > 16 && (ARCH_X86_64 == 0 || xmm_regs_used > 16 || notcpuflag(avx512)))` (`line 374`) to elide both `vzeroupper` and Win64 `.xdata` `UWOP_SAVE_XMM128` spills whenever a kernel uses $\le 16$ vector registers (`m0..m15` $\mapsto$ `zmm16..zmm31`) or $\le 22$ registers on Win64 (`zmm16..zmm31` + volatile `zmm0..zmm5`). An object-level ABI verifier must therefore partition its clobber and `vzeroupper` proof obligations on `reg_idx < 16` vs `reg_idx >= 16`: `vzeroupper` before `ret` is required if and only if any instruction writes `ymm0..15` or `zmm0..15` (`VL >= 256` and `dst_idx < 16`).

---

### 3. x86-64 Pass-2 Coverage Gaps in `s2n-bignum` and ACL2 `x86isa` and Fail-Closed Extension Rules

`Basis: source + derived`

Auditing the pinned x86-64 theorem-prover models against the FFmpeg/dav1d instruction census yields an unambiguous result:

| Component / Opcode (`FFmpeg` & `dav1d` Scope) | `intelxed/xed` (`0bcb6237`) | `awslabs/s2n-bignum` (`280a2209`) | ACL2 `x86isa` (`08bec188`) / `sail-x86-from-acl2` (`0c6c023d`) | Required Pass-2 Action |
| :--- | :--- | :--- | :--- | :--- |
| **`ZMM0..31` & `k0..k7` State** | Metadata (`avx512-regs.txt`, `avx512-kregs.txt`) | **Complete:** `simdregisters: (5)word->(512)word` (`x86.ml:68`), `maskregisters: (3)word->(64)word` (`x86.ml:69`) | **Partial:** `zmmi` `32 x 512b` (`register-readers-and-writers.lisp:781`, `sail_regs.sail:127`); `opmsk` omitted from `sail_regs.sail` | Reuse `s2n-bignum` state isomorphism (`Fin 32 -> BitVec 512`, `Fin 8 -> BitVec 64`). |
| **`EVEX` `0x62` Prefix, `disp8*N`, `{k1}`/`{z}`, `{1toN}`** | **Complete** (`avx512-evex-dec.txt`, `avx512-disp8.txt`) | **Staged but unwired:** `read_EVEX`, `read_EVEX_ModRM`, `evex_tuple_disp_scale` (`decode.ml:168-406`), `apply_evex_masking`, `evex_src` (`x86.ml:2612-2827`); **`[0x62:8]` absent from `decode_aux` (`decode.ml:777-860`)!** | **Prefix only:** `evex-decode-and-execute` (`evex-opcodes-dispatch.lisp:202-343`) checks `#UD` on `P0`/`P1`, but **0 of 1,375 `:EVEX` entries in `inst-listing.lisp` have execution bodies (`NIL`)** | Wire `[0x62:8]` dispatch with XED `#UD` guards (`~(aaa=0 ∧ z=1)`, `ZEROING=0` on stores & `k`-dests, `BCRC=0` on `FVM`). |
| **`VPDPBUSD` / `VPDPWSSD` (`AVX512_VNNI` & `AVX_VNNI`)** | **Complete** (`vnni-isa.xed.txt:30-290`, `avx-vnni-isa.xed.txt:29-180`) | **Missing** (`0` in `instruction.ml`, `[0x50:8]` absent in `VEXM_0F38` `decode.ml:860-1015`) | **Missing** (`0` entries in `inst-listing.lisp`) | Add both `VEX.128/256` (`AVX_VNNI`) and `EVEX.128/256/512` (`Full_Tuple`, `ESIZE_32_BITS` `{1toN}`) rules. |
| **`VPERMB`, `VPERMI2B`, `VPERMT2B` (`AVX512_VBMI`)** | **Complete** (`vbmi-isa.xed.txt:29-310`, `BCRC=0`, `DISP8_FULLMEM`) | **Missing** (has `VPERMD`/`VPERMQ` VEX only at `instruction.ml:410-411`) | **Stub only:** `3` `VPERMB` rows in `inst-listing.lisp`, all execution `NIL` | Add `EVEX` `0F38 8D` (`VPERMB`), `75` (`VPERMI2B`), `7D` (`VPERMT2B`) with `BCRC=0` (`#UD` if `b=1`). |
| **`VPTERNLOGD` / `VPTERNLOGQ` (`AVX512F`)** | **Complete** (`skx-isa.xed.txt:23788-23890`, `0F3A 25`, `UIMM8`) | **Missing** (`0` in `instruction.ml`) | **Stub only:** `6` rows in `inst-listing.lisp`, all execution `NIL` | Add `EVEX` `0F3A 25` (`W=0` 32-bit / `W=1` 64-bit `Full_Tuple` broadcast, `imm8` LUT). |
| **`VPMADD52LUQ` / `VPMADD52HUQ` (`AVX512_IFMA`)** | **Complete** (`ifma-isa.xed.txt:29-206`, `0F38 B4/B5`, `W=1`) | **Missing** (`0` in `instruction.ml`) | **Stub only:** `6` rows in `inst-listing.lisp`, all execution `NIL` | Add `EVEX` `0F38 B4/B5` (`W=1` mandatory, `#UD` if `W=0`, `Full_Tuple` 64-bit `{1toN}`). |
| **`VPSHUFBITQMB` (`AVX512_BITALG`)** | **Complete** (`bitalg-isa.xed.txt:210-296`, `0F38 8F`, `W=0`, `BCRC=0`, `ZEROING=0`) | **Missing** (`0` in `instruction.ml`) | **Missing** (`0` entries in `inst-listing.lisp`) | Add `EVEX` `0F38 8F` writing `k_dst` (`R'=1, R=1, z=0, b=0` mandatory, implicit zero-masking by `k_mask`). |
| **`KMOVB/W/D/Q` & `VMOVDQU8/16/32/64` & `VPCMPUB`** | **Complete** (`skx-isa.xed.txt:8660-8720, 27489-27590`) | **Missing** (`VMOVDQU` VEX only at `instruction.ml:394`; `0` `KMOV*`) | **Stub only:** `35` `KMOV*` rows in `inst-listing.lisp`, all execution `NIL` | Add `VEX` `0F 90..93` (`KMOV*`), `EVEX` `0F 6F/7F` (`VMOVDQU*` with masked fault suppression), and `EVEX` `0F3A 3E` (`VPCMPUB`). |

#### Fail-Closed Pass-2 Subset and Semantic Extension Specification

Because neither `s2n-bignum` nor ACL2 `x86isa` implements the six `AVX-512ICL` / `AVXVNNI` opcode families, a sound Pass-2 x86-64 verification architecture must apply a **two-part fail-closed rule**:
1. **Decoder & `#UD` Legality Oracle (`intelxed/xed@0bcb6237`):** Any instruction byte sequence inside `.text.<fn>` whose XED decode either fails, requires an `ISA_SET` outside the function's declared CPUID dispatch predicate (`SKYLAKE_SERVER` $\cup$ `ICE_LAKE` for `avx512icl`; `AVX2` $\cup$ `AVX_VNNI` for `avxvnni`), or violates XED's `EVEX` constraints (`(aaa == 0 && z == 1)`, `(is_store && z == 1)`, `(is_kmask_dest && (z == 1 || ~R' != 0 || ~R != 0))`, `(!broadcast_enabled && b == 1)`, `(LL == 0b11 && !(fp_reg_reg_512 && b == 1))`) **maps deterministically to `.fault .illegalInstruction`**.
2. **Closed `BitVec` Lane Semantics Over `s2n-bignum`'s `apply_evex_masking` / `evex_src` Algebra:** Every admitted media opcode reduces to total, loop-free `BitVec` lane combinators over $L \in \{128, 256, 512\}$ bits (zero-extending bits `[511:L]` of `ZMM[dst]`):
   - **`VPDPBUSD` (`0F38 50`, `W=0`, `esize=32`, both `VEX` `Unmasked` and `EVEX` `masking`):** For each 32-bit lane $j \in [0, L/32)$, let $a_k = \text{uext}_{32}(\text{src1}[32j+8k+7 : 32j+8k])$ and $b_k = \text{sext}_{32}(\text{src2}[32j+8k+7 : 32j+8k])$ for $k \in \{0,1,2,3\}$; compute $\text{res}_j = (\text{dst}_{\text{old}}[32j+31:32j] + \sum_{k=0}^{3} a_k \cdot b_k) \bmod 2^{32}$, then apply `apply_evex_masking 32 masking res dst_old`. (`VPDPBUSDS` `0F38 51` replaces modular addition with signed 32-bit saturation $\text{clamp}_{[-2^{31}, 2^{31}-1]}$.)
   - **`VPERMB` (`0F38 8D`, `W=0`, `b=0`, `esize=8`) and `VPERMI2B` (`0F38 75`, `W=0`, `b=0`, `esize=8`):** Let $M = L / 8 \in \{16, 32, 64\}$ bytes. In `VPERMB`, byte $i$ of `res` selects $\text{src2}[\text{idx}_i \bmod M]$ where $\text{idx}_i = \text{src1}[8i + \log_2 M - 1 : 8i]$ (**ignoring bit 7**, unlike `VPSHUFB`). In `VPERMI2B`, `dst` holds the index vector; let $s_i = \text{dst}_{\text{old}}[8i + \log_2(2M) - 1 : 8i]$ (`5, 6,` or `7` bits for $L = 128, 256, 512$); byte $i$ selects from the concatenated $2M$-byte table $(\text{src2} \mathbin{\Vert} \text{src1})[s_i]$, and `apply_evex_masking 8 masking res dst_old` merges inactive lanes (`k[i] = 0`) against the **original index register `dst_old`** (whereas `VPERMT2B` `0F38 7D` takes indices from `src1` and merges inactive lanes against table half `dst_old`).
   - **`VPTERNLOGD` / `VPTERNLOGQ` (`0F3A 25`, `esize = 32 << W`):** Bitwise parallel evaluation: for every bit $b \in [0, L)$, let $t = (\text{dst}_{\text{old}}[b] \ll 2) \mid (\text{src1}[b] \ll 1) \mid \text{src2}[b] \in \{0..7\}$; $\text{res}[b] = (\text{imm8} \gg t) \mathbin{\&} 1$, masked at `esize`-bit granularity (`32` or `64` bits) by `apply_evex_masking`.
   - **`VPMADD52LUQ` / `VPMADD52HUQ` (`0F38 B4` / `B5`, `W=1` mandatory, `esize=64`):** For each 64-bit lane $q \in [0, L/64)$, compute the exact 104-bit unsigned product $P_q = (\text{src1}_q \mathbin{\&} (2^{52}-1)) \times (\text{src2}_q \mathbin{\&} (2^{52}-1))$; `VPMADD52LUQ` sets $\text{res}_q = (\text{dst}_{\text{old},q} + (P_q \mathbin{\&} (2^{52}-1))) \bmod 2^{64}$, while `VPMADD52HUQ` sets $\text{res}_q = (\text{dst}_{\text{old},q} + (P_q \gg 52)) \bmod 2^{64}$.
   - **`VPSHUFBITQMB` (`0F38 8F`, `W=0`, `b=0`, `z=0`, `R'=1`, `R=1`):** Partition `src1` and `src2` into $Q = L / 64 \in \{2, 4, 8\}$ 64-bit qwords. For each qword $q \in [0, Q)$ and byte $j \in [0, 8)$, let $m_{8q+j} = \text{src2}_{q}[8j+5 : 8j] \in [0, 63]$; bit $8q+j$ of `k_dst` is set to $\text{mask}[8q+j] \mathbin{\&} \text{src1}_q[m_{8q+j}]$ for $8q+j < L/8$, and `0` for all bits $[L/8, 63]$.

---

### 4. Armv9 `SVE2` and `SME2` State Machine, `inter_sme2.S` Anatomy, and Upstream FFmpeg ABI/SVL Defects

`Basis: normative + source + execution`

#### 4.1 `sail-arm` Architectural State (`SVCR`, `ZA`, `ZT0`, `FPSR`) and NEON-SVE Aliasing

In `rems-project/sail-arm@5416ef6b43e9527c38dc71fb752259c1d01a47e1` (`arm-v9.4-a/src/v8_base.sail:2700-2726, 6871-7012, 9504-9513, 29383-29649, 31132-31306` and `src/instrs64.sail:39038-39170`), scalable vector and matrix state at `EL0` comprises:
- **Vector & Predicate Storage:** `_Z : vector(32, bits(2048))`, `_P : vector(16, bits(256))`, `_FFR : bits(256)` (`v8_base.sail:2710-2714`), where `CurrentVL_read()` (`L6997-7000`) returns `CurrentSVL_read()` when `HaveSME() & PSTATE.SM == 0b1` and `CurrentNSVL_read()` otherwise (`PL = VL / 8`).
- **SME Matrix & Lookup-Table Storage:** `_ZA : vector(256, bits(2048))` (`L2724`, active slice dimension $\text{SVL}/8 \times \text{SVL}$ bits, i.e., `16 x 16 = 256` bytes at `SVL = 128` up to `256 x 256 = 65,536` bytes at `SVL = 2048`), viewing tile $t$ of element width $\text{esize} \in \{8, 16, 32, 64, 128\}$ as interleaved row vectors `ZAvector[t + s * (esize / 8)]` (`ZAhslice_read`, `L31157-31165`), plus SME2's 512-bit lookup-table register `_ZT0 : bits(512)` (`L2726`), gated by `CheckSMEZT0Enabled()` (`SMCR_ELx[EZT0] == 0b1`, `L29525-29545`, raising `SMEExceptionType_InaccessibleZT0` if disabled) and `PSTATE.ZA == 0b1`.
- **Mode Transitions (`smstart` / `smstop` $\equiv$ `MSR SVCR*`, `instrs64.sail:39038-39050`):**
  - `SetPSTATE_SM(v)` (`v8_base.sail:29616-29622`): **If and only if `PSTATE.SM != v`**, invokes `ResetSVEState()` (`L9504-9513`)—zeroing all 32 `_Z` registers (`2048` bits each), all 16 `_P` registers, and `_FFR`, **and resetting `FPSR` to `0x0800009f`**!
  - `SetPSTATE_ZA(v)` (`v8_base.sail:29626-29632`): **If and only if `PSTATE.ZA != v`**, invokes `ResetSMEState()` (`L29606-29612`)—zeroing all 256 `_ZA` vectors and 512-bit `_ZT0`!
- **Non-Streaming NEON/SVE Interleaving vs. Streaming NEON Trap:**
  - In `PSTATE.SM == 0` (`videolan/dav1d` `src/arm/64/mc16_sve.S:94-248`), `v0..v31` alias `_Z[0..31][127:0]`: NEON writes (`zip1 v16.4s`, `tbl v16.16b`, `uzp1 v0.4s`) zero bits `[MAX_VL-1:128]`, while interleaved SVE2 instructions (`ptrue p0.b, vl16`, `ld1sb {z7.h}, p0/z`, `sdot z0.d, z16.h, z7.h[0..1]`) operate across `[VL-1:0]`.
  - In `PSTATE.SM == 1` (`FFmpeg` `inter_sme2.S`), unless optional `FEAT_SME_FA64` (`SMCR_ELx.FA64 == 1`, absent on Apple M4 and non-mandatory in Armv9.2-A) is active, **legacy NEON instructions raise `SMEExceptionType_Streaming` (`SIGILL`)**.

#### 4.2 Dissection of `FFmpeg` `libavcodec/aarch64/vvc/inter_sme2.S` and Three Verified Upstream Bugs

`FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` `libavcodec/aarch64/vvc/inter_sme2.S:25-651` implements ITU-T H.266 (VVC) §8.8.5.2 7x7 diamond Adaptive Loop Filtering (`ff_vvc_alf_filter_luma_{8,10,12}_sme2`, `12` symmetric neighbor pairs $p_0..p_{11}$ plus center pixel $p_{\text{curr}}$, classified per $4 \times 4$ luma block). Its inner pipeline maps 4 pixel rows (`r = 0..3`, `x14..x17`) across $\text{cnth} = \text{SVL} / 16$ horizontal luma samples simultaneously:
1. **Head-First Remainder Predication (`lines 132-138, 344-350`):** Computes `w9 = width - ((width - 1) / cnth) * cnth` $\in [1, \text{cnth}]$ (`sdiv` + `msub`) and `whilelo p10.h, xzr, x9`, processing the partial strip **first** under `p0 = p10` and setting `ptrue p0.h` (`line 344`) for all subsequent full-`cnth` horizontal strips (`subs w8, w8, w12; b.gt 2b`).
2. **4-Way Transpose + `FEAT_SME_I16I64` `ZA` Accumulation (`lines 88-114, 217-337`):** Loads three 4-tap coefficient/clip groups via `ld3h {z0.h-z2.h}, p0/z, [x5]` and `ld3h {z3.h-z5.h}, p0/z, [x4]`, replicates each `4x4` block's 64-bit 4-tap vector across 4 `Z` registers via `zip {z12.d-z15.d}, {z12.d-z15.d}` and `zip {z28.d-z31.d}, {z28.d-z31.d}`, transposes 4 neighbor differences $(p_k - p_{\text{curr}})$ via `zip {z20.h-z23.h}, {z20.h-z23.h}`, clips via `sclamp`, accumulates 16-bit products into 64-bit `ZA` vectors via `sdot za.d[w10, \idx], {z20.h-z23.h}, {z28.h-z31.h}` (`execute_SDOT_ZA_ZZW_4x4`, `instrs64_sme.sail:20633`, `w10 = 0`, `\idx ∈ {0,1,2,3}`), extracts via `mova {z16.d-z19.d}, za.d[w10, 0..3]` (`execute_MOVA_MZ_ZA4_1`, `instrs64_sme.sail:5358`), rounds/narrows `64 -> 16` bits via `sqrshr z12.h, {z16.d-z19.d}, #7` (or `#10` on virtual-boundary rows tested via packed `w13` bits `#0/#8/#16/#24`, `lines 320-330`), adds `p_curr` (`add` for 8-bit, `sqadd` for 10/12-bit), clamps to `[0, (1<<bd)-1]`, stores via `st1b`/`st1h`, and clears `ZA` via `zero {za}` (`lines 341, 626`).

Cross-checking this assembly line-by-line against `rems-project/sail-arm` (`5416ef6b43e9527c38dc71fb752259c1d01a47e1`) and `ARM-software/abi-aa` (`9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7`) exposes **three concrete upstream bugs** in `FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, confirmed by our executable Sail-to-VVC correspondence harness (`sme2_alf_sail_check.py`, `Basis: source + normative + execution`):

1. **Bug 1 — Unchecked `SVL == 128` `SIGILL` (`Error_Undefined`) Trap in `zip {z12.d-z15.d}` (`inter_sme2.S:232, 239, 264, 272, 292, 300, 516, 523, 548, 556, 576, 584` + `vvc/dsp_init.c:327, 382, 438`):**
   - In `instrs64_sme.sail:35046-35051`, `execute_ZIP_MZ_Z_4 (VL, d, esize, n)` begins with:
     ```sail
     if VL < esize * 4 then {
         throw(Error_Undefined())
     };
     ```
   - When `zip {z12.d-z15.d}, {z12.d-z15.d}` is invoked with `.d` (`esize = 64`), `esize * 4 = 256` bits. On any architecturally compliant Armv9 SME2 implementation whose Streaming Vector Length is **`SVL == 128` bits** (`SMCR_EL1.LEN = 0` or `128`-bit SME2 hardware, which is explicitly legal in `is_VL('vl) = ('vl in {128, 256, 512, 1024, 2048})`, `prelude.sail:349`), `zip {z12.d-z15.d}` **immediately raises `Error_Undefined()` (`SIGILL`)**!
   - Yet `libavcodec/aarch64/vvc/dsp_init.c:327, 382, 438` wires `c->alf.filter[LUMA] = alf_filter_luma_{8,10,12}_sme2` under `if (have_sme2(cpu_flags) && have_sme_i16i64(cpu_flags))` with **zero `SVL >= 256` runtime check** (`rdsvl >= 32` bytes), whereas for all `SVL ∈ {256, 512, 1024, 2048}` our correspondence harness confirms `exact_match = True` against ITU-T H.266 §8.8.5.2.

2. **Bug 2 — Missing AAPCS64 `TPIDR2_EL0` Lazy-Save Commit and Unzeroed First-Iteration `ZA` Accumulation (`libavutil/aarch64/asm.S:352-371` + `inter_sme2.S:124, 249-311, 341`):**
   - `ff_vvc_alf_filter_luma_*_sme2` is called through a standard C function pointer (`c->alf.filter[LUMA]`), which under the AAPCS64 SME Procedure Call Standard (`ARM-software/abi-aa` `aapcs64/aapcs64.rst:2642-2659`) is a **non-streaming, private-ZA** interface. Normative AAPCS64 rules allow a caller holding live `ZA` data to defer saving `ZA` across normal C calls by leaving **`PSTATE.ZA == 1`** and pointing **`TPIDR2_EL0`** at a `TPIDR2 block`, requiring any private-ZA callee that touches `ZA` or `PSTATE.ZA` to execute:
     ```c
     if (TPIDR2_EL0 != nullptr) { __arm_tpidr2_save(); TPIDR2_EL0 = nullptr; }
     ```
     before `smstart` (`aapcs64.rst:2648-2654`).
   - `FFmpeg`'s `sme_entry` (`libavutil/aarch64/asm.S:352-361`) saves `x29, x30, d8..d15` and executes bare `smstart` **without checking `TPIDR2_EL0`**, and `inter_sme2.S` omits `zero {za}` in its prologue (executing `zero {za}` only at the *end* of inner loop `2:` on lines `341` and `626`).
   - Because `SetPSTATE_ZA(0b1)` (`v8_base.sail:29627`: `if PSTATE.ZA != value_name then ResetSMEState()`) **does NOT zero `_ZA` when `PSTATE.ZA` is already `1`**, entering `ff_vvc_alf_filter_luma_8_sme2` with `PSTATE.ZA == 1, TPIDR2_EL0 != NULL` causes two simultaneous failures: (a) on strip `(0, 0)`, `sdot za.d[w10, 0..3]` accumulates onto the caller's live `ZA` matrix (`127/256` output pixels corrupted at `SVL = 512`, `dirty_za = 0x10000` in `sme2_alf_sail_check.py`); and (b) `sme_exit`'s `smstop` clears `PSTATE.ZA := 0` (`ResetSMEState()`) while leaving `TPIDR2_EL0 == &BLK`, tricking the caller's post-call check (`if (TPIDR2_EL0) { TPIDR2_EL0 = nullptr; } else { __arm_tpidr2_restore(&BLK); }`, `aapcs64.rst:2714-2722`) into skipping `__arm_tpidr2_restore` and trapping (`SMEExceptionType_InactiveZA`) on its next `ZA` instruction!

3. **Bug 3 — Unsaved Callee-Saved `d8..d15` Clobber in `ff_aarch64_sme_length` (`libavutil/aarch64/cpu_sme.S:26-31`):**
   - `ff_aarch64_sme_length` executes bare `smstart; cntb x0; smstop; ret` without `sme_entry`/`sme_exit`. Both `smstart` (`0 -> 1`) and `smstop` (`1 -> 0`) invoke `ResetSVEState()` (`v8_base.sail:9504-9513`), **zeroing AAPCS64 callee-saved `d8..d15`** (and clobbering any lazy `TPIDR2_EL0` `ZA` state). Replacing the body with `rdsvl x0, #1; ret` (`ENABLE_SME`) queries `SVL / 8` directly in non-streaming mode with zero register or `SVCR` side effects.

---

### 5. Resolving the `VL`-Parametric Obstacle: Finite Power-of-Two `ASLp` `rASL` Specialization vs. Sliced `sail-arm` Lean 4 Extraction

`Basis: source + normative + derived`

Verifying scalable vector (`SVE2`) and matrix (`SME2`) kernels in Lean 4 faces a foundational design choice: should Pass-2 golden correspondence and Pass-1 kernel proofs reason **inductively over symbolic `VL`**, **partially evaluate each opcode per fixed `VL` via `UQ-PAC/ASLp`**, or **extract per-opcode Lean 4 slices directly from `rems-project/sail-arm`**? Source-level inspection of both tools resolves every piece of this trade-off:

1. **Architectural `VL` vs. `SVL` Cardinality Law (`ARM DDI 0487` vs. `sail-arm` `prelude.sail:349`):**
   - For **SME/SME2 (`PSTATE.SM == 1`)**, the Arm Architecture Reference Manual normatively restricts Streaming Vector Length `SVL` to **powers of two** in $[128, 2048]$ bits (`ImplementedSMEVectorLength` checks `IsPow2(nbits)`, `v8_base.sail:6936`). There are **only `5` architecturally legal `SVL` values in existence**: $\{128, 256, 512, 1024, 2048\}$ bits (and only **`4` values `{256, 512, 1024, 2048}`** once `SVL >= 256` is enforced for `.d` multi-vector kernels!).
   - For **non-streaming SVE/SVE2 (`PSTATE.SM == 0`)**, `ARM DDI 0487` normatively permits `16` multiples of 128 bits (`128, 256, 384, ..., 2048` via `ZCR_EL1.LEN`), although all shipping Arm silicon implements powers of two (`128` on Neoverse V2 / Cortex-X4, `256` on Neoverse V1 / Graviton3/4, `512` on Fujitsu A64FX) and `rems-project/sail-arm` itself defines `type is_VL('vl : Int) -> Bool = ('vl in {128, 256, 512, 1024, 2048})` (`prelude.sail:349`, `v8_base.sail:6877`).

2. **Why `UQ-PAC/ASLp` (`92e4fd949402056e16e3747e66922060be57ecc8`) Excels on Fixed-Width NEON/SVE2 Yet Encounters Four Barriers on General SVE2/SME2:**
   - **Barrier A — `Stmt_While` Emits `assert FALSE` (`libASL/dis.ml:1413-1416`):** Unlike `Stmt_For` (which `dis.ml:1355-1381` unrolls whenever `stop - start < config.unroll_bound`), `ASLp`'s partial evaluator translates **every `Stmt_While` and `Stmt_Repeat` directly to `Stmt_Assert(expr_false, loc)`**, even when all loop variables are compile-time constants! Because `ImplementedSVEVectorLength` (`while nbits > 128`) and `ImplementedSMEVectorLength` (`while nbits > 128` and `while nbits < maxbits`) execute `while` loops for every `VL >= 256` (and for `SVL = 128` when `MaxImplementedSVL > 128`), unpatched `ASLp` emits dead `assert FALSE` semantics unless `CurrentVL` / `Implemented*VectorLength` is monkey-patched to a constant or `dis.ml` is extended with bounded `Stmt_While` unrolling.
   - **Barrier B — Uninitialized `PSTATE.{SM,ZA}` / `ZCR_EL1` / `SMCR_EL1` in `build_env` (`dis.ml:1628-1654`):** `Dis.build_env` pins only `PSTATE.{EL,SP,nRW} = 0`, `SCR_EL3 = 0`, `SCTLR_EL1 = 0`, and `InGuardedPage = false`. Specializing `SVE2`/`SME2` requires extending `build_env` with concrete `(PSTATE.SM, PSTATE.ZA, ZCR_EL1.LEN, SMCR_EL1.{LEN,FA64,EZT0})` per target mode and `VL`.
   - **Barrier C — Dynamic Slice Rejection on `ZT0` `LUTI2`/`LUTI4` (`rASL_check.ml:266`):** In `execute_LUTI2_Z_ZTZ__` (`instrs64_sme.sail:35957-35959`), 2-bit/4-bit indices extracted from symbolic vector `Zn` slice `_ZT0 : bits(512)` at dynamic bit offset `32 * UInt(index)`. Unless `!Symbolic.use_vectoriser = true` (`rASL_check.ml:139-141`, preserving `Elem.read`) or `Elem.read` is rewritten to a dynamic logical right shift `(table >> (32 * zext(index)))[esize-1 : 0]`, `Expr_Slices` fails `is_const(l)` (`IllegalSlice`).
   - **Barrier D — AST Blowup at `SVL = 2048` and Proprietary Arm XML Licensing:** Fully unrolling `SDOT_ZA_ZZW_4x4` (`4` vectors $\times 32$ `i64` lanes $\times 4$ `i16` products = `512` MACs per instruction) or `ZERO {za}` (`256` 2048-bit vector writes) at `SVL = 2048` inflates flat `rASL` trees by `16x` over `SVL = 128`, while running `ASLp` over Arm's proprietary MRA XML restricts open-source redistribution of generated Lean artifacts (`comp1`: `x86-64-and-aarch64-simd-isa-formalizations-sail-asl-acl2-hol-k-comparison`).

3. **Why Per-Opcode Sliced `rems-project/sail-arm` (`5416ef6b43e9527c38dc71fb752259c1d01a47e1`) Eliminates `ArmExtras.lean` `sorry`s Cleanly:**
   - Our complete scan of `v8_base.sail` (`57,139` lines), `instrs64_sve.sail` (`95,548` lines), and `instrs64_sme.sail` (`42,546` lines) proves that **zero (`0`) SME/SME2 instruction executors and all SVE/SVE2 executors except `PNEXT` contain zero `while`/`repeat` loops**.
   - Every `decode_*` function in `instrs64_sve.sail` and `instrs64_sme.sail` (`decode_WHILELO_P_P_RR__:15799`, `decode_MOVA_MZ_ZA4_1:5386`, `decode_SDOT_ZA_ZZW_4x4:20682`, `decode_SQRSHR_Z_MZ4__:34050`, `decode_ZIP_MZ_Z_4:35080`, `decode_LUTI2_Z_ZTZ__:35981`) **already dispatches `match VL { 128 => ..., 256 => ..., 512 => ..., 1024 => ..., 2048 => ... }` to monomorphic `execute_*(VL_const, ...)` calls** whose `foreach` bounds (`0 .. (VL_const / esize) - 1`) are structurally finite!
   - Slicing `sail-arm` to EL0 user-mode memory (`Mem_read` / `Mem_set` bypassing EL1/EL2 `AArch64_S1Walk`/`S2Walk`), excluding unused FP transcendental `Real` normalizers (`FPRoundBase__1`, `FPLogB`), deleting `ArmExtras.lean:19-23`'s `sorry` macro, and supplying explicit `termination_by` measures for `ImplementedSVEVectorLength` (`nbits.toNat`), `ImplementedSMEVectorLength` (`nbits.toNat` and `(maxbits - nbits).toNat`), and `execute_PNEXT_P_P_P__` (`(elements - next).toNat`) produces a **`100%` `sorry`-free, `BSD-3-Clause-Clear` Lean 4 Pass-2 specification**.

| Verification Dimension | (A) Symbolic `VL`-Parametric Inductive Proofs | (B) Fixed-`VL` `UQ-PAC/ASLp` `rASL` Partial Evaluation (`5` `VL`s) | (C) Per-Opcode Sliced `sail-arm` + Finite `5`-`SVL` Case Split |
| :--- | :--- | :--- | :--- |
| **Redistribution License** | Open (hand-authored Lean `BitVec`) | Tool BSD-3-Clause; **raw Arm MRA XML proprietary** | **`BSD-3-Clause-Clear`** with explicit Arm Limited copyright grant (`arm-v9.4-a/LICENSE:1-37`) |
| **Pass-2 `sorryAx` / Axiom Status** | Requires inductive equivalence proof against Sail `foreachM` over dynamic `VL` | `0` `sorry`s, **requires patching `dis.ml:1413` (`Stmt_While`), `build_env`, and `LUTI2/4` dynamic slices** | **`0` `sorry`s, `0` custom axioms** after removing `ArmExtras.lean:23` & MMU/FP `while` walkers |
| **SME/SME2 Architectural `SVL` Coverage** | All `SVL`s, but dependent `BitVec (4 * esize)` casts complicate `ZA` stride arithmetic `(w10 + idx) % (SVL / 32)` | Exact `100%` coverage of all `5` architectural `SVL`s (`128..2048`), with large unrolled ASTs at `1024`/`2048` | **Exact `100%` coverage of all `5` architectural `SVL`s** directly matching `sail-arm`'s `match VL` |
| **Non-Streaming SVE2 `VL` Coverage** | Covers all `16` multiples of `128` bits (`128..2048`) | Covers power-of-two `VL`s (or all `16` if instantiated `16x`) | Covers all `5` power-of-two `VL`s (`100%` of commercial silicon; non-pow2 `384..1920` outside `sail-arm`'s `is_VL`) |
| **Loop-Strip Termination (`whilelo` / `subs w8, w8, cnth`)** | Single symbolic proof over `cnth = SVL / 16` | `4` or `5` concrete loop-step proofs ($w_8$ decreases by constant `16, 32, 64, 128`) | **Best hybrid:** Parametric strip-loop invariant over `cnth ∈ {16, 32, 64, 128}` + 4-way finite `SVL` body discharge! |

---

### 6. End-to-End Pass-2 Sandboxed Correspondence Blueprint for `EVEX`, `SVE2`, and `SME2`

`Basis: derived + source`

Integrating these findings into `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`'s two-pass audit boundary (`trusted/audit/TrustedBoundary.lean:229-314`, `trusted/audit/src/lib.rs:61-157`) yields a uniform, fail-closed verification contract:

1. **Object-Level Binary Lifter Admission Gate (Before Pass-1 WP Generation):**
   - Resolve all `.rela.text` / COFF / Mach-O relocations against immutable `.rodata*` sections using exact instruction-end offsets ($\text{EA} = S + A + \text{RIP}_{\text{next}} - P$, handling `-4` on `vpdpbusd` and `-5` on `vpternlogd` identically).
   - Decode x86-64 `.text` bytes via XED-equivalent tables enforcing `BCRC`, `ZEROING`, `MASKNOT0`, `MASK_R`, and `disp8 * N` scaling; verify `vzeroupper` precedes every `ret` whenever any path writes `ymm0..15`/`zmm0..15`.
   - Decode AArch64 `.text` bytes against `sail-arm`'s `__DecodeA64_{SVE,SME}` masks; on any function entering `PSTATE.SM = 1` or `PSTATE.ZA = 1` via a standard C ABI boundary, **mandate**:
     1. Entry guard `SVL >= SVL_min` (e.g., `SVL >= 256` bits whenever `ZIP_MZ_Z_4` `.d` or `MOVA_MZ4_ZA_D1` appears in the lifted CFG);
     2. AAPCS64 `TPIDR2_EL0` lazy-save commit (`mrs x_t, TPIDR2_EL0; cbz x_t, skip; bl __arm_tpidr2_save; msr TPIDR2_EL0, xzr`) **plus explicit `zero {za}`** before any accumulating `ZA` instruction (`SDOT`/`SUMOPA`/`SMLAL`), eliminating reliance on `PSTATE.ZA` having been `0` at entry;
     3. Preservation of `x19..x29` and `d8..d15` across `smstart`..`smstop`, with `FPSR` explicitly marked caller-clobbered (since both `ResetSVEState()` and `sqrshr`/`sqadd` mutate `FPSR`).

2. **Pass-1 Compact Evaluators vs. Pass-2 `bwrap --unshare-all` Correspondence Slices:**
   - **Pass 1 (`RepoOrigin`, `candidate:isa_x86_64_evex` and `candidate:isa_aarch64_sve2_sme2`):** Models vector state as `Fin 32 -> BitVec 512` + `Fin 8 -> BitVec 64` (`x86-64`) and `(svl : SVL) -> { z : Fin 32 -> BitVec svl.bits, p : Fin 16 -> BitVec (svl.bits / 8), za : Fin (svl.bits / 8) -> BitVec svl.bits, zt0 : BitVec 512, sm : Bool, za_en : Bool }` (`Armv9`), using pure lane-wise `BitVec` combinators amenable to structural decomposition under the 3-axiom kernel (`propext`, `Quot.sound`, `Classical.choice`).
   - **Pass 2 (`CorrOrigin`, networkless `bwrap` replay):** Replays per-opcode simulation theorems ($\forall s,\; \text{AdmittedState}(s) \implies M_{\text{pass1}}(\text{opc}, s) = \alpha^{-1}(M_{\text{sail\_arm}}(\text{opc}, \alpha(s)))$) against sliced, `sorry`-free `rems-project/sail-arm` (`aarch64`) and the HOL-Light-ported `s2n-bignum` + `EVEX` specification cross-checked against XED (`x86-64`).

---

## Boundaries

1. **Non-Power-of-Two SVE Vector Lengths (`384, 640, ..., 1920` bits) (`known not to apply` to `sail-arm`'s `is_VL`, `unsupported` on shipping silicon):** While `ARM DDI 0487` allows non-streaming SVE `VL` to take any 128-bit multiple up to 2048 bits (exercisable under QEMU `-cpu max,sve384=on`), `rems-project/sail-arm@5416ef6b43e9527c38dc71fb752259c1d01a47e1` (`prelude.sail:349`, `v8_base.sail:6877`) restricts `is_VL` to `{128, 256, 512, 1024, 2048}`. By contrast, SME `SVL` is **normatively** restricted to powers of two by Arm architecture rules, so `{128, 256, 512, 1024, 2048}` is 100% exhaustive for all `SME`/`SME2` kernels.
2. **Native Execution on Physical `AVX-512ICL` and `Armv9 SME2` Silicon (`not examined` directly on host CPU):** The Linux `x86_64` build host used for binary assembly/relocation probes in this investigation (`AMD EPYC 7B12`, `Rome` microarchitecture) implements up to `AVX2`/`BMI2` without `AVX-512` or `Armv9 SME2`. Machine-code byte encodings, `SHT_RELA` relocations, and disassembler rejections were verified by real execution of `gcc 15.2.0` / `GNU Binutils 2.47`, while `SME2` instruction semantics were executed against a faithful Python transcription of `rems-project/sail-arm`'s `instrs64_sme.sail` definitions (`sme2_alf_sail_check.py`), not on physical Apple M4 or Arm Cortex-X925 hardware.
3. **x86 `AVX10.1`/`AVX10.2`, `AMX` (`TMUL`), and `APX` Extended `EVEX` (`not examined` / `unsupported`):** Intel `APX` repurposes `EVEX` bit `P0[3]` (`B4`) and `P2[4]` (`ND`/`NF`) for 32-GPR (`r16..r31`) scalar instructions (`intelxed/xed` `datafiles/apx-f/apx-evex-dec.txt`), and `AMX` introduces 2D tile registers `tmm0..tmm7`. Neither is used by `FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` or modeled in `s2n-bignum` / ACL2 `x86isa`.
4. **First-Faulting (`LDFF1*`) and Non-Faulting (`LDNF1*`) Speculative SVE Loads (`not examined` in detail):** Neither `FFmpeg` `inter_sme2.S` nor `dav1d` `mc16_sve.S` uses `FFR`-updating first-faulting loads (`LDFF1*`), relying instead on `whilelo`/`whilelt` exact strip predicates (see `rvv-lmul-vtype-hazards-arm-sme-streaming-za-tiles-and-ffload-speculation` for general `FFR` speculation semantics).
5. **Asynchronous Signal / Exception Delivery Mid-Streaming Mode (`not examined`):** OS kernel signal-frame layout (`sve_context`, `za_context`, `zt_context` in Linux `ucontext_t`) during asynchronous preemption inside `smstart`..`smstop` is outside user-mode ISA operational semantics (`aapcs64.rst:3215-3251`).

---

## Evidence

### 1. Primary Upstream Repository Citations (All Verified 2026-11-20)

- **`FFmpeg/FFmpeg`** (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`):
  - x86-64 CPUID/`XCR0` gating & `x86inc.asm` ABI: `libavutil/x86/cpu.c:141-185, 275-286`; `libavutil/x86/cpu.h:48-49, 78-80`; `libavutil/cpu.c:153-155, 189-194`; `libavutil/x86/x86inc.asm:374-375, 966-967, 1073-1145`; `tests/checkasm/ext/src/x86/checkasm.asm:322-335, 473-484`.
  - x86-64 AVX-512 / AVX-512ICL kernels: `libavcodec/x86/vp9mc.asm:132-166, 847-865, 936-953, 1192-1268, 1404-1625`; `libavcodec/x86/hevc/mc.asm:90-95, 1248-1391`; `libavcodec/x86/vp9itxfm_avx512.asm:25, 159, 193-196, 281-288, 438-556, 757-826, 1172-1191`; `libavcodec/x86/vp9itxfm_16bpp_avx512.asm:25, 118, 231, 308, 349, 423, 1039-1054`; `libavcodec/x86/bitpacked.asm:26, 144, 220-221`; `libavcodec/x86/v210.asm:93, 148, 173`; `libavcodec/x86/v210enc.asm:59, 177, 331`; `libavfilter/x86/{vf_colordetect.asm:29,54, vf_gblur.asm:34,86-89,279,946, vf_idetdsp.asm:70,84}`; `libswscale/x86/{ops_common.asm:114,222, rgb_2_rgb.asm:38,81,231-232}`.
  - AArch64 SVE/SME2 kernels & ABI macros: `libavcodec/aarch64/vvc/inter_sme2.S:1-651`; `libavcodec/aarch64/vvc/dsp_init.c:294-329, 379-384, 435-440`; `libavcodec/aarch64/vvc/alf_template.c:246-274`; `libavutil/aarch64/asm.S:44-137, 213-262, 351-372`; `libavutil/aarch64/cpu.c:32-104, 183-264`; `libavutil/aarch64/cpu.h:34-46`; `libavutil/aarch64/cpu_sve.S:24-29`; `libavutil/aarch64/cpu_sme.S:24-31`.
- **`videolan/dav1d`** (`2a0775ca5ea055450bdfbfe81758a3c9e001f58a`):
  - `src/meson.build:124, 190-226`; `src/x86/cdef_avx512.asm:177, 201, 254-268` (`vpermi2b`, `vpdpbusd`, `vpshufbitqmb`); `src/x86/filmgrain_avx512.asm:319-322, 745-767`; `src/x86/ipred_avx512.asm:233-300`; `src/x86/looprestoration_avx512.asm:205-217` (`vpternlogd` `0xe4`); `src/x86/mc_avx512.asm:1144-1179`; `src/arm/64/mc16_sve.S:33-320`.
- **`intelxed/xed`** (`0bcb6237345c5066726dcc08b3d87928df3b5b26`):
  - `datafiles/avx512f/avx512-evex-dec.txt:19-53`; `datafiles/avx512f/evex-maps.txt:19-22`; `datafiles/avx512f/avx512-disp8.txt:22-130`; `datafiles/avx512f/avx512-kregs.txt:18-25`; `datafiles/avx512f/avx512-reg-table-mask.txt:20-69`; `datafiles/icl/icl-chips.txt:20-64`; `datafiles/vnni/vnni-isa.xed.txt:30-205`; `datafiles/avx-vnni/avx-vnni-isa.xed.txt:27-130`; `datafiles/avx512vbmi/vbmi-isa.xed.txt:27-160`; `datafiles/avx512ifma/ifma-isa.xed.txt:27-206`; `datafiles/bitalg/bitalg-isa.xed.txt:27-296`; `datafiles/avx512-skx/skx-isa.xed.txt:8660-8720, 23788-23848, 27489-27568`.
- **`awslabs/s2n-bignum`** (`280a220986a0bc6249248187717a771153d073db`):
  - `x86/proofs/instruction.ml:177-220, 275-464`; `x86/proofs/decode.ml:168-406, 777-1050, 1505-1508, 2912-2950, 3384-3392`; `x86/proofs/x86.ml:68-69, 330-336, 2606-2632, 2698-2712, 2811-2855`.
- **`acl2/acl2`** (`08bec1884997560686932229dbfe458c1bba34bf`) & **`rems-project/sail-x86-from-acl2`** (`0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf`):
  - `books/projects/x86isa/machine/evex-opcodes-dispatch.lisp:81-353`; `books/projects/x86isa/machine/dispatch-creator.lisp:41, 138-151, 210-415`; `books/projects/x86isa/machine/inst-listing.lisp:598-618` (and all `1,375` `:EVEX` `(INST ...)` blocks); `books/projects/x86isa/machine/register-readers-and-writers.lisp:781-1215`.
  - `sail-x86-from-acl2`: `model/registers.sail:121-127`; `model/evex_opcodes_dispatch.sail:1-9837`.
- **`rems-project/sail-arm`** (`5416ef6b43e9527c38dc71fb752259c1d01a47e1`), **`UQ-PAC/ASLp`** (`92e4fd949402056e16e3747e66922060be57ecc8`), **`leanprover/LNSym`** (`49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`), **`ARM-software/abi-aa`** (`9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7`), & **`joshlf/anneal`** (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):
  - `sail-arm`: `arm-v9.4-a/Makefile:25-97`; `arm-v9.4-a/lean/ArmExtras.lean:1-23`; `arm-v9.4-a/src/prelude.sail:349-354`; `arm-v9.4-a/src/impdefs.sail:853-854`; `arm-v9.4-a/src/termination_measures.sail:40-116`; `arm-v9.4-a/src/v8_base.sail:2700-2726, 6871-7012, 9504-9513, 29383-29649, 31132-31306`; `arm-v9.4-a/src/instrs64.sail:39038-39170`; `arm-v9.4-a/src/instrs64_sve.sail:15750-15810, 22090, 31051, 53467, 62790-62845, 66920`; `arm-v9.4-a/src/instrs64_sme.sail:4105-4158, 5231-5275, 5354-5412, 20629-20711, 33261-33310, 34007-34066, 35042-35090, 35940-35999`.
  - `ASLp`: `libASL/dis.ml:42, 712-995, 1080-1166, 1349-1435, 1610-1676`; `libASL/symbolic.ml:8, 491-555, 706-725, 983-986`; `libASL/rASL_check.ml:38-296`; `libASL/eval.ml:165-250, 441-445, 1313-1328`; `libASL/cpu.ml:33-98`; `bin/offline_sem.ml:1-29`.
  - `abi-aa`: `aapcs64/aapcs64.rst:2221-2767, 3204-3251`.
  - `anneal`: `trusted/audit/TrustedBoundary.lean:13-122, 229-314, 529-558`; `trusted/audit/src/lib.rs:61-157`.

### 2. Executed x86-64 `EVEX` / `AVX-VNNI` Machine-Code, Relocation, and `#UD` Probe (`Basis: execution`)

Assembled and inspected on Linux `x86_64` with `gcc (Debian 15.2.0-14) 15.2.0` and `GNU objdump (GNU Binutils for Debian) 2.47`:

```asm
.intel_syntax noprefix
.section .rodata.cst4,"aM",@progbits,4
.align 4
tap_const: .long 0x01fb113a
.text
.globl evex_probe
evex_probe:
    {vex}  vpdpbusd ymm1, ymm2, ymm3                        # c4 e2 6d 50 cb
    {evex} vpdpbusd ymm1, ymm2, ymm3                        # 62 f2 6d 28 50 cb
    vpdpbusd zmm16{k1}, zmm17, ZMMWORD PTR [rsi + 64]       # 62 e2 75 41 50 46 01 (disp8=0x01, N=64)
    vpdpbusd zmm16{k1}, zmm17, DWORD PTR [rsi + 64]{1to16}  # 62 e2 75 51 50 46 10 (disp8=0x10, N=4)
    vpdpbusd zmm16{k1}, zmm17, DWORD PTR [rip + tap_const]{1to16}
                                                            # R_X86_64_PC32 tap_const-0x4
    vpternlogd zmm23{k3}{z}, zmm24, DWORD PTR [rip + tap_const]{1to16}, 0xe4
                                                            # R_X86_64_PC32 tap_const-0x5
    vpmadd52luq zmm25{k4}{z}, zmm26, QWORD PTR [rcx + 8]{1to8} # 62 62 ad d4 b4 49 01
    vpshufbitqmb k5{k6}, zmm27, ZMMWORD PTR [r8 + 64]       # 62 d2 25 46 8f 68 01
    kmovb k1, eax                                           # c5 f9 92 c8 (VEX 2-byte!)
    # Illegal #UD forms:
    .byte 0x62, 0xa2, 0x75, 0xc0, 0x50, 0xc2                # {k0}{z} -> objdump: {bad}
    .byte 0x62, 0x41, 0x7f, 0xc9, 0x7f, 0x61, 0x01          # store {z} -> objdump: /(bad)
    .byte 0x62, 0xd2, 0x25, 0xc6, 0x8f, 0x68, 0x01          # k-dest {z} -> objdump: /(bad)
    .byte 0x62, 0xe2, 0x55, 0xd2, 0x8d, 0x67, 0x01          # VPERMB BCRC=1 (#UD in XED/as, missed by objdump!)
    .byte 0x62, 0xc2, 0x25, 0x46, 0x8f, 0x68, 0x01          # k-dest R'=0 -> objdump: (bad)
    ret
```

### 3. Executed `sail-arm` vs. ITU-T H.266 VVC ALF `SME2` Correspondence Probe (`Basis: execution + derived`)

Self-contained Python 3.13 executable transcription of `rems-project/sail-arm`'s `execute_ZIP_MZ_Z_4` (`instrs64_sme.sail:35046`), `execute_SDOT_ZA_ZZW_4x4` (`L20633`), `execute_MOVA_MZ_ZA4_1` (`L5358`), `execute_SQRSHR_Z_MZ4__` (`L34011`), and `SetPSTATE_ZA` (`v8_base.sail:29626`) composed per `FFmpeg` `inter_sme2.S:88-350` against scalar VVC H.266 §8.8.5.2 luma ALF across all `5` architectural SME `SVL`s (`w = 64`):

```text
SVL=128: UNDEFINED INSTRUCTION TRAP (zip {z12.d-z15.d} requires VL >= 4*64 = 256 bits!)
SVL=256 (entry ZA=0): exact_match=True
SVL=512 (entry ZA=0): exact_match=True
SVL=1024 (entry ZA=0): exact_match=True
SVL=2048 (entry ZA=0): exact_match=True
SVL=512 (entry PSTATE.ZA=1, dirty ZA=0x10000): mismatches=127/256 pixels
```

---

## Revalidation

To cheaply check whether upstream models or FFmpeg's `AVX-512` / `SVE2` / `SME2` implementations have changed without repeating full repository audits:

1. **Check `awslabs/s2n-bignum` and ACL2 `x86isa` `EVEX` Dispatch Activation (<5s):**
   - Inspect `awslabs/s2n-bignum` `x86/proofs/decode.ml` for `[0x62:8]` or `read_EVEX` inside `decode_aux` and `x86/proofs/instruction.ml` for `VPDPBUSD` / `VPERMB` / `VPMADD52LUQ` / `VPSHUFBITQMB`.
   - Inspect `acl2/acl2` `books/projects/x86isa/machine/inst-listing.lisp` for any `(INST ... :EVEX ...)` block whose fourth positional argument is non-`NIL`.
2. **Check `rems-project/sail-arm` Lean Termination & `while` Loop Count (<5s):**
   - Diff `arm-v9.4-a/lean/ArmExtras.lean` (checking whether `sorry` remains in `decreasing_trivial`) and `arm-v9.4-a/src/termination_measures.sail` (checking whether `$iftarget coq` still gates `while` measures), and scan `arm-v9.4-a/src/instrs64_{sve,sme}.sail` for `\b(while|repeat)\b` (`1` and `0` occurrences respectively at `5416ef6b43e9527c38dc71fb752259c1d01a47e1`).
3. **Check `UQ-PAC/ASLp` `Stmt_While` and `LUTI2` `rASL` Invariants (<5s):**
   - Inspect `libASL/dis.ml` around `Stmt_While` (`Stmt_Assert(expr_false, loc)` at `92e4fd949402056e16e3747e66922060be57ecc8`) and `libASL/rASL_check.ml` around `Expr_Slices` (`is_const(l) && is_const(w)`).
4. **Check `FFmpeg` `SME2` ABI and `SVL >= 256` Guards (<5s):**
   - Inspect `FFmpeg/FFmpeg` `libavutil/aarch64/asm.S` (`sme_entry`), `libavutil/aarch64/cpu_sme.S` (`ff_aarch64_sme_length`), `libavcodec/aarch64/vvc/inter_sme2.S` (`zero {za}` placement and `zip {z12.d-z15.d}`), and `libavcodec/aarch64/vvc/dsp_init.c` (`have_sme2` dispatch) to verify whether `__arm_tpidr2_save`, prologue `zero {za}`, `rdsvl`, and an `SVL >= 256` check have been added.
