# x86-64, i686, AArch64, and ARMv7 SIMD ISA Formalizations: Sail, ASL/ASLp, ACL2, HOL, K, XED, and Lean 4 Comparison

## Summary

No single existing machine-readable ISA formalization simultaneously covers the full `x86_64`/`i686` and `aarch64`/`armv7` media SIMD instruction surface used by production video and audio codecs while translating cleanly into total, zero-axiom Lean 4 definitions (`Basis: source + derived`):

1. **x86-64 and i686 Formalization Split (`Basis: source`):**
   - **`kframework/X86-64-semantics`** (`592380aea04820ea11cfa5475b343f0257f2474e`, UIUC/NCSA) provides the broadest operational coverage of 64-bit Haswell user-mode media SIMD (`3,155` variants across `774` mnemonics, including `PADDSW`/`VPADDSW`, `PSUBUSB`/`VPSUBUSB`, `PACKUSWB`/`VPACKUSWB`, `PMADDWD`/`VPMADDWD`, `PMADDUBSW`/`VPMADDUBSW`, `PSHUFB`/`VPSHUFB`, `PHADDW`/`VPHADDW`, `VPERM2I128`, and `VZEROUPPER`), but omits `i686` 32-bit mode, `MMX`/`EMMS`, `LDMXCSR`/`STMXCSR`, and all `AVX-512` (`ZMM`/`EVEX`/`k0..k7`/`VPDPBUSD`/`VPERMB`), and emits unrolled `#ifMInt` bitvector ASTs (`512` nested branches in `vpshufb_ymm_ymm_ymm.k:12`) pinned to an older K compiler syntax.
   - **ACL2 `x86isa`** (`acl2/acl2@08bec1884997560686932229dbfe458c1bba34bf`, BSD-3-Clause, together with `rems-project/sail-x86-from-acl2@0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf`) uniquely formalizes **both 64-bit and `i686` 32-bit modes**, `MMX` aliasing over `x87` `ST0..ST7` with `EMMS`, `LDMXCSR`/`STMXCSR`, `ZMM0..ZMM31` (`512`-bit) state, `EVEX` (`#x62`) dispatch, `(V)PADDSB/SW`, `(V)PADDUSB/USW`, `(V)PSUB*`, `PACKSS/PACKUS`, and `(V)PMADDWD`, but lacks SSSE3/AVX2/AVX-512 byte permutations and VNNI dot products (`PSHUFB`/`VPSHUFB`, `PMADDUBSW`, `PHADDW`, `VPERMB`, `VPDPBUSD`, and `VZEROUPPER`).
   - **`awslabs/s2n-bignum`** (`280a220986a0bc6249248187717a771153d073db`, `Apache-2.0 OR ISC OR MIT-0`) formalizes a clean, HOL Light operational semantics over `32` `512`-bit `ZMM` registers plus `EVEX` opmasking (`evex_mask`, `x86/proofs/x86.ml:2612`) and includes `VPADDB/W/D`, `VPSUBB/W/D/Q`, `VPACKUSWB`, `VPMADDUBSW`, `VPMADDWD`, `VPMULHRSW`, `PSHUFB`/`VPSHUFB`, and `VZEROUPPER` (added for ML-KEM/ML-DSA), yet omits packed saturating add/sub (`PADDSB`/`PADDSW`/`PSUBUSB`), `PHADDW`, `VPDPBUSD`, `VPERMB`, `MXCSR`, floating-point SIMD, `MMX`, and `i686`.
   - **HOL4 / `L3`** (`coruus/L3@d6558e679a25ffaaf16a47a3189f8f8111e45e0c`, `HOL-Theorem-Prover/HOL@0c30bdb71aafd4e6a354f5b0b43fffbff6fa8d47`) models `MXCSR` and SSE floating-point (`ADDPS/PD`, `CMPPD`) in `x64` (`x64Script.sml:13-90, 2330-2402`) and 32-bit scalar integer in `x86` (`x86_astScript.sml:15-60`), with **zero** `MMX`, packed integer SSE2–SSE4.2, AVX2, or AVX-512.
   - **Intel XED / `XED-to-XML` / `uiCA`** (`intelxed/xed@0bcb6237345c5066726dcc08b3d87928df3b5b26`, Apache-2.0; `andreas-abel/XED-to-XML@56fe1b1c228c2407fbde6b2de24b7b39d1e8da9a`, Apache-2.0; `andreas-abel/uiCA@6ebeeab0f8705cae4b17a9362f9c65ef91f5cc44`, AGPL-3.0) supply authoritative encoding, operand-width, EVEX masking, and port/latency metadata through `AVX-512ICL`/`AVX-VNNI` (`VPDPBUSD`), but contain **no arithmetic value semantics**.

2. **AArch64 and ARMv7 Formalization Split (`Basis: source`):**
   - **`rems-project/sail-arm`** (`5416ef6b43e9527c38dc71fb752259c1d01a47e1`, **BSD-3-Clause-Clear** with explicit Arm Limited copyright grant, unlike raw Arm MRA XML under Arm's proprietary click-through license) and **Arm ASL / `UQ-PAC/aslp`** (`92e4fd949402056e16e3747e66922060be57ecc8`, BSD-3-Clause tool) cover the entire A64 and A32/T32 (`instrs32.sail`) instruction sets—including NEON, `DOTPROD`, `I8MM`, `SVE` (`instrs64_sve.sail`), `SVE2`, `SME` (`instrs64_sme.sail`), and `FPCR`/`FPSR.QC`—but direct Sail-to-Lean extraction (`gen_lean`) still emits `noncomputable` mutual definitions and `sorry` placeholders (`ArmExtras.lean`), while `ASLp` eliminates dynamic width polymorphism by partial-evaluating ASL per opcode into loop-free Reduced ASL (`rASL`).
   - **`leanprover/LNSym`** (`49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`, Apache-2.0) and **`s2n-bignum` `arm`** provide clean, kernel-checked `BitVec`/`word` semantics in Lean 4 and HOL Light (`TBL`/`TBX` in `LNSym`; `TBL`, `SMLAL`, `SQDMULH`, `ADDV`, `UZP1`/`ZIP1`/`TRN1` in `s2n-bignum`), yet both omit `FPCR`/`FPSR` (`QC` sticky saturation bit), `SQADD`/`UQSUB`/`SQXTUN`, `SDOT`/`UDOT`, `ADDP`, all `SVE`/`SVE2`, and all 32-bit `armv7`.
   - **`L3` `arm-v7`** (`arm-vfp.spec`, `arm-iset.spec`) models `ARMv6` in-GPR SIMD (`QADD16`, `SADD16`) and scalar `VFPv3-D32` with `FPSCR.QC` (`arm-vfp.spec:20-53`), but omits 128-bit `NEON` (`Q0..Q15`, `VTBL`, `VQADD`), while `L3` `arm-v8` stubs out AArch64 SIMD/FP entirely.

3. **Critical Cross-ISA Equivalence Hazards (`Basis: normative + source + execution`):**
   Proving media SIMD kernels equivalent across `x86_64` and `aarch64`—or upgrading SSSE3/AVX2 filters to `AVX-512ICL`—exposes four non-obvious semantic boundaries verified by source inspection and native `x86_64` execution: (a) byte shuffle out-of-range indexing (`PSHUFB`/`VPSHUFB` tests only bit `7 == 1` to zero and wraps indices `0x10..0x7F` modulo `16` within isolated 128-bit lanes, whereas single-register AArch64 `TBL` zeroes every unsigned index `>= 16` and `TBX` preserves `Rd`); (b) intermediate saturation in multiply-add (`PMADDUBSW + PMADDWD` clamps intermediate `u8 * i8` pairs to signed `int16` `[-32768, +32767]` before summing, whereas `VPDPBUSD` and AArch64 `USDOT` accumulate exact 4-way sums in `int32`, agreeing **only** under codec filter-coefficient $L_1$ bounds); (c) `PMADDWD` signed overflow at `(-32768, -32768)` wraps `int32` to `-2147483648` (`0x80000000`); and (d) legacy SSE instructions preserve bits `[MAXVL-1:128]` whereas VEX/EVEX encodings zero-extend to `MAXVL`, coupled with AArch64 `SQADD`/`SQXTUN` mutating sticky `FPSR.QC` while x86 `PADDSW`/`PACKUSWB` are flagless.

---

## Applicability

This report governs the selection, adaptation, and trusted-computing-base (TCB) design of formal ISA semantics for verifying `x86_64`, `i686` (32-bit IA-32), `aarch64` (Armv8-A/v9-A A64), and `armv7` (AArch32 A32/T32) SIMD kernels—either as inline assembly, standalone `.asm`/`.S` object routines (NASM/YASM `x86inc.asm` or GAS), or compiler intrinsic lowerings (`core::arch::{x86_64, x86, aarch64, arm}`).

Relationship among examined subjects (`REPORT.json`):
- **`FFmpeg/FFmpeg`** (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) defines the target media SIMD workload: CPU capability flags (`libavutil/cpu.h:32-88`), NASM macro ABI and `vzeroupper` discipline (`libavutil/x86/x86inc.asm:374-1139`), and representative H.264, HEVC, VP9, VVC, and `swscale` SIMD kernels across `libavcodec/{x86,aarch64,arm}/`.
- **`kframework/X86-64-semantics`**, **`acl2/acl2`** (`books/projects/x86isa`), **`rems-project/sail-x86-from-acl2`**, **`coruus/L3`**, **`HOL-Theorem-Prover/HOL`**, **`awslabs/s2n-bignum`** (alongside **`cslib-community/bignum`** and **`AeneasVerif/kraken`**), **`intelxed/xed`**, **`andreas-abel/XED-to-XML`**, and **`andreas-abel/uiCA`** are compared as candidate specifications, decoders, and microarchitectural models for `x86_64`/`i686`.
- **`rems-project/sail-arm`**, **`UQ-PAC/aslp`**, **`rems-project/mra_tools`**, **`leanprover/LNSym`**, **`awslabs/s2n-bignum`**, and **`coruus/L3`** are compared as candidate specifications and lifters for `aarch64`/`armv7`.
- **Intel SDM (`325462`)** and **Arm ARM (`ARM DDI 0487`)** serve as the normative architectural authorities.

To avoid duplicating prior corpus analyses, this report cross-references rather than repeats:
- `asl-l3-lnsym-and-isa-verification-frameworks-lean-adaptation` for general `LNSym` state-monad mechanics, `ASLp` architecture, and `Islaris`/`CakeML` pipelines;
- `sail-isa-models-lean-backend-and-rv64d-decoding-framing` for `rems-project/sail` Lean backend code generation internals and `-lean-noncomputable` failure modes;
- `jasmin-s2n-bignum-cslib-and-verified-cryptographic-assembly` and `kraken-aarch64-x86-64-instruction-validation-and-rust-assembly-pilots` for cryptographic bignum proof tactics and Rust inline-assembly harness plumbing;
- `rvv-lmul-vtype-hazards-arm-sme-streaming-za-tiles-and-ffload-speculation` for Arm `SME` streaming SVE (`PSTATE.SM`) and `ZA` tile ABI save/restore hazards.

---

## Findings

### 1. Architectural Scope, Licensing, TCB Size, and Lean 4 Viability Across Formal Models

`Basis: source + documentation + derived`

Direct inspection of licenses, AST definitions, decoder generators, and theorem-prover backends across all twelve formal model repositories reveals a sharp trade-off between **SIMD breadth**, **redistribution licensing**, and **Lean 4 kernel mechanization cost**:

| Framework / Repository (Pinned SHA) | Target Modes & Vector Extensions Modeled | License & Redistribution Constraints | TCB & Proof Kernel Footprint | Lean 4 Translation Viability |
| :--- | :--- | :--- | :--- | :--- |
| **`kframework/X86-64-semantics`** (`592380ae`) | `x86_64` 64-bit user-mode Haswell (`SSE`–`SSE4.2`, `AVX`, `AVX2`, `FMA3`, `BMI1/2`, `AES-NI`/`PCLMULQDQ`; **0** `i686`, **0** `MMX`, **0** `AVX-512`) | **UIUC / NCSA** (`LICENSE.md:1-28`), permissive BSD-like | Unverified Perl/Stoke stratification scripts (`scripts/process_spec.pl`) + legacy K Java/LLVM backend + Z3 | **Low for direct AST import; Medium as differential test oracle.** Rules expand 256-bit shuffles into single-line `#ifMInt` trees (`512` nested branches in `vpshufb_ymm_ymm_ymm.k:12`) and require legacy `kframework/k` syntax (`README.md:20-25`). |
| **ACL2 `x86isa`** (`acl2/acl2@08bec188`) | `x86_64` 64-bit **and** `i686` 32-bit user + system paging (`MMX`/`EMMS`, `SSE`/`SSE2`, partial `AVX`, `EVEX`/`ZMM0..31` infrastructure, `MXCSR` via `rtl/rel11`) | **BSD-3-Clause** (`evex-opcodes-dispatch.lisp:3-35`, `register-readers-and-writers.lisp:3-36`) | Common Lisp (SBCL) + ACL2 untrusted-kernel prover (`:ttags (:undef-flg :syscall-exec)` in `pack.lisp:46`, `two-byte-opcodes-dispatch.lisp:41`) | **Medium-High via `sail-x86-from-acl2` or direct Lisp-to-Lean.** Specifications (`simd-add-signed-sat-spec`, `packus-spec`, `simd-muladd-spec`) are clean recursive bit-slice functions rather than unrolled trees. |
| **`rems-project/sail-x86-from-acl2`** (`0c6c023d`) | Automated Sail snapshot of ACL2 `x86isa` (`model/registers.sail:127` `zmms : vector(32, dec, bits(512))`, `vex_opcodes_dispatch.sail`, `evex_opcodes_dispatch.sail`) | **BSD-2-Clause** translator + **BSD-3-Clause** generated `model/*.sail` (`LICENCE:1-37`) | Python macro-expander querying live ACL2 (`README.md:21-35`) + 10 handwritten `.sail` support files + Sail compiler | **Medium.** Bridges ACL2 `x86isa` to `sail -lean`, inheriting ACL2's exact `MMX`/`i686`/`ZMM` state and exact SSSE3/AVX2/VNNI gaps, plus Sail's monadic Lean output overhead. |
| **`awslabs/s2n-bignum`** (`280a2209`) | `x86_64` (`ZMM0..31` `512`-bit + `EVEX` masks, SSE2/SSSE3/AVX2/AVX-512 subset) & `aarch64` (`Q0..31` `128`-bit NEON + Crypto subset); **0** `i686`/`armv7`/`SVE` | **`Apache-2.0 OR ISC OR MIT-0`** (`x86/proofs/base.ml:3`, `arm/proofs/base.ml:3`) | Small LCF-style HOL Light kernel (~400 LOC OCaml) + ELF object-byte loader (`SOUNDNESS.md:25-27`) + CI hardware co-sim (`common/cosim.ml`) | **High (proven path).** `cslib-community/bignum` (`1b3952cb`) and `AeneasVerif/kraken` (`3acb3ee4`) already port `s2n-bignum` specs; instruction combinators in `x86.ml`/`arm/proofs/instruction.ml` map 1-to-1 to Lean 4 `BitVec`. |
| **`coruus/L3` & HOL4** (`d6558e67` / `0c30bdb7`) | `x86_64` scalar + FP SSE (`x64.spec`); `i686` scalar (`x86_astScript.sml`); `armv7` A32/T32 + ARMv6 GPR-SIMD + scalar `VFPv3-D32` (`arm-vfp.spec`); `armv8` scalar (`v8-iset.spec`) | **BSD-3-Clause** (`isa-models/COPYRIGHT:1-34`, `HOL/COPYRIGHT:1-33`) | SML L3 compiler + HOL4 LCF kernel | **Low for media SIMD.** Zero packed integer SSE2/AVX2 on x86 and zero 128-bit NEON/SVE on Arm; useful only as a reference for legacy 32-bit `ARMv7` A32/T32 + `VFPv3` control state (`FPSCR`). |
| **`intelxed/xed` + `XED-to-XML` + `uiCA`** (`0bcb6237` / `56fe1b1c` / `6ebeeab0`) | Full `x86`/`x86_64` encoding/iforms (`MMX` through `AVX-512ICL`, `AVX-VNNI`, `AMX`) + Intel Core port/latency models (`uops.info`) | **Apache-2.0** (`xed`, `XED-to-XML:LICENSE:2`); **AGPL-3.0** (`uiCA:LICENSE:1`) | C/Python table generators; **no theorem-prover kernel** | **High for verified decoder/encoder generation (`xed`/`XED-to-XML` only); N/A for ALU semantics.** `uiCA` is AGPL-3.0 copyleft and must remain an external unlinked analysis tool. |
| **Arm `ASL` + `mra_tools` + `UQ-PAC/aslp`** (`94131760` / `92e4fd94`) | Full `aarch64` A64 + `armv7`/`armv8` A32/T32 (`NEON`, `VFP`, `DOTPROD`, `I8MM`, `SVE`, `SVE2`, `SME`) | Tools: **BSD-3-Clause** (`eval.ml:5`); Raw Arm MRA XML: **Proprietary Arm EULA** (restricts redistribution without Arm grant) | OCaml `libASL` interpreter + `ASLp` symbolic partial evaluator (`libASL/symbolic.ml`, `1,128` LOC) | **High via `ASLp` `rASL` offline lifting, subject to Arm XML licensing.** `ASLp` resolves `VL`/width loops per opcode (`bin/offline_sem.ml:5-12`), emitting flat bitvector statements ideal for Lean `BitVec`. |
| **`rems-project/sail-arm`** (`5416ef6b`) | Full `arm-v8.5-a` & `arm-v9.4-a`: A64 (`instrs64.sail`), A32/T32 (`instrs32.sail`), `SVE`/`SVE2` (`instrs64_sve.sail`), `SME` (`instrs64_sme.sail`) | **BSD-3-Clause-Clear** with explicit Arm Limited copyright grant (`arm-v9.4-a/LICENSE:1-37`; no patent grant `L26`) | `asl_to_sail` + Sail compiler (`arm-v9.4-a/Makefile:25-45`) | **Medium (blocked on full-monolith `gen_lean`, viable via per-instruction slicing).** Solves the Arm redistribution problem cleanly, but monolithic `gen_lean` emits `noncomputable` + `sorry` (`sail-isa-models-lean-backend-and-rv64d-decoding-framing`). |
| **`leanprover/LNSym`** (`49f8a1d9`) | `aarch64` user-mode subset: A64 GP + 128-bit `NEON`/Crypto (`TBL`/`TBX`, `ADD`/`SUB`, bitwise, `TRN1/2`, `REV*`, `EXT`, `PMULL`, `AES`, `SHA512`); **0** `SVE`, **0** `armv7` | **Apache-2.0** (`Arm/State.lean:1-4`) | **Zero external TCB beyond Lean 4 kernel** (zero Mathlib dependency) + hardware co-sim (`Arm/Insts/CosimM.lean`) | **Native Lean 4.** Immediate foundation for AArch64 Lean verification (`@[state_simp_rules]`), requiring extension for `FPCR`/`FPSR.QC`, saturating/multiply-accumulate NEON, and SVE2. |

Key architectural observations from source inspection:
- **Licensing Asymmetry on Arm (`Basis: source`):** `rems-project/sail-arm` (`arm-v9.4-a/LICENSE:3-27` and `arm-v9.4-a/README.md:11-18`) was generated from a plain-ASL 2023-03 snapshot provided directly by Arm Limited and released under **BSD-3-Clause-Clear** (`Copyright (c) 2023 Arm Limited ...`). Any open-source Lean 4 ISA library that extracts instruction semantics from `rems-project/sail-arm` inherits explicit open-source redistribution permission (excluding patent grants), whereas scraping Arm's website XML via `rems-project/mra_tools` (`941317606f36580f668498889abc6301ed8222d8`) binds downstream artifacts to Arm's proprietary specification EULA unless separately licensed.
- **Why `kframework/X86-64-semantics` Struggles in Interactive Theorem Provers (`Basis: source`):** In `kframework/X86-64-semantics/semantics/registerInstructions/vpshufb_ymm_ymm_ymm.k:1-15`, stratification (`Dasgupta et al., PLDI 2019`, DOI `10.1145/3314221.3314601`) synthesizes semantics for wider vector instructions from 128-bit base templates by fully unrolling every byte lane into nested `#ifMInt eqMInt(extractMInt(...), mi(4, k))` expressions—producing a single 19,000-character rewrite rule on line 12 with `32 * 16 = 512` conditional branches. Importing such unrolled rules directly into Lean 4 causes quadratic kernel `whnf` blowups compared to parametric lane combinators such as `LNSym`'s `binary_vector_op_aux` (`Arm/Insts/DPSFP/Advanced_simd_three_same.lean:20-32`) or ACL2's `simd-add-signed-sat-spec` (`padd.lisp:139-157`).

---

### 2. FFmpeg Hot Media SIMD Primitives: Exact Instruction Coverage Audit

`Basis: source`

Inspection of `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` establishes the six mandatory SIMD instruction families across H.264 (`libavcodec/x86/h264_idct.asm`, `libavcodec/aarch64/h264idct_neon.S`, `libavcodec/arm/h264idct_neon.S`), HEVC (`libavcodec/x86/hevc/mc.asm`, `libavcodec/aarch64/hevcdsp_idct_neon.S`), VP9 (`libavcodec/x86/vp9mc.asm`, `libavcodec/aarch64/vp9mc_neon.S`, `libavcodec/aarch64/vp9mc_sve.S`), and VVC (`libavcodec/x86/vvc/{mc,sad}.asm`, `libavcodec/aarch64/vvc/alf.S`), governed by capability flags in `libavutil/cpu.h:32-88` and register/epilogue macros in `libavutil/x86/x86inc.asm:374, 944-967, 1085-1139`:

1. **Packed Saturating Arithmetic & Narrowing Pack:**
   - FFmpeg kernels: `paddsw` (`h264_idct.asm:394`, `vp9mc.asm:238`, `hevc/mc.asm:685`, `vvc/mc.asm:134`), `psubusb` (`h264_idct.asm:248`), `packuswb` (`h264_idct.asm:231`, `vp9mc.asm:243`, `hevc/mc.asm:702`, `vvc/mc.asm:174`), AArch64 `sqadd` (`vp9mc_neon.S:203-204`, `hevcdsp_idct_neon.S:51-52`), and `sqxtun` (`h264idct_neon.S:68`, `vvc/alf.S:145`).
2. **Packed Widening Multiply-Add & 8-bit Dot Products (VNNI / DotProd / I8MM):**
   - FFmpeg kernels: `pmaddwd` (`h264_idct.asm:583`, `hevc/mc.asm:551`, `vvc/sad.asm:91`, `vvc/mc.asm:144`), `pmaddubsw` (`vp9mc.asm:271`, `hevc/mc.asm:542`), `vpdpbusd` under `avx512icl` (`vp9mc.asm:861`, `hevc/mc.asm:1288`), and AArch64 `smlal` (`vvc/alf.S:61`, `hevcdsp_idct_neon.S:246-248`) plus `.arch_extension dotprod` and `.arch_extension i8mm` (`libavutil/aarch64/asm.S:52, 60`).
3. **In-Register Byte Shuffles & Cross-Lane Table Lookups:**
   - FFmpeg kernels: `pshufb`/`vpshufb` (`vp9mc.asm:269`), full-register 512-bit `vpermb` (`vp9mc.asm:848`, `hevc/mc.asm:1286`), and AArch64 `tbl`/`tbx` + `uzp1/2`/`trn1/2`/`zip1/2`.
4. **Horizontal Pairwise Reductions:**
   - `phaddw`/`vphaddw`, `phaddd`/`vphaddd`, `phaddsw`/`vphaddsw` on x86; `addp` (pairwise) and `addv`/`saddlv` (across-vector) on AArch64.
5. **Predicated / Masked Vector Operations (`AVX-512` `k1..k7` vs `SVE`/`SVE2` `P0..P15`):**
   - FFmpeg kernels: `kmovb k1, r6d` (`vp9mc.asm:1192`) with `{k1}` merge/zero masking under `INIT_ZMM avx512icl` (`x86inc.asm:967, 1131`), and `.arch_extension sve` / `.arch_extension sve2` (`libavutil/aarch64/asm.S:88, 96`; `vp9mc_sve.S`, `me_cmp_sve.S`).
6. **Vector Upper-State Transitions & FP/SIMD Control/Status Registers:**
   - `vzeroupper` (`x86inc.asm:374, 617-618, 1073`, `vp9mc.asm:1181`), `EMMS` after `INIT_MMX` (`x86inc.asm:1085`), x86 `MXCSR` (`RC`, `FTZ`, `DAZ`), AArch64 `FPCR`/`FPSR` (specifically cumulative saturation bit `FPSR.QC` bit 27), and ARMv7 `FPSCR`.

The exact verified coverage across the formal ISA models is:

| SIMD Primitive / Control Feature | `K-x86-64` (`592380ae`) | ACL2 `x86isa` (`08bec188`) | `s2n-bignum` x86 (`280a2209`) | HOL4 / `L3` x86 & Arm (`d6558e67`) | `sail-arm` (`5416ef6b`) / `ASLp` (`92e4fd94`) | `s2n-bignum` Arm (`280a2209`) | `LNSym` (`49f8a1d9`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Saturating Add/Sub & Narrowing Pack** (`(v)paddsw`, `(v)psubusb`, `(v)packuswb` / `sqadd`, `uqsub`, `sqxtun`) | **Full** (`SSE2` + `AVX2` `.k` rules) | **Full** (`MMX`, `SSE2`, `VEX` in `padd.lisp:94-157, 277-373`, `psub.lisp:93-152`, `pack.lisp:108-221`) | **Partial:** `VPACKUSWB` (`x86.ml:1972`), wrapping `VPADDB/W/D` & `VPSUBB/W/D/Q`; **0** `PADDSW`/`PSUBUSB` | **Missing** on x86 & Arm NEON (only ARMv6 GPR `QADD16` in `arm-iset.spec:900`) | **Full** (`NEON`, `A32/T32`, `SVE`, `SVE2`, sets `FPSR.QC`) | **Missing** `SQADD`/`UQSUB`/`SQXTUN` (has `SQDMULH` at `instruction.ml:1751` without `QC`) | **Missing** (wrapping `ADD`/`SUB` only in `Advanced_simd_three_same.lean:60-70`) |
| **Multiply-Add & Dot-Product** (`(v)pmaddwd`, `(v)pmaddubsw`, `vpdpbusd` / `smlal`, `sdot`, `usdot`) | **Partial:** `(v)pmaddwd` + `(v)pmaddubsw` (`SSE2`/`SSSE3`/`AVX2`); **0** `vpdpbusd` | **Partial:** `MMX`/`SSE2`/`VEX` `(V)PMADDWD` (`pmadd.lisp:50-114`); **0** `PMADDUBSW`, **0** `VPDPBUSD` | **Partial:** `VPMADDUBSW` (`x86.ml:1995`), `VPMADDWD` (`L2018`), `VPMULHRSW` (`instruction.ml:434`); **0** `VPDPBUSD` | **Missing** (`0` integer SIMD multiply-accumulate) | **Full** (`SMLAL`, `SDOT`, `UDOT`, `USDOT` `I8MM`, `SMMLA`, `SVE` dot products) | **Partial:** `SMLAL`/`SMLAL2` (`instruction.ml:2026-2047`), `UMLAL`, `PMULL`; **0** `SDOT`/`UDOT`/`USDOT` | **Partial:** `PMULL`/`PMULL2` only (`Advanced_simd_three_different.lean:67`); **0** `SMLAL`/`SDOT` |
| **Byte Shuffles & Permutes** (`(v)pshufb`, `vpermb`, `vperm2i128` / `tbl`, `tbx`, `trn`, `uzp`, `zip`) | **Partial:** `pshufb`, `vpshufb`, `vperm2i128`; **0** `vpermb` (`AVX-512VBMI`) | **Partial:** FP `SHUFPS/PD`, `UNPCK*` (`fp/shuffle-and-unpack.lisp:91-489`); **0** `PSHUFB`/`VPSHUFB`/`VPERMB` | **Partial:** `PSHUFB` (`x86.ml:1468`), `VPSHUFB` (`L2290`); **0** `VPERMB` | **Missing** (`0` `PSHUFB`, `0` `VTBL`/`TBL`) | **Full** (`TBL`/`TBX` 1–4 regs, `TRN`, `UZP`, `ZIP`, `SVE` `TBL`) | **Partial:** `TBL`/`TBL2` (`instruction.ml:2879-2893`), `UZP1/2`, `ZIP1/2`, `TRN1/2`; **0** `TBX` | **Partial:** `TBL`/`TBX` 1–4 regs (`Advanced_simd_table_lookup.lean:47-68`), `TRN1/2` (`Advanced_simd_permute.lean:52-57`, `UZP`/`ZIP` return `Unimplemented`) |
| **Horizontal Adds** (`(v)phaddw/d/sw` / `addp`, `addv`) | **Full** (`SSSE3` + `AVX2` `(v)phaddw/d/sw`) | **Missing** (`0` `PHADD*`) | **Missing** (`0` `PHADD*`) | **Missing** | **Full** (`ADDP` vector/scalar, `ADDV`, `SADDLV`, `UADDLV`) | **Partial:** `ADDV` (`instruction.ml:2625`); **0** `ADDP` | **Missing** (`0` `ADDP`/`ADDV`) |
| **Masked AVX-512 / SVE Predication** (`k1..k7`, `EVEX` `{z}` / `P0..P15`, `FFR`) | **Missing** (`0` `ZMM`, `0` `k0..k7`, `0` `EVEX`) | **Infrastructure + partial ops:** `ZMM0..31` (`register-readers-and-writers.lisp:781`) + `EVEX` `#x62` decoder (`evex-opcodes-dispatch.lisp:44-80`) | **Infrastructure + crypto subset:** `ZMM0..31` (`x86.ml:68`) + `evex_mask` / `evex_expand_mask` (`x86.ml:2612-2617`) | **Missing** | **Full** (`instrs64_sve.sail`, `instrs64_sme.sail`; `P0..P15`, `FFR`, merging `/m` & zeroing `/z`) | **Missing** (`128`-bit `Q0..31` only, `instruction.ml:27`) | **Missing** (`128`-bit `SFP` state only) |
| **Upper State, `MXCSR`/`FPCR`/`FPSR`, & 32-bit Legacy** (`vzeroupper`, `emms`, `i686`, `armv7`) | **Partial:** `vzeroupper` (`vzeroupper.k:11-43`); **0** `ldmxcsr`/`stmxcsr`, **0** `emms`, **0** `i686` | **Strongest x86 state:** `i686` 32-bit (`register-readers-and-writers.lisp:113-271`), `MMX`+`EMMS` (`emms.lisp:47`), `LDMXCSR`/`STMXCSR` (`fp/mxcsr.lisp:54-63`); **0** `vzeroupper` | **Partial:** `VZEROUPPER` (`x86.ml:1014`) + VEX vs legacy SSE `READ_YMM_SSE_EQUIV` (`base.ml:61-62`); **0** `MXCSR`, **0** `MMX`/`i686` | **Partial:** `MXCSR` record (`x64Script.sml:13-16`); `i686` scalar (`x86_astScript.sml`); `armv7` `FPSCR.QC` (`arm-vfp.spec:25`) | **Full:** `A64` + `A32/T32` (`instrs32.sail`), `FPCR`, `FPSR.QC`, `FPSCR` | **Missing** `FPCR`/`FPSR` (`instruction.ml:24-31`) and `armv7` | **Missing** `FPCR`/`FPSR` and `armv7` |

---

### 3. Cross-ISA Semantic Divergence Traps and Hardware Execution Witnesses

`Basis: normative + source + execution`

Media codecs routinely treat an `x86_64` kernel (`libavcodec/x86/*.asm`), an `aarch64` NEON kernel (`libavcodec/aarch64/*.S`), and a scalar C reference function as computing the same mathematical function on pixel/coefficient arrays. Formal source inspection and native `x86_64` execution (`gcc (Debian 15.2.0-14) 15.2.0 -O2 -mavx2`) expose five concrete semantic divergences that break naive equivalence specifications:

1. **Byte Table Lookup Index Semantics and the 128-Bit Lane Wall (`PSHUFB`/`VPSHUFB`/`VPERMB` vs `TBL`/`TBX`):**
   - **x86 `PSHUFB` / `VPSHUFB` (`kframework/X86-64-semantics/semantics/registerInstructions/vpshufb_ymm_ymm_ymm.k:12`, `s2n-bignum/x86/proofs/x86.ml:2290`, Intel SDM Vol. 2B):** Each control byte `c` checks **only bit 7 (`c & 0x80`)** to decide zeroing. When `c & 0x80 == 0`, `PSHUFB` (`XMM`) selects byte `c & 0x0F` (`bits [3:0]`), and `VPSHUFB` (`YMM`/`ZMM`) selects byte `(lane_128 * 16) + (c & 0x0F)`—meaning indices `0x10..0x7F` **do not zero** (they alias `0x00..0x0F` within the same 128-bit lane), and upper 128-bit lanes cannot read bytes `0..15` (`VPERMB` under `AVX-512VBMI` removes the lane wall, indexing `c & 0x3F` across all 64 bytes without MSB zeroing!).
   - **AArch64 `TBL` / `TBX` (`leanprover/LNSym/Arm/Insts/DPSFP/Advanced_simd_table_lookup.lean:36-58`, Arm ARM C7.2.337):** `tblx_aux` extracts the **full unsigned 8-bit integer** `let index := (elem_get indices i 8).toNat` and tests `if index < 16 * regs` (`16`, `32`, `48`, or `64` for 1–4 table registers). Out-of-range indices `16 * regs .. 255` write `0` in `TBL` (`is_tbl := inst.op = 0b0#1`) or preserve the prior destination byte `Rd` in `TBX` (`L55-57`).
   - **Hardware Execution Witness (`Basis: execution`):** On native `x86_64` silicon (`x86_simd_probe.c`), feeding `tbl[i] = 0xA0 + i` and control bytes `ctl[0] = 0x03`, `ctl[1] = 0x13`, `ctl[2] = 0x83`, `ctl[16] = 0x03`, `ctl[17] = 0x13` to `vpshufb` produces `out[0] = 0xa3`, `out[1] = 0xa3`, `out[2] = 0x00`, `out[16] = 0xb3`, `out[17] = 0xb3`. For any control byte in `0x10..0x7F` (such as `0x13`), 1-register `VPSHUFB` (`0xa3`) and 1-register AArch64 `TBL` (`0x00`) disagree! Consequently, cross-ISA equivalence proofs over dynamic index vectors require the precondition $\forall i,\; \text{ctl}[i] \in [0, 15] \cup [128, 255]$.

2. **Intermediate `int16` Saturation in `PMADDUBSW + PMADDWD` vs Exact `int32` Accumulation in `VPDPBUSD` / `USDOT`:**
   - In `FFmpeg/FFmpeg` 8-tap motion-compensation filters (`libavcodec/x86/vp9mc.asm:271` vs `L861`; `libavcodec/x86/hevc/mc.asm:542-551` vs `L1286-1288`), SSSE3/AVX2 paths compute $\text{pmaddwd}(\text{pmaddubsw}(u, c), \mathbf{1}_{16})$ while `avx512icl` upgrades the same filter to `vpdpbusd`.
   - `PMADDUBSW` (`x86/proofs/x86.ml:1995`) computes `sat_i16(u[2k]*c[2k] + u[2k+1]*c[2k+1])` **with signed 16-bit saturation to `[-32768, +32767]`** before `PMADDWD` adds adjacent pairs into `int32`, whereas `VPDPBUSD` (`intelxed/xed` `datafiles/avx-vnni/avx-vnni-isa.xed.txt:28-43`) and AArch64 `USDOT` (`FEAT_I8MM`) accumulate $\sum_{j=0}^{3} u_{4k+j} c_{4k+j}$ directly into `int32` **without** intermediate 16-bit saturation.
   - **Hardware Execution Witness (`Basis: execution`):** On `u = [255, 255, 255, 255]` (`0xFF`) and `c = [127, 127, 127, 127]`, `255 * 127 + 255 * 127 = 64,770` clamps to `32,767` in `pmaddubsw`, so `pmaddubsw + pmaddwd` outputs `65,534` while `vpdpbusd` outputs `129,540`! Equivalence between FFmpeg's AVX2 and `AVX512ICL` motion-compensation kernels holds **if and only if** the filter tap pairs satisfy $255 \cdot (|c_{2k}| + |c_{2k+1}|) \le 32767$ (for positive pairs, $c_{2k} + c_{2k+1} \le 128$), which holds for normative HEVC (`[-1, 4, -11, 40, 40, -11, 4, -1]`, max adjacent pair $40 + 40 = 80 \le 128$) and VP9 8-tap filters (`max pair <= 128` except sharp/bilinear degenerate cases handled separately). Any formal equivalence proof must encode this tap-sum invariant explicitly.

3. **`PMADDWD` Corner Overflow at `(-32768, -32768)` (`Basis: source + execution`):**
   - Each 32-bit lane of `PMADDWD` computes $a_{2k} b_{2k} + a_{2k+1} b_{2k+1}$ for $a_j, b_j \in [-32768, 32767]$. For every input **except** $a_{2k} = b_{2k} = a_{2k+1} = b_{2k+1} = -32768$, the mathematical sum fits in signed `int32`. At all-`-32768`, $(-32768)^2 + (-32768)^2 = 2^{30} + 2^{30} = +2^{31}$, which wraps modulo $2^{32}$ to `-2147483648` (`0x80000000`), verified by `x86_simd_probe` (`PMADDWD_MIN16_WRAP: -2147483648 (0x80000000)`). IDCT and motion-compensation proofs using `PMADDWD` must exclude simultaneous `-32768` pairs via coefficient range invariants.

4. **Legacy SSE Upper-Lane Preservation vs VEX/EVEX Zero-Extension and `vzeroupper` (`Basis: source + execution`):**
   - Both `kframework/X86-64-semantics` (`pshufb_xmm_xmm.k:12` `extractMInt(getParentValue(R2, RSMap), 0, 128)` vs `vpshufb`) and `s2n-bignum` (`x86/proofs/x86.ml:200-206`, `x86/proofs/base.ml:61-62` `READ_YMM_SSE_EQUIV`) formalize that legacy non-VEX SSE writes leave bits `[MAXVL-1:128]` unmodified, whereas 128-bit VEX/EVEX writes zero bits `[MAXVL-1:128]` (confirmed on hardware: `SSE_LEGACY_PADDD_UPPER128: cafebabe deadbeef 12345678 87654321` vs `VEX_VPADDD_UPPER128: 00000000 00000000 00000000 00000000`).
   - FFmpeg's `libavutil/x86/x86inc.asm:374, 617-618, 1073` codifies the architectural/microarchitectural state boundary: `%define vzeroupper_required (mmsize > 16 && (ARCH_X86_64 == 0 || xmm_regs_used > 16 || notcpuflag(avx512)))` and notes on line 1073 (`Prefer registers 16-31 over 0-15 to avoid having to use vzeroupper`) that `EVEX` writes exclusively to `ZMM16..ZMM31`/`YMM16..YMM31` do not dirty the architectural `YMM0..YMM15` upper-half state machine (`XCR0.YMM_Hi128`), avoiding SSE-transition stalls without `vzeroupper`.

5. **Sticky Saturation Side Effects (`FPSR.QC` vs Flagless x86 Saturation) and `Q15` Rounding (`Basis: normative + source + execution`):**
   - x86 `PADDSW`, `PSUBUSB`, `PACKUSWB`, and `PMULHRSW` modify **zero** architectural flags (`RFLAGS` and `MXCSR` are untouched). By contrast, AArch64 `SQADD`, `UQSUB`, `SQXTN`, `SQXTUN`, and `SQRDMULH` set the cumulative sticky saturation bit `FPSR.QC` (`bit 27`, modeled in `sail-arm` and `L3` `arm-vfp.spec:25`, but **omitted** from `ArmState` in `LNSym` `Arm/State.lean` and `s2n-bignum` `arm/proofs/instruction.ml:24-31`!). Any frame condition or ABI contract that treats `FPSR` as callee-preserved or observable will reject NEON saturating kernels unless `FPSR.QC` is explicitly designated caller-clobbered (matching AAPCS64). Furthermore, native `x86_64` execution confirms `PMULHRSW(-32768, -32768) = -32768 (0x8000)` (wrapping), whereas AArch64 `SQRDMULH(-32768, -32768) = +32767 (0x7FFF)` (saturating and setting `FPSR.QC = 1`).

---

### 4. Verification Priority Stack Implications for Media SIMD Kernels

`Basis: derived + source`

Evaluating the candidate ISA formalizations against a four-tier media verification stack clarifies exactly how much ISA machinery each assurance level requires:

1. **Tier 1 — Memory Safety and Undefined-Behavior Freedom (UB-Freedom):**
   - Requires modeling effective address calculation (`ModR/M` + `SIB` + segment/canonicality on x86; post-index/pre-index/vector-list addressing on AArch64), alignment traps (`MOVDQA` vs `MOVDQU`, `AlignmentFault`), masked fault suppression (`EVEX` `{k1}` masked loads and `SVE` first-faulting loads `LDFF1` via `FFR`), ABI register clobbers (`Win64` `XMM6..XMM15` callee-save in `x86inc.asm:612, 857`; AAPCS64 `D8..D15` low 64 bits callee-save as seen in `s2n-bignum/arm/proofs/mlkem_basemul_k2.ml:20-23`), and `EMMS` x87 tag reset on legacy `i686` `MMX`.
   - **Model Sufficiency:** `s2n-bignum`'s `common/safety.ml` + `tools/x86_safety_spec_generator.ml` and `LNSym` already discharge Tier 1 for fixed-width 64-bit `SSE2`/`AVX2`/`NEON` kernels; `EVEX` masked-load fault suppression and `SVE` `FFR` require `sail-arm` / `ASLp` or extending `s2n-bignum`'s `evex_mask` memory rules.

2. **Tier 2 — Trap / Panic Freedom (`#UD`, `#GP`, `#NM`, `StateError.Illegal`):**
   - Requires exact opcode/prefix legality decoding: VEX/EVEX `L` vector-length combinations, `EVEX` `aaa != 0` opmask restrictions (e.g., instructions forbidding `{z}` on memory stores), CPUID feature gating (`AV_CPU_FLAG_AVX512ICL` vs `AV_CPU_FLAG_AVXVNNI` in `libavutil/cpu.h:60-62`), and AArch64 `Q:size` illegal encodings (such as `inst.size = 0b11#2 ∧ inst.Q = 0b0#1` explicitly trapped in `LNSym` `Advanced_simd_three_same.lean:61-62` and `inst.size ++ inst.Q = 0b110#3` in `Advanced_simd_permute.lean:34-35`).
   - **Model Sufficiency:** `intelxed/xed` (`0bcb6237`) and `sail-arm` (`5416ef6b`) are the gold-standard sources for exact `#UD` / `UNDEFINED` decode boundaries on `x86_64` and `aarch64`.

3. **Tier 3 — SIMD-vs-Scalar Behavioral Equivalence:**
   - Requires exact bit-accurate lane arithmetic (`BitVec 8/16/32/64`) and explicit preconditions guarding the cross-ISA divergence points in Finding 3 (`ctl[i] < 16 || ctl[i] >= 128` for byte shuffles, tap-sum bounds for `PMADDUBSW` vs `VPDPBUSD`, non-`(-32768,-32768)` inputs for `PMADDWD`/`PMULHRSW`, and `MXCSR.FTZ/DAZ/RC` == `FPCR.FZ/RMode` for float audio/filter kernels).
   - **Model Sufficiency:** Extending `LNSym` (`aarch64`) and an `s2n-bignum`/ACL2-derived Lean 4 `BitVec` semantics (`x86_64`) with ~25 media SIMD instructions suffices to discharge 100% of Tier 3 obligations without importing system-mode paging or x87 transcendental machinery.

4. **Tier 4 — Full Bit-Exact Codec Specification Conformance (ITU-T H.264 / H.265 / H.266 / VP9 / AV1):**
   - Video standards mandate bit-exact integer inverse transforms, motion compensation, loop filters, and film-grain synthesis across all architectures (`x86_64`, `aarch64`, `riscv64`, `wasm`). By proving **Tier 3** (`asm_kernel ≈ safe_rust_reference`) against the ISA model and **Tier 4** (`safe_rust_reference ≈ codec_math_spec`) purely at the Rust/Lean `BitVec` level, $N$ architecture backends require $N$ local basic-block equivalence proofs rather than $N$ full codec conformance proofs.

---

### 5. Performance, Microarchitectural Resource Reality, and Proof-Scaling Trade-offs

`Basis: source + documentation + derived`

1. **Real-World Media SIMD Speedups & Microarchitectural Costs (`Basis: documentation + source`):**
   - Across H.264/HEVC/VP9/VVC 8-bit and 10-bit decoders, 256-bit `AVX2` and 128-bit `NEON`/`DOTPROD`/`I8MM` kernels account for `3x`–`12x` kernel-level speedups (and `2x`–`5x` end-to-end decode throughput) over scalar C by executing 16–64 MACs per cycle (`vpdpbusd` on Zen 4/5 and Ice Lake+/Sapphire Rapids; `sdot`/`usdot` on Neoverse V1/V2 and Apple M-series).
   - `andreas-abel/uiCA` (`6ebeeab0`, `Abel & Reineke, ICS 2022`, DOI `10.1145/3524059.3532396`) and `XED-to-XML` (`56fe1b1c`, `ASPLOS 2019`, DOI `10.1145/3297858.3304062`) quantify port pressure that pure functional ISA specs erase: e.g., Intel Core port-5 shuffle bottlenecks on `VPSHUFB`/`VPERMB`, dirty-upper-YMM transition penalties when omitting `VZEROUPPER` on pre-Ice Lake cores (`x86inc.asm:374`), and `AVX-512` 512-bit license downclocking on Skylake-X/Cascade Lake (analyzed for short loops in `x86-avx512-short-loop-regression-and-vector-width-profitability`).
   - Buffer Overread / Padding Footprint: FFmpeg's `AV_INPUT_BUFFER_PADDING_SIZE` (`64` bytes, widened specifically to accommodate 512-bit `ZMM` speculative/unmasked vector loads in bitstream and motion-compensation readers) is an ABI-visible memory-safety precondition at Tier 1 unless `EVEX` `{k1}` or `SVE` predicated tail loads are used (`vp9mc.asm:1192`).

2. **Proof & Kernel Reduction Scaling in Lean 4 (`Basis: source + derived`):**
   - Representing 256-bit or 512-bit vector operations as flat monolithic `BitVec 256`/`BitVec 512` bitblasting goals (or `K-x86`'s 512-branch `#ifMInt` term) degrades SMT and Lean `bv_decide` scaling superlinearly on 16-bit/32-bit multiply-accumulate (`PMADDWD`, `VPDPBUSD`, `SMLAL`).
   - Both `s2n-bignum` (`arm/proofs/neon_helper.ml:14-65` `WORD_BITMANIP_SIMP_LEMMAS`, `common/relational2.ml`) and `LNSym` (`Arm/Insts/DPSFP/Advanced_simd_three_same.lean:33-50` `binary_vector_op_aux_of_lt`) solve this by **lane-wise structural decomposition**: rewriting a 256-bit or 128-bit vector step into $K \in \{4, 8, 16, 32\}$ independent lane equations of width $8, 16,$ or $32$ bits before invoking arithmetic/bitvector decision procedures.

---

### 6. Clean-Rewrite Modularity: Separating Legacy Assembly Accidents from Silicon Constraints

`Basis: source + derived`

Auditing `FFmpeg/FFmpeg` alongside the formal ISA models distinguishes historical C/NASM technical debt that a clean verified Rust media engine should **eliminate outright** from genuine hardware constraints that must be modeled:

- **Eliminate (Historical Accidents in FFmpeg):**
  1. **64-bit `MMX` / `MMXEXT` / `3DNow!` and `EMMS` state aliasing (`libavutil/cpu.h:32-40`, `x86inc.asm:1085`):** `SSE2` has been baseline on every `x86_64` processor since 2003 and every modern `i686` target. Dropping `MMX` eliminates x87 FPU tag-word aliasing (`acl2/acl2` `register-readers-and-writers.lisp:659-763`) from the entire verification TCB.
  2. **Deprecated ARMv6 GPR-SIMD and `VFP_VM` vector mode (`libavutil/cpu.h:70-76`, `libavutil/arm/cpu.h:36`):** Eliminating pre-NEON 32-bit Arm assembly removes `ITSTATE` conditional Thumb-2 block interleaving (`L3` `arm-base.spec:392-393`) from media kernels.
  3. **Preprocessor-entangled multi-width NASM templates (`x86inc.asm` `INIT_XMM` / `INIT_YMM` / `INIT_ZMM` mutating global `%assign mmsize`):** Replacing untyped macro text substitution with typed Rust `core::arch` SIMD intrinsics (compiled through verified MIR/LLVM lowering or validated at the object level via `s2n-bignum`/`LNSym`-style ELF lifters) captures `70%–85%` of codec kernels in safe/verified Rust while isolating inline assembly strictly to genuine codegen gaps (such as `AVX-512ICL` `vpermb + vpdpbusd` multi-tap loops or `I8MM` `usdot`).
- **Retain and Model Explicitly (Fundamental Silicon Constraints):**
  1. **128-bit in-lane boundaries in 256-bit `AVX2` (`VPSHUFB`, `VPACKUSWB`, `VPMADDWD` + `VPERM2I128`)** vs full-crossbar `AVX-512VBMI` `VPERMB`.
  2. **VEX/EVEX upper-register dirtying (`YMM0..15` vs `ZMM16..31`)** and function-boundary `VZEROUPPER` invariants.
  3. **Caller-clobbered sticky `FPSR.QC`** on AArch64 saturating NEON/SVE2 instructions and `MXCSR`/`FPCR` flush-to-zero/rounding-mode agreement.

---

## Boundaries

1. **System-Mode, Privilege, and Weak-Memory Concurrency (`not examined`):** This comparison covers sequential user-mode (`Ring 3` / `EL0`) SIMD instruction semantics. Page-table walks, TLB shootdowns, and relaxed-memory store/load reordering across threads are outside scope (see `assembly-atomic-fence-mappings-and-aarch64-x86-weak-memory-models` and `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement`).
2. **Arm `SME` / `SME2` Outer-Product Tile (`ZA`) Media Kernels (`not examined` in detail here):** While `rems-project/sail-arm` includes `instrs64_sme.sail` and FFmpeg declares `AV_CPU_FLAG_SME`/`AV_CPU_FLAG_SME2` (`libavutil/cpu.h:81, 83`), streaming mode (`PSTATE.SM`) ABI hazards are covered in `rvv-lmul-vtype-hazards-arm-sme-streaming-za-tiles-and-ffload-speculation`; neither `LNSym` nor `s2n-bignum` supports `SME` (`unsupported`).
3. **Intel `AMX` (`TMUL`) and `AVX10` Unified Vector Extensions (`unsupported` across theorem-prover models):** Although `intelxed/xed` encodes `AMX` and `AVX10` forms, none of `kframework/X86-64-semantics`, ACL2 `x86isa`, `s2n-bignum`, or HOL4/`L3` currently formalizes `AMX` tile registers (`TMM0..TMM7`) or `AVX10` converged 256/512-bit EVEX execution (`unsupported`).
4. **Raw Arm MRA XML Redistribution (`known not to apply` for open-source Lean corpora without separate license):** Direct outputs of `mra_tools` / `ASLp` run over proprietary Arm website XML downloads cannot be assumed redistributable under Apache-2.0/MIT; open-source Lean 4 artifacts must either derive from `rems-project/sail-arm`'s `BSD-3-Clause-Clear` snapshot (`5416ef6b`) or author clean-room specifications from published `ARM DDI 0487` pseudocode validated via hardware co-simulation (as `leanprover/LNSym` and `awslabs/s2n-bignum` do).
5. **Microarchitectural Constant-Time Guarantees of Media Instructions (`known not to apply` without uarch model):** Functional ISA equivalence does not establish constant-time execution on variable-latency media instructions or data-dependent subnormal floats unless paired with a leakage model (`s2n-bignum` `common/consttime.ml`; see `side-channel-freedom-foundations-and-leakage-contracts-1996-2026`).

---

## Evidence

### Primary Upstream Source Citations (Verified 2026-11-20)

1. **`FFmpeg/FFmpeg`** (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`):
   - `libavutil/cpu.h:32-88` (`AV_CPU_FLAG_MMX` through `AV_CPU_FLAG_AVXVNNI`, `AV_CPU_FLAG_VFP` through `AV_CPU_FLAG_SME2`); `libavutil/arm/cpu.h:36` (`AV_CPU_FLAG_VFP_VM`); `libavutil/aarch64/asm.S:52, 60, 88, 96` (`dotprod`, `i8mm`, `sve`, `sve2`).
   - `libavutil/x86/x86inc.asm:374, 612-618, 857, 944-967, 1073, 1085-1139` (`vzeroupper_required`, `Win64` `xmm_regs_used`, `ZMM16..31` preference, `INIT_MMX`/`INIT_XMM`/`INIT_YMM`/`INIT_ZMM`).
   - `libavcodec/x86/h264_idct.asm:231, 248, 394, 583`; `libavcodec/x86/vp9mc.asm:238-271, 848-861, 1181-1192`; `libavcodec/x86/hevc/mc.asm:542-551, 685-702, 1286-1288`; `libavcodec/x86/vvc/mc.asm:134, 144, 174`; `libavcodec/x86/vvc/sad.asm:91`.
   - `libavcodec/aarch64/h264idct_neon.S:68` (`sqxtun`); `libavcodec/aarch64/vp9mc_neon.S:203-204` (`sqadd`); `libavcodec/aarch64/hevcdsp_idct_neon.S:51-52, 246-248` (`sqadd`, `smlal`); `libavcodec/aarch64/vvc/alf.S:61, 145` (`smlal`, `sqxtun`).
2. **`kframework/X86-64-semantics`** (`592380aea04820ea11cfa5475b343f0257f2474e`):
   - `LICENSE.md:1-28` (UIUC/NCSA); `README.md:3-25` (`3,155` variants / `774` mnemonics, K `MInt` compatibility constraint); `semantics/registerInstructions/pshufb_xmm_xmm.k:1-15`; `semantics/registerInstructions/vpshufb_ymm_ymm_ymm.k:1-15` (512-branch `#ifMInt` expansion); `semantics/registerInstructions/vzeroupper.k:11-43`.
3. **`acl2/acl2`** (`08bec1884997560686932229dbfe458c1bba34bf`) & **`rems-project/sail-x86-from-acl2`** (`0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf`):
   - `books/projects/x86isa/machine/register-readers-and-writers.lisp:3-36, 113-271, 659-795` (BSD-3-Clause, 32-bit mode, `MMX`/`EMMS` x87 aliasing, `XMM`/`YMM`/`ZMM` 512-bit accessors); `evex-opcodes-dispatch.lisp:44-80`; `instructions/{padd,psub,pmadd,pack,emms,move-vex}.lisp`; `instructions/fp/{mxcsr,shuffle-and-unpack,top}.lisp`.
   - `sail-x86-from-acl2`: `LICENCE:1-37`, `README.md:7-36`, `model/registers.sail:121-127`, `model/evex_opcodes_dispatch.sail`, `model/vex_opcodes_dispatch.sail`.
4. **`awslabs/s2n-bignum`** (`280a220986a0bc6249248187717a771153d073db`), **`cslib-community/bignum`** (`1b3952cba6438a6a03da02ff207deb6c93e7d4eb`), & **`AeneasVerif/kraken`** (`3acb3ee4a7e6711d198cb1a124bb892de9dac5d4`):
   - `x86/proofs/base.ml:1-68` (`Apache-2.0 OR ISC OR MIT-0`, `READ_YMM_SSE_EQUIV`); `x86/proofs/instruction.ml:11-190, 275-285, 352-462` (`ZMM0..31`, `EVEX`, `VPSHUFB`, `VPMADDWD`, `VPMADDUBSW`, `VPMULHRSW`, `VPACKUSWB`, `VZEROUPPER`); `x86/proofs/x86.ml:68, 200-206, 1014, 1468, 1823-2291, 2606-2617` (`evex_mask`).
   - `arm/proofs/instruction.ml:24-31, 1751, 1946-2047, 2199-2211, 2625, 2658-2893` (`armstate` omitting `FPCR`/`FPSR`, `SQDMULH`, `SMLAL`, `PMULL`, `ADDV`, `UZP1`/`ZIP1`/`TRN1`, `TBL`/`TBL2`); `arm/proofs/neon_helper.ml:14-65`; `SOUNDNESS.md:15-49`.
5. **`coruus/L3`** (`d6558e679a25ffaaf16a47a3189f8f8111e45e0c`) & **`HOL-Theorem-Prover/HOL`** (`0c30bdb71aafd4e6a354f5b0b43fffbff6fa8d47`):
   - `L3`: `isa-models/COPYRIGHT:1-34`, `isa-models/x86-64/x64.spec:1-45`, `isa-models/arm-v7/{arm-base.spec:31-58, arm-vfp.spec:20-53, arm-iset.spec:847-920}`, `isa-models/arm-v8/v8-iset.spec:1-45`.
   - `HOL`: `examples/l3-machine-code/x64/model/x64Script.sml:13-90, 2330-2402` (`MXCSR` + FP SSE only); `examples/machine-code/instruction-set-models/x86/x86_astScript.sml:15-60` (32-bit scalar integer only).
6. **`intelxed/xed`** (`0bcb6237345c5066726dcc08b3d87928df3b5b26`), **`andreas-abel/XED-to-XML`** (`56fe1b1c228c2407fbde6b2de24b7b39d1e8da9a`), & **`andreas-abel/uiCA`** (`6ebeeab0f8705cae4b17a9362f9c65ef91f5cc44`):
   - `xed`: `datafiles/xed-isa.txt:11350, 13728`; `datafiles/avx-vnni/avx-vnni-isa.xed.txt:28-43` (`VPDPBUSD`). `XED-to-XML`: `LICENSE:1-15` (Apache-2.0), `README.md:10-35`. `uiCA`: `LICENSE:1-15` (AGPL-3.0), `README.md:1-14`.
7. **`UQ-PAC/aslp`** (`92e4fd949402056e16e3747e66922060be57ecc8`), **`rems-project/mra_tools`** (`941317606f36580f668498889abc6301ed8222d8`), **`rems-project/sail-arm`** (`5416ef6b43e9527c38dc71fb752259c1d01a47e1`), & **`leanprover/LNSym`** (`49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`):
   - `aslp`: `libASL/symbolic.ml:1-45`, `libASL/eval.ml:1-19` (BSD-3-Clause), `bin/offline_sem.ml:1-29`.
   - `sail-arm`: `arm-v9.4-a/LICENSE:1-37` (BSD-3-Clause-Clear), `arm-v9.4-a/README.md:6-45`, `arm-v9.4-a/Makefile:25-45` (`instrs32.sail`, `instrs64.sail`, `instrs64_sve.sail`, `instrs64_sme.sail`).
   - `LNSym`: `Arm/State.lean:1-35` (Apache-2.0), `Arm/Decode/DPSFP.lean:14-70`, `Arm/Insts/DPSFP/Advanced_simd_table_lookup.lean:18-69`, `Advanced_simd_three_same.lean:20-70`, `Advanced_simd_three_different.lean:22-70`, `Advanced_simd_permute.lean:18-58`, `Advanced_simd_two_reg_misc.lean:1-70`.

### Native `x86_64` Hardware Execution Probe (`Basis: execution`)

Executed on Linux `x86_64` (`avx2`, `ssse3`, `fma`, `bmi1`, `bmi2`) compiled with `gcc (Debian 15.2.0-14) 15.2.0 -O2 -mavx2`:

```c
#include <immintrin.h>
#include <stdint.h>
#include <stdio.h>

int main(void) {
    uint32_t init_ymm[8] = {1, 2, 3, 4, 0xCAFEBABEu, 0xDEADBEEFu, 0x12345678u, 0x87654321u};
    uint32_t add_xmm[8]  = {10, 20, 30, 40, 0, 0, 0, 0}, out_sse[8] = {0}, out_vex[8] = {0};
    __asm__ volatile (
        "vmovdqu (%2), %%ymm0\n\tvmovdqu (%3), %%xmm1\n\tpaddd %%xmm1, %%xmm0\n\tvmovdqu %%ymm0, (%0)\n\t"
        "vmovdqu (%2), %%ymm0\n\tvpaddd %%xmm1, %%xmm0, %%xmm0\n\tvmovdqu %%ymm0, (%1)\n\tvzeroupper\n\t"
        : : "r"(out_sse), "r"(out_vex), "r"(init_ymm), "r"(add_xmm) : "ymm0", "ymm1", "memory");
    printf("SSE_LEGACY_PADDD_UPPER128: %08x %08x %08x %08x\n", out_sse[4], out_sse[5], out_sse[6], out_sse[7]);
    printf("VEX_VPADDD_UPPER128:       %08x %08x %08x %08x\n", out_vex[4], out_vex[5], out_vex[6], out_vex[7]);

    uint8_t tbl[32], ctl[32], shuf[32];
    for (int i = 0; i < 32; i++) { tbl[i] = (uint8_t)(0xA0 + i); ctl[i] = 0x80; }
    ctl[0] = 0x03; ctl[1] = 0x13; ctl[2] = 0x83; ctl[16] = 0x03; ctl[17] = 0x13;
    _mm256_storeu_si256((__m256i *)shuf,
        _mm256_shuffle_epi8(_mm256_loadu_si256((const __m256i *)tbl),
                            _mm256_loadu_si256((const __m256i *)ctl)));
    printf("VPSHUFB: [0]=0x%02x [1]=0x%02x [2]=0x%02x [16]=0x%02x [17]=0x%02x\n",
           shuf[0], shuf[1], shuf[2], shuf[16], shuf[17]);

    __m128i mwrap = _mm_madd_epi16(_mm_set1_epi16(-32768), _mm_set1_epi16(-32768));
    __m128i ubsw  = _mm_maddubs_epi16(_mm_set1_epi8((char)0xFF), _mm_set1_epi8(127));
    __m128i pair  = _mm_madd_epi16(ubsw, _mm_set1_epi16(1));
    __m128i q15   = _mm_mulhrs_epi16(_mm_set1_epi16(-32768), _mm_set1_epi16(-32768));
    printf("PMADDWD_WRAP=%d PMADDUBSW_4WAY=%d VNNI_EXACT=%d PMULHRSW_MIN=%d\n",
           _mm_cvtsi128_si32(mwrap), _mm_cvtsi128_si32(pair), 4*255*127,
           (int16_t)_mm_extract_epi16(q15, 0));
    return 0;
}
```

Recorded output (2026-11-20):
```text
SSE_LEGACY_PADDD_UPPER128: cafebabe deadbeef 12345678 87654321
VEX_VPADDD_UPPER128:       00000000 00000000 00000000 00000000
VPSHUFB: [0]=0xa3 [1]=0xa3 [2]=0x00 [16]=0xb3 [17]=0xb3
PMADDWD_WRAP=-2147483648 PMADDUBSW_4WAY=65534 VNNI_EXACT=129540 PMULHRSW_MIN=-32768
```

---

## Revalidation

To cheaply revalidate whether upstream ISA models have closed the media SIMD gaps identified in this report without repeating full repository audits:

1. **Check `s2n-bignum` x86 & Arm media instruction additions (`<5s`):**
   Fetch `x86/proofs/instruction.ml` and `arm/proofs/instruction.ml` at the new `HEAD` of `awslabs/s2n-bignum` and grep for `VPADDSW|VPSUBUSB|VPDPBUSD|VPERMB|VPHADDW` (`x86`) and `SQADD|SQXTUN|SDOT|UDOT|FPSR` (`arm`).
2. **Check `leanprover/LNSym` NEON/SVE & `FPSR.QC` additions (`<5s`):**
   Inspect `Arm/State.lean` for `fpsr` / `fpcr` fields and `Arm/Insts/DPSFP/` for `sqadd`, `sqxtun`, `smlal`, `sdot`, or `sve` modules.
3. **Check ACL2 `x86isa` SSSE3/AVX2/VNNI coverage (`<5s`):**
   List `books/projects/x86isa/machine/instructions/` in `acl2/acl2` for `pshufb`, `pmaddubsw`, `vpdpbusd`, `vpermb`, or `vzeroupper`.
4. **Check `rems-project/sail-arm` Lean backend totality (`<10s`):**
   Inspect `arm-v9.4-a/Makefile` (`gen_lean` flags for `-lean-noncomputable`) and `ArmExtras.lean` for remaining `sorry` placeholders.
5. **Re-run the native `x86_64` C probe above (`<2s`):**
   Compile with `gcc -O2 -mavx2` on any `x86_64` host to re-verify upper-lane zeroing, `vpshufb` `0x10..0x7F` wrap/lane isolation, `pmaddwd` `0x80000000` wrap, and `pmaddubsw` vs `vpdpbusd` saturation divergence.
