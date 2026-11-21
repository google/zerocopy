# Mechanical s2n-bignum + Arm ASL Pass-2 AArch64 reference transpilation, vendor/lean-miri NEON/Crypto gap closure, and 3-way core::arch::aarch64 triangulation in Lean 4

## Summary

Closing the Pass-2 reference-correspondence gap for word-decoded `aarch64`
machine code and `core::arch::aarch64` NEON, Cryptographic, and CRC32
intrinsics in Lean `v4.34.1` yields four empirically and mechanically verified
results:

1. **Closing `9` missing `core::arch::aarch64` NEON + Crypto intrinsics (`51`
   net new `llvm.aarch64.*` link names) in a pure, tactic-free (`0` `by`, `0`
   `isPartial`) Lean `v4.34.1` extension (`support/IntrinsicAarch64Ext.lean`)
   lifts real-world 12-crate AArch64 SIMD call-site coverage from `88.35%`
   (`584 / 661`) to `100.00%` (`661 / 661`).** Auditing
   `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`
   (`Miri.Interpreter.{IntrinsicSimd,IntrinsicCrypto,IntrinsicArchitecture}`)
   against `rustc 1.99.1`'s `stdarch` (`9,841` public functions referencing
   `2,655` distinct `llvm.aarch64.*` link names, `940` non-SVE) and `12`
   production pure-Rust SIMD crates (`zlib-rs`, `memchr`, `simdutf8`,
   `crc32fast`, `simd-adler32`, `blake3`, `aho-corasick`, `bytecount`,
   `hashbrown`, `sha2`, `chacha20`, `aes`) shows `494` pure portable `simd_*`
   call sites and `661` `core::arch::aarch64` call sites across `101` distinct
   intrinsics. Base `IntrinsicArchitecture.aarch64` covers `584 / 661`
   (`88.35%`) and fails closed (`.unsupported`) on **`77 / 661` (`11.65%`)**
   concentrated in `vaddlvq_u8` (`5` sites in `bytecount`), Armv8 AES
   `vaeseq_u8`/`vaesmcq_u8`/`vaesdq_u8`/`vaesimcq_u8` (`24` sites in `aes`), and
   Armv8.2 SHA-512 `vsha512{h,h2,su0,su1}q_u64` (`48` sites in `sha2`).
   `support/IntrinsicAarch64Ext.lean` (`691` LOC, `35,099` B) closes all `9`
   intrinsics plus `ushl`/`sshl`, `umaxv`/`uminv`/`smaxv`/`sminv`/`saddlv`, and
   `pmull` width families (`68` total supported non-SVE `stdarch` link names),
   compiles in **`2.82 s`**, replays from scratch at
   `(trustLevel := 0, level := .private)` in **`165 ms`** (`204` constants,
   axioms `["Quot.sound", "propext"]`), and agrees bit-for-bit with live
   `rustc --target aarch64-unknown-linux-gnu` + `qemu-aarch64 11.1.2 -cpu max`
   execution on NIST `FIPS-197` AES-128 and `FIPS-180-4` SHA-512 `"abc"`
   vectors.
2. **Combining `awslabs/s2n-bignum` with an Arm DDI 0487 ASL decode-legality
   and opcode overlay produces a fast, pure `Init.*` Pass-2 reference model
   (`VendorArm64Ref`), whereas raw `s2n-bignum` delegates constrained-unpredictable
   loads/stores to total state havoc (`ASSIGNS entirety`) and omits `11 / 34`
   (`32.35%`) of `rustc -O3` `.o` functions.** Parsing pinned
   `awslabs/s2n-bignum@d4518712d040485efe621caba1c723a07fbc549e`
   (`arm/proofs/{instruction,decode,arm,neon_helper,sha256,sha512}.ml` +
   `common/aes.ml`: `228` `decode.ml` bitmatch arms, `229` `arm_*` semantic
   definitions) reveals five architectural seams that prevent direct unguarded
   reuse for general Rust/NEON object verification: (i) `21` memory definitions
   in `instruction.ml` (`arm_LDP` at `L3069`, `arm_LDR` at `L2945`, etc.) guard
   overlapping `Rt == Rt2` (including `LDP xzr, xzr, [x4]` `0xa9407c9f` at
   `L3066`) and writeback `Rn == Rt` with `ASSIGNS entirety` (`\s s'. T`),
   allowing an arbitrary post-state PC and memory rather than failing closed;
   (ii) `arm.ml:140` pre-increments `PC := PC + 4` before `arm_execute` and
   compensates via `word_sub (read PC s) (word 4)` across `11` PC-relative
   definitions (`ADRP` at `instruction.ml:753`, `4,096`-byte page-mask hazard at
   `PC & 0xfff == 0xffc`); (iii) `5` NEON decode arms reject `64`-bit `D`-width
   forms (`~q then NONE`, including `rev64 v0.8b` at `decode.ml:1530`); (iv)
   `UMOV` rejects `.b` and `.h` lanes (`decode.ml:1494`); and (v) `decode.ml`
   omits `CMEQ`, `CMLT #0`, `UQADD`, `UQSUB`, `SSHL`, `BSL`, `ADDP`, `UMINV`,
   `CRC32*`, `UDIV`/`SDIV`, `LDAR`/`STLR`/`LDAXR`/`STLXR`/`CLREX`, `BTI`, and
   `UDF`. `support/transpile_s2n_arm_to_lean.py` emits 5 sharded `prelude` +
   `Init.*` modules (`support/VendorArm64Ref/*.lean`, `82` slice entries) that
   compile in **`8.80 s` sequential wall time** (`0.36 s`–`3.78 s` per module,
   `0` `isPartial` constants), replay at `(trustLevel := 0, level := .private)`
   in **`489 ms`** (`1,678` constants, axioms `["Quot.sound", "propext"]`), and
   match **`224 / 224` (`100.0%`)** of live `qemu-aarch64 11.1.2` (`-cpu max`
   and `-cpu cortex-a53`) execution and fault vectors (`QemuCheck224.all_224_qemu_vectors_match`).
3. **Pass-2 correspondence (`VendorArm64Ref.Step ⊆ WordArm64.Step`) exposes
   both `s2n-bignum` `ASSIGNS entirety` frame unsoundness and two microarchitectural
   narrow-refinement traps (`FEAT_LSE2` alignment and `STLXR` exclusive-monitor
   spurious failure).** Live `qemu-aarch64 11.1.2` execution across `224`
   vectors demonstrates **`6` `SIGBUS` (`sig = 7`) divergences** between
   `-cpu max` (`FEAT_LSE2`, where intra-16-byte unaligned `LDAR`/`STLR`/`LDAXR`
   succeed) and `-cpu cortex-a53` (`Armv8.0-A`, where all `6` trap with
   `SIGBUS`), while cross-16-byte `[x4 + 12]` `LDAR`/`STLR` trap on both CPUs;
   meanwhile `llvm-objdump 21.1.8 -d` emits zero warnings on **`10 / 10`
   (`100.0%`)** of constrained-unpredictable encodings (`llvm-mc 21.1.8
   --disassemble` is silent on `4 / 10`). In
   `support/WordArm64Pass2Correspondence.lean` (`5.22 s` compile, **`991 ms`**
   private kernel replay across `357` constants, `0` `sorry`), we prove (a)
   `s2n_assigns_entirety_unsound_frame_violation` (raw `ASSIGNS entirety`
   destroys unrelated callee-saved `X19` and memory on `LDP x0, x0, [x4]`), (b)
   `misaligned_ldar_lse2_narrow_refinement_counterexample` and
   `stlxr_spurious_fail_narrow_refinement_counterexample` (falsifying hardware-overfit
   `WordArm64.StepNarrow` on `LDAR` alignment and deterministic QEMU `STLXR`
   success), and (c) universal single-step and `N`-step Pass-2 simulation
   `vendorArm64Ref_step_sub_wordArm64_step` and
   `vendorArm64Ref_stepsN_sub_wordArm64_stepsN` with explicit `exclSpuriousFail`
   demonic nondeterminism (`qemu_stlxr_deterministic_in_vendorArm64Ref`).
4. **All `25` curated `core::arch::aarch64` NEON, Crypto, and CRC32 primitives
   (`+ 9` signed/width/boundary/crypto companions = `34` `.o` functions) emit
   word-identical AArch64 machine code across `rustc 1.99.1`, `1.101.0-nightly`,
   and `1.95.0-nightly` (`LLVM 21.1.8` & `23.1.1`) and satisfy universal 3-way
   Pass-2 triangulation—alongside `4` constructive MIR-vs-NEON UB and Arm-vs-x86
   AES asymmetry theorems.** In `support/NeonTriangulationCore.lean` (`7.17 s`)
   and `support/NeonTriangulation24.lean` (`8.77 s`), we prove:
   - `unguarded_miri_simd_shl_ub_vs_neon_ushl_bidir`: raw MIR `simd_shl` raises
     UB on negative (`-2 = 0xfe`) and oversize (`8`) shift bytes where NEON
     `ushl v0.16b` (`0x6e214400`) shifts right (`0x21`) and saturates to `0x00`;
   - `unguarded_miri_simd_shr_32_ub_vs_rustc_cmlt_zero`: raw MIR
     `simd_shr(a, splat(32))` raises UB (`32 >= 32`), whereas `stdarch` clamps
     `vshrq_n_s32::<32>` to `31` and `rustc -O3` lowers it to
     `cmlt v0.4s, v0.4s, #0` (`0x4ea0a800`), proven equal across all `2^128`
     vectors;
   - `arm_aese_aesmc_ne_x86_vaesenc_single_key` and
     `arm_aese_aesmc_eor_eq_x86_vaesenc_universal`: Arm `AESE` XORs the round
     key *before* `ShiftRows`/`SubBytes` whereas x86 `VAESENC` XORs *after*
     `MixColumns`, falsifying 1-key equivalence on NIST FIPS-197 inputs while
     satisfying the universal 2-key cipher-round identity
     `∀ state rk0 rk1, aesmc(aese(state, rk0)) ^^^ rk1 = x86Vaesenc(state ^^^ rk0, rk1)`
     over all `2^384` triples;
   - **`34` universally quantified (`∀ a b c sp lr mem`) 3-way triangulation
     theorems** linking `LeanMiri`/`IntrinsicAarch64Ext`, `StdarchArmSpec`, and
     the `rustc -O3` `.o` words stepped in `VendorArm64Ref` and lifted into
     `WordArm64.StepsN`—covering operand commutation, relational reversal
     (`vcltq_s8` $\to$ `cmgt`), boundary shift folding (`vshrq_n_u32::<32>` $\to$
     `movi #0`, `vshrq_n_s32::<32>` $\to$ `cmlt #0`), 3-step `uaddlv`/`umaxv`/`uminv`
     + `fmov w0, s0` scalar writeback, 64-bit `rev64 v0.8b` upper-`V0[127:64]`
     zeroing, destructive `bsl`, 6-step AAPCS64 `X1:X0` `vmull_p64`, `aese`/`aesmc`,
     `sha512h`/`sha512su0`, and `crc32cx` `W0` upper-32 zeroing.

## Applicability

These findings govern the relationship among the eleven concrete subjects
recorded in `REPORT.json`:

- **Target verification architecture (`joshlf/anneal` at
  `c131b320eeeb26ef692e5afd5ec8db49ee518613` and `leanprover/lean4` `v4.34.1` at
  `5045d0056413266e57c625dcd7c365b10e377c52`):** All `9` staged Lean modules and
  the `224`-vector QEMU check harness compile with synchronous kernel checking
  (`-DElab.async=false -Ddebug.skipKernelTC=false`) strictly over `prelude` +
  `Init.{Core,Data.BitVec.Basic,Data.BitVec.Lemmas,Data.List.Basic,Data.Nat.Basic}`,
  and replay from `baseInit` via
  `importModules ... (trustLevel := 0) (plugins := #[]) (loadExts := false)
  (level := .private)` followed by `baseInit.toKernelEnv.replay`, matching
  `trusted/audit/TrustedBoundary.lean`.
- **Upstream AArch64 reference specifications (`awslabs/s2n-bignum` at
  `d4518712d040485efe621caba1c723a07fbc549e`, Arm Architecture Reference Manual
  `DDI 0487` Edition `L.a`, and NIST `FIPS PUB 197-upd1` / `FIPS PUB 180-4`):**
  `VendorArm64Ref` models little-endian EL0 (`A64`) execution with separated
  `XZR`/`WZR` vs `SP`/`WSP` register-31 accessors, 16-byte `SP` alignment
  enforcement, 32-bit `W`-write upper-32 zeroing, 64-bit `D`-write upper-64
  zeroing, `FEAT_AES`/`FEAT_PMULL`/`FEAT_SHA256`/`FEAT_SHA512`/`FEAT_CRC32`, and
  explicit `FEAT_LSE2` alignment and `ExclusiveMonitor` parameters.
- **Upstream Rust/MIR SIMD reference and compilers (`proofs-rs/lean-miri` at
  `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`; `rustc 1.99.1`
  `58cf8f9c35b355199727627d07ae34a4e2846d67` with `LLVM 23.1.1`, `rustc
  1.101.0-nightly` `5c543b0b8c73c7b72bc8284ced4fb22ead15734d` with `LLVM
  23.1.1`, and `rustc 1.95.0-nightly`
  `f134bbc78dac04a17324341a8d4a15a6930d81a7` with `LLVM 21.1.8` targeting
  `aarch64-unknown-linux-gnu`):** Object-code triangulation applies to AAPCS64
  `extern "C"` functions compiled at `-C opt-level=3` under explicit
  `#[target_feature(enable = "neon")]`, `"aes"`, `"sha3"` (which enables
  `FEAT_SHA512` in Rust/LLVM), and `"crc"`. All three toolchains emit
  word-identical ELF64 `.text` instruction sequences across all `34` examined
  functions.
- **Execution and disassembler baselines (`qemu-aarch64 11.1.2`, Debian
  `1:11.1.2+ds-2` under `-cpu max` and `-cpu cortex-a53`; `llvm-mc 21.1.8` and
  `llvm-objdump 21.1.8` on `Linux 7.1.6-1rodete1-amd64`):** Live user-mode EL0
  execution captures architectural `X0..X4`, `SP`, `NZCV`, `V0`, memory words,
  and Linux `SA_SIGINFO` `SIGILL` (`sig = 4`, `UDF` and unallocated encodings)
  and `SIGBUS` (`sig = 7`, `SP` misalignment and `LDAR`/`STLR`/`LDAXR`
  alignment faults).

## Findings

### 1. Audit of `vendor/lean-miri@c92d1d97` `IntrinsicArchitecture.aarch64` and `88.35%` $\to$ `100.00%` production crate gap closure

Basis: normative + source + execution + derived

Scanning `rustc 1.99.1`'s `library/stdarch/crates/core_arch/src/{aarch64,arm_shared}`
tree (`support/probe_lean_miri_aarch64_audit.py`,
`support/probe_lean_miri_aarch64_audit_results.json`) identifies `9,841` public
intrinsic wrappers referencing `2,655` distinct `llvm.aarch64.*` link names
(`940` non-SVE `neon.*` / `crypto.*` / `crc32*` / system names plus `1,715`
`sve.*`/`svcount` names). In `joshlf/anneal@c131b320`'s vendored
`proofs-rs/lean-miri@c92d1d97`, `Miri/Interpreter/IntrinsicArchitecture.lean`
(`308` LOC, `17,724` B, `0` `by` blocks, `0` `partial`/`unsafe`) implements `35`
non-SVE `llvm.aarch64.*` link names (`neon.{addp,rbit,pmull.v8i16,pmull.v4i32,pmull.v2i64,smax,smin,umax,umin,sqadd,sqsub,uqadd,uqsub,sqdmulh,tbl1,tbl2,vpaddl,fmax,fmin}`
plus `crypto.sha256{h,h2,su0,su1}`).

Auditing all `core::arch::aarch64` and portable `simd_*` call sites across `12`
widely deployed pure-Rust SIMD crates (`494` pure portable `simd_*` sites
handled by `IntrinsicSimd.lean` plus **`661` `core::arch::aarch64` call sites**
spanning `101` distinct intrinsics) pinpoints the exact real-world gap:

| Production Crate | `core::arch::aarch64` Sites | Distinct Intrinsics | Base `lean-miri` Covered | Uncovered Before | After `IntrinsicAarch64Ext` | Missing Intrinsics Closed |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| `zlib-rs-0.6.8` | `129` | `32` | `129` (`100.0%`) | `0` | `129` (`100.0%`) | — (uses `vmull_p64` $\to$ `pmull.v2i64` / `pmull64`, `crc32*`, `vqsubq_u16`, `vqtbl1q_u8`) |
| `sha2-0.11.1` | `203` | `20` | `155` (`76.4%`) | **`48`** | `203` (`100.0%`) | `vsha512hq_u64` (`16`), `vsha512h2q_u64` (`16`), `vsha512su0q_u64` (`8`), `vsha512su1q_u64` (`8`) |
| `bytecount-0.6.9` | `62` | `7` | `57` (`91.9%`) | **`5`** | `62` (`100.0%`) | `vaddlvq_u8` (`5` $\to$ `llvm.aarch64.neon.uaddlv.i32.v16i8`) |
| `simd-adler32-0.3.10` | `55` | `20` | `55` (`100.0%`) | `0` | `55` (`100.0%`) | — |
| `aes-0.9.4` | `44` | `12` | `20` (`45.5%`) | **`24`** | `44` (`100.0%`) | `vaeseq_u8` (`7`), `vaesdq_u8` (`6`), `vaesimcq_u8` (`6`), `vaesmcq_u8` (`5`) |
| `chacha20-0.10.2` | `40` | `20` | `40` (`100.0%`) | `0` | `40` (`100.0%`) | — |
| `crc32fast-1.5.5` | `38` | `15` | `38` (`100.0%`) | `0` | `38` (`100.0%`) | — (`vmull_p64` + `veorq_u8` folding) |
| `aho-corasick-1.1.5` | `37` | `13` | `37` (`100.0%`) | `0` | `37` (`100.0%`) | — |
| `hashbrown-0.17.1` | `19` | `10` | `19` (`100.0%`) | `0` | `19` (`100.0%`) | — |
| `memchr-2.8.3` | `17` | `13` | `17` (`100.0%`) | `0` | `17` (`100.0%`) | — |
| `simdutf8-0.1.5` | `17` | `13` | `17` (`100.0%`) | `0` | `17` (`100.0%`) | — |
| `blake3-1.8.7` | `0` | `0` | `0` (`100.0%`) | `0` | `0` (`100.0%`) | *(uses portable `simd_*` on AArch64)* |
| **Total (`12` crates)** | **`661`** | **`101` unique** | **`584` (`88.35%`)** | **`77` (`11.65%`)** | **`661` (`100.00%`)** | **All `9` missing intrinsics (`77 / 77` sites) closed** |

`support/IntrinsicAarch64Ext.lean` implements a standalone, pure (`prelude` +
`Init.*`), tactic-free (`0` `by` blocks, `0` `isPartial`, `0` `unsafe`)
extension evaluator `evalAarch64Ext` covering **`52` `llvm.aarch64.*` link names**
(`51` net new names beyond `IntrinsicArchitecture.aarch64`):
- **Armv8 AES (`crypto.{aese,aesmc,aesd,aesimc}`):** 2-level `16 × 16` `match`
  forward and inverse S-boxes, little-endian `ShiftRows`/`InvShiftRows`, and
  $\text{GF}(2^8)$ `MixColumns`/`InvMixColumns` modulo $x^8 + x^4 + x^3 + x + 1$,
  with kernel `rfl` proofs of full 10-round NIST `FIPS-197` Appendix B AES-128
  encryption (`0x320b6a19978511dcfb09dc021d842539` in LE `BitVec 128`), inverse
  decryption recovery, and `aesimc(aesmc(x)) = x`.
- **Armv8.2 SHA-512 (`crypto.sha512{h,h2,su0,su1}`):** Exact port of
  `s2n-bignum`'s `arm/proofs/sha512.ml` (`L41-218`) 64-bit lane schedule and
  compression steps, verified by kernel `rfl` against the complete 80-round NIST
  `FIPS-180-4` SHA-512 digest of `"abc"` (`0xddaf35a193617abacc417349ae204131...`)
  and cross-checked on `qemu-aarch64 11.1.2 -cpu max`.
- **Across-vector reductions, signed variable shifts, and polynomial multiply
  (`neon.{uaddlv,saddlv,umaxv,uminv,smaxv,sminv,ushl,sshl,pmull,pmull64}`):**
  `Nat.rec`-total implementations across all 64-bit and 128-bit lane widths
  (`v8i8`, `v16i8`, `v4i16`, `v8i16`, `v2i32`, `v4i32`, `v2i64`, `i64 × i64 ->
  i128` `pmull64`, which `stdarch`'s `vmull_p64` links via
  `llvm.aarch64.neon.pmull64`).

### 2. Mechanical `s2n-bignum` + Arm ASL transpilation to `VendorArm64Ref` and raw `s2n-bignum` gaps

Basis: normative + source + execution + derived

`support/transpile_s2n_arm_to_lean.py` (`support/s2n_arm_transpiler_audit.json`)
verifies exact Git blob SHA-1 digests across all `7` pinned `awslabs/s2n-bignum@d4518712`
Arm HOL Light files (`arm/proofs/instruction.ml` `ef9be01f`, `decode.ml`
`d71476c1`, `arm.ml` `8084bff1`, `neon_helper.ml` `afa2e916`, `sha256.ml`
`a4a56982`, `sha512.ml` `918a24d3`, `simulator_iclasses.ml` `281b03c2`, plus
`common/aes.ml` `520c48a5`), cataloging `228` `decode.ml` bitmatch arms (`221`
distinct targets) and `229` `arm_*` semantic definitions. Source inspection and
differential testing expose **five structural hazards in raw `s2n-bignum` AArch64
decoding and semantics**:

1. **Constrained-unpredictable load/store overlap (`Rt == Rt2`, `Rn == Rt`
   writeback) decoded as `SOME` and delegated to `ASSIGNS entirety` (`21`
   definitions in `instruction.ml:2945-3502`):** In `decode.ml`, `LDP x0, x0,
   [x4]` (`0xa9400080`), `LDP xzr, xzr, [x4]` (`0xa9407c9f`), and pre/post-indexed
   `LDR x0, [x0], #8` (`0xf8408400`) all return `SOME instr`. Inside
   `instruction.ml` (`arm_LDP` at `L3066-3069`: `~(dest1 = dest2) ... | ASSIGNS
   entirety`), overlapping operands fall into the fallback relational disjunct
   `ASSIGNS entirety` (`\s s'. T`), which permits arbitrary mutation of **every
   register, memory byte, and `PC`**. An operational verifier importing
   `decode.ml` without filtering constrained-unpredictable overlaps either omits
   the fallback (unsoundly picking one register write order) or admits total
   frame destruction; `VendorArm64Ref/Decode.lean` rejects all such encodings
   fail-closed at decode time with `.error .constrainedUnpredictable` (including
   `LDP xzr, xzr` via raw 5-bit `rt == rt2` check before `XZR` zeroing).
2. **Pre-incremented `PC := PC + 4` execution convention (`arm.ml:140` vs `11`
   definitions in `instruction.ml:748-1395`):** `arm.ml` increments `PC` by `4`
   *before* invoking `arm_execute instr`, requiring `arm_ADR` (`L748`),
   `arm_ADRP` (`L753`), `arm_B` (`L802`), `arm_BL` (`L877`), `arm_BL_ABSOLUTE`
   (`L886`), `arm_Bcond` (`L898`), `arm_CBNZ`/`arm_CBZ` (`L907-916`),
   `arm_TBNZ`/`arm_TBZ` (`L930-939`), and `arm_RET` (`L1395`) to subtract `4`
   internally. Any naive port of `arm_ADRP` into a standard fetch-at-`PC`
   stepper shifts the 4 KiB page base by `+4,096` bytes whenever `PC & 0xfff ==
   0xffc` (verified on live `qemu-aarch64` vector `c73_adrp_page_end` at
   `0x10ffc`). `VendorArm64Ref` evaluates all instructions uniformly against
   fetch `s.pc` (`pageBase = s.pc &&& ~~~0xfff#64`) and writes `nextPc = s.pc +
   4#64` on non-branch completion.
3. **Partial 64-bit NEON `~q then NONE` rejections (`5` sites in `decode.ml:1036,
   1044, 1321, 1530, 1537`) and `.b`/`.h` `UMOV` rejection (`decode.ml:1494`):**
   Raw `decode.ml` explicitly returns `NONE` with `// datasize = 64 is
   unsupported yet` on 64-bit `D`-register NEON operations such as `rev64 v0.8b,
   v0.8b` (`0x0e200800`, emitted by `core::arch::aarch64::vrev64_u8`) and on
   8-bit/16-bit `UMOV w0, v0.b[k]` / `v0.h[k]`. `VendorArm64Ref` decodes both
   `.d64` and `.q128` forms and enforces architectural upper-64 zeroing
   (`V[d][127:64] = 0`) in `writeVec .d64`.
4. **Missing scalar/atomic/CRC32/NEON opcodes (`11 / 34 = 32.35%` of `rustc -O3`
   `.o` functions):** Raw `decode.ml` omits `CMEQ`, `CMLT #0`, `UQADD`, `UQSUB`,
   `SSHL`, `BSL`, `ADDP`, `UMINV`, `UADDLP`, `CRC32B/H/W/X` and `CRC32CB/CH/CW/CX`,
   `UDIV`/`SDIV` (which return `0` without trapping on division by zero in A64,
   verified on `qemu-aarch64` vectors `c59_udiv_by_zero` and `c61_sdiv_by_zero`),
   `LDAR`/`STLR`/`LDAXR`/`STLXR`/`CLREX`, `BTI`, and `UDF`.
5. **Separated `XZR`/`WZR` vs `SP`/`WSP` register-31 semantics and 16-byte `SP`
   alignment (`Arm DDI 0487` C1.2.5 & D1.3.2):** Register specifier `31` means
   `SP`/`WSP` in `ADD`/`SUB` immediate (`readSp`/`writeSp`), base registers of
   memory addressing (`evalAddrMode`, checking `(base &&& 0xf#64) != 0#64` $\to$
   `.spAlignmentFault` whenever `rn == 31`), and logical-immediate destinations
   when `S = 0`, while meaning `XZR`/`WZR` (`readXzr`/`writeXzr`) in shifted-register
   ALU, flag-setting `ADDS`/`SUBS`/`ANDS` (`CMN`/`CMP`/`TST`), transfer operands
   `Rt`/`Rt2`, multiplication/division, and `FMOV`/`UMOV`/`DUP`/`INS`.

Three Lean `v4.34.1` kernel-engineering techniques keep compilation under `9 s`
per module with `0` `isPartial` helpers:
- **`Nat.rec` elimination of `*._unsafe_rec` and `List.rec` noncomputability:**
  Replacing equation-compiler recursion (`execStepsN`, `clzWidth`, `crc32Multi`,
  `popcntByte`, `pmullByte`, `pmull64`, `uaddlvLoop`, `umaxvLoop`, `uminvLoop`)
  and `List.rec` (`listGetOpt`) with `Nat.rec` eliminates both `isPartial = true`
  (`*._unsafe_rec`) entries and Lean code-generator `dependsOnNoncomputable`
  rejections (`0` `partial_consts` across all `3,356` delta constants).
- **6-way decoder group factoring (`VendorArm64Ref/Decode.lean`):** Factoring
  `decodeWord32` into `decodeSysBranch`, `decodeDpImm`, `decodeDpReg`,
  `decodeLoadsStores`, `decodeCryptoExt`, and `decodeNeon` prevents nested
  `ite`-chain type-inference quadratic blowup, compiling all `655` LOC in
  **`1.47 s`**.
- **4-bit Sarwate `Nat` nibble CRC32 and `gfXtimeNat` `AESIMC` reduction:**
  Evaluating reflected CRC-32/CRC-32C (`crc32Multi`) in `2` 16-entry nibble
  steps per byte (`16` steps for 64-bit `CRC32X`/`CRC32CX`) and `gfMul9/11/13/14`
  via C++ GMP `Nat` primitives (`Nat.xor`, `Nat.land`, `Nat.shiftRight`) avoids
  $O(2^{64})$ call-by-name `ite` duplication in WHNF, allowing all `224` live
  QEMU vectors—including 64-bit `CRC32X`/`CRC32CX` and 5-instruction AES
  encryption/decryption roundtrips—to check by pure kernel `rfl` with zero
  `set_option` overrides.

| Module (`support/`) | Source LOC / Bytes | Cold Compile (`ms`) | Peak RSS (`kB`) | `.olean` (`B`) | Kernel Consts | Private Replay (`ms`) | Axioms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| `IntrinsicAarch64Ext.lean` | `691` / `35,099` | `2,821.78` | `327,472` | `2,352,568` | `204` | **`165`** (`204` $\Delta$) | `Quot.sound, propext` |
| `VendorArm64Ref/Types.lean` | `313` / `11,386` | `3,784.26` | `384,856` | `6,121,568` | `1,500` | *(in `489`)* | `Quot.sound, propext` |
| `VendorArm64Ref/Decode.lean` | `655` / `28,553` | `1,465.49` | `307,760` | `1,404,400` | `32` | *(in `489`)* | `Quot.sound, propext` |
| `VendorArm64Ref/SemanticsScalar.lean` | `559` / `22,195` | `1,071.90` | `305,192` | `1,140,128` | `45` | *(in `489`)* | `Quot.sound, propext` |
| `VendorArm64Ref/SemanticsNeon.lean` | `832` / `37,020` | `2,121.08` | `330,728` | `2,253,488` | `76` | *(in `489`)* | `Quot.sound, propext` |
| `VendorArm64Ref/Machine.lean` | `97` / `3,776` | `360.64` | `290,336` | `133,696` | `25` | **`489`** (`1,678` $\Delta$) | `Quot.sound, propext` |
| `WordArm64Pass2Correspondence.lean` | `669` / `31,154` | `5,219.22` | `358,572` | `3,330,400` | `357` | **`991`** (`357` $\Delta$) | `Quot.sound, propext` |
| `NeonTriangulationCore.lean` | `738` / `45,904` | `7,171.99` | `451,620` | `1,087,696` | `242` | *(in `13,525`)* | `Classical.choice, Quot.sound, propext` |
| `NeonTriangulation24.lean` | `218` / `13,082` | `8,774.58` | `433,560` | `4,386,592` | `390` | **`13,525`** (`3,356` $\Delta$ w/ `QemuCheck224`) | `Classical.choice, Quot.sound, propext` |
| **Total (`9` staged `.lean` modules)** | **`4,772` / `228,169`** | **`32,790.94`** | **`451,620` max** | **`22,210,536`** | **`2,871`** (`3,356` w/ `QemuCheck224`) | **`15,170` sum** | **`0` `sorry`, `0` `partial`, `0` `unsafe`** |

### 3. Live 224-vector QEMU (`-cpu max` vs `-cpu cortex-a53`) & LLVM disassembler cross-check and Pass-2 `WordArm64` correspondence

Basis: normative + source + execution + derived

`support/probe_qemu_224_aarch64_vectors.py`
(`support/probe_qemu_224_aarch64_vectors_results.json`) compiles an AArch64 EL0
ELF harness with `SA_SIGINFO` `sigsetjmp`/`siglongjmp` recovery for `SIGILL` and
`SIGBUS` and executes **`224` vectors** across `qemu-aarch64 11.1.2` (`-cpu max`
and `-cpu cortex-a53`), `llvm-mc 21.1.8 --triple=aarch64 --disassemble`, and
`llvm-objdump 21.1.8 -d`:

- **Category A (`32` fault, unallocated, constrained-unpredictable, and `SP`
  alignment vectors):**
  - `18 / 18` `UDF` (`0x00000000`, `0x0000dead`) and unallocated bitfield
    encodings (`add` `shift=0b11`, 32-bit `lsl/lsr/extr` `imm >= 32`, `add`
    extended `imm3 > 4`, `ubfm` `N=1` with `sf=0`, `rev` `opc` mismatch, `crc32`
    `sf/sz` mismatch, 64-bit `ext v0.8b` `imm4 >= 8`, `dup v0.1d`, `umov x0,
    v0.b[0]`, `cmgt v0.1d`, `uaddlv v0.2s`) raise **`SIGILL` (`sig = 4`)** on
    both CPUs;
  - `4 / 4` misaligned `SP` accesses (`ldr x0, [sp]`, `str x0, [sp]`, `ldp x0,
    x1, [sp]`, `ldr q0, [sp]` with `SP & 0xf ∈ {4, 8}`) raise **`SIGBUS` (`sig =
    7`)**;
  - Across the `10` constrained-unpredictable overlap encodings (`ldp x0, x0,
    [x4]`, `ldp w2, w2, [x4]`, `ldp xzr, xzr, [x4]`, `ldp q0, q0, [x4]`,
    writeback `ldr/str/ldp/stp` with `Rn == Rt`, and `stlxr` `Rs == Rt` / `Rs ==
    Rn`), **`llvm-objdump 21.1.8 -d` emits zero warnings on `10 / 10` (`100.0%`)**
    and **`llvm-mc 21.1.8 --disassemble` emits zero warnings on `4 / 10` (`40.0%`)**
    (accepting `ldp xzr, xzr, [x4]`, `ldp d0, d0, [x4]`, and `stlxr` `Rs == Rt` /
    `Rs == Rn` silently), confirming that off-the-shelf LLVM disassemblers
    cannot serve as a Pass-2 legality oracle.
- **Category B (`16` `LDAR`/`STLR`/`LDAXR`/`STLXR`/`CLREX` alignment & exclusive-monitor
  vectors):** Exposes **`6` architectural divergences** between `-cpu max`
  (`FEAT_LSE2`) and `-cpu cortex-a53` (`Armv8.0-A`): intra-16-byte unaligned
  `ldar x0, [x4+4]`, `ldar w0, [x4+2]`, `ldarh w0, [x4+1]`, `stlr x0, [x4+4]`,
  `ldaxr x0, [x4+4]`, and `ldar x0, [x4+8]` succeed (`sig = 0`) under `FEAT_LSE2`
  but raise **`SIGBUS` (`sig = 7`)** on `cortex-a53`, whereas cross-16-byte
  `ldar x0, [x4+12]` and `stlr x0, [x4+12]` raise **`SIGBUS` (`sig = 7`)** on
  both CPUs! Also verifies `LDAXR`+`STLXR` success (`w2 = 0`), `CLREX` failure
  (`w2 = 1`, memory untouched), `STLXR` without prior `LDAXR` failure (`w2 = 1`),
  and intervening `STR` clearing the exclusive monitor (`w2 = 1`).
- **Categories C & D (`96` scalar GP/branch/CRC32 vectors + `80` NEON/Crypto
  vectors):** Verifies `W`-write upper-32 zeroing, `D`-write upper-64 zeroing,
  `XZR` vs `SP` register-31 routing, `ADCS`/`SBCS` 128-bit carry/borrow chains,
  `UDIV`/`SDIV` by zero $\to 0$ and `INT64_MIN / -1` wrapping to `INT64_MIN`,
  `ADRP` at `PC & 0xfff == 0xffc`, `CRC32B/H/W/X` + `CRC32CB/CH/CW/CX`, and all
  NEON + `AESE`/`AESMC`/`AESD`/`AESIMC` + `SHA256*` + `SHA512*` instructions.
  Every single one of the `224` vectors checks by kernel `rfl` in `QemuCheck224`.

`support/WordArm64Pass2Correspondence.lean` formalizes an independent operational
target `WordArm64` (recording a 32-entry `regs : Reg5 → BitVec 64` file with
`regs 31 = 0#64` invariant `WfState`) and proves five Pass-2 theorems:

1. **`s2n_assigns_entirety_unsound_frame_violation`:** Constructs two valid post-states
   under `S2nRawAssignsEntiretyStep` on `0xa9400080` (`ldp x0, x0, [x4]`) showing
   that raw `s2n-bignum`'s fallback allows `X19` (`0x1111_2222_3333_4444` $\to$
   `0xdead_dead_dead_dead`) and unrelated memory (`0x90000`) to be overwritten
   while `VendorArm64Ref` deterministically rejects the instruction with
   `fault = some .constrainedUnpredictable`.
2. **`misaligned_ldar_lse2_narrow_refinement_counterexample`:** Proves that an
   `FEAT_LSE2`-overfit target (`WordArm64.StepNarrow`, permitting intra-16-byte
   unaligned `LDAR x0, [x4]` at `x4 = 0x20004`) fails Pass-2 simulation against
   strict Armv8.0-A (`lse2Align16B = false`, which raises `.alignmentFault` as
   observed on `-cpu cortex-a53`).
3. **`stlxr_spurious_fail_narrow_refinement_counterexample` &
   `qemu_stlxr_deterministic_in_vendorArm64Ref`:** On single-threaded
   `qemu-aarch64`, `ldaXR x0, [x4] ; stlxr w2, x1, [x4]` always succeeds (`w2 =
   0`), tempting `WordArm64.StepNarrow` to omit spurious `STLXR` failure. Arm
   DDI 0487 B2.9.5 explicitly permits an `ExclusiveMonitorsPass()` implementation
   to fail spuriously (`status = 1`, memory unchanged), falsifying
   `VendorArm64Ref.Step ⊆ WordArm64.StepNarrow` when `exclSpuriousFail = true`.
4. **`vendorArm64Ref_step_sub_wordArm64_step` &
   `vendorArm64Ref_stepsN_sub_wordArm64_stepsN`:** With `exclSpuriousFail : Bool`
   in `WordArm64.DemonicChoice` and explicit `lse2Align16B` parameterization,
   proves universal single-step and `N`-step simulation across the entire
   `VendorArm64Ref` ISA (`∀ code lse2 n s s', VendorArm64Ref.StepsN code lse2 n
   s s' → WordArm64.StepsN code lse2 n (toWordState s) (toWordState s')`).

### 4. Three-way Pass-2 triangulation across all 25 curated `core::arch::aarch64` primitives (`34` `.o` functions)

Basis: normative + source + execution + derived

`support/probe_28_core_arch_aarch64_obj.py`
(`support/probe_28_core_arch_aarch64_obj_results.json`) compiles `25` curated
`core::arch::aarch64` primitives (`14` portable `simd_*` operations + `11`
`llvm.aarch64.*` families) plus `9` signed/width/boundary/crypto companions (`34`
AAPCS64 `extern "C"` functions total) at `-C opt-level=3 --target
aarch64-unknown-linux-gnu` across **three `rustc` toolchains** (`1.99.1` `LLVM
23.1.1`, `1.101.0-nightly` `LLVM 23.1.1`, and `1.95.0-nightly` `LLVM 21.1.8`).
All **`34 / 34` (`100.0%`)** functions emit **word-identical 32-bit AArch64 `.o`
instruction sequences** across all three compilers and pass live execution on
`qemu-aarch64 11.1.2 -cpu max`.

In `support/NeonTriangulationCore.lean` and `support/NeonTriangulation24.lean`,
we decouple closed `(code, pc)` `.o` instruction decoding (`fetchDecodeAt`) from
symbolic `MachineState` stepping (`execStep_of_fetchDecode`), avoiding `isDefEq`
`lazyDeltaReduction` backtracking over symbolic `s.pc` and proving **all `4`
UB/crypto asymmetry theorems** plus **all `34` universally quantified
(`∀ a b c sp lr mem`) 3-way triangulation theorems** (`TriangulatedVec128`,
`TriangulatedGp64`, `TriangulatedGpPair128`):

| ID | `core::arch::aarch64` API | MIR / `llvm.aarch64.*` Lowering | Exact `rustc -O3` `.o` Words (`3` Toolchains) | Decoded AArch64 Sequence & Backend Optimization | Theorem (`NeonTriangulation24.*`) |
| --- | --- | --- | --- | --- | --- |
| `p01` | `vaddq_u8` | `simd_add` | `0x4e208420, 0xd65f03c0` | `add v0.16b,v1.16b,v0.16b; ret` *(commutes `b + a`)* | `triangulate_p01_vaddq_u8` |
| `p02` | `vsubq_u8` | `simd_sub` | `0x6e218400, 0xd65f03c0` | `sub v0.16b,v0.16b,v1.16b; ret` | `triangulate_p02_vsubq_u8` |
| `p03` | `vandq_u8` | `simd_and` | `0x4e201c20, 0xd65f03c0` | `and v0.16b,v1.16b,v0.16b; ret` *(commutes `b & a`)* | `triangulate_p03_vandq_u8` |
| `p04` | `vorrq_u8` | `simd_or` | `0x4ea01c20, 0xd65f03c0` | `orr v0.16b,v1.16b,v0.16b; ret` *(commutes `b \| a`)* | `triangulate_p04_vorrq_u8` |
| `p05` | `veorq_u8` | `simd_xor` | `0x6e201c20, 0xd65f03c0` | `eor v0.16b,v1.16b,v0.16b; ret` *(commutes `b ^ a`)* | `triangulate_p05_veorq_u8` |
| `p06` | `vceqq_u8` | `simd_eq` | `0x6e218c00, 0xd65f03c0` | `cmeq v0.16b,v0.16b,v1.16b; ret` | `triangulate_p06_vceqq_u8` |
| `p07` | `vcgtq_u8` | `simd_gt` (unsigned) | `0x6e213400, 0xd65f03c0` | `cmhi v0.16b,v0.16b,v1.16b; ret` | `triangulate_p07_vcgtq_u8` |
| `p08` | `vcltq_s8` | `simd_lt` (signed) | `0x4e203420, 0xd65f03c0` | `cmgt v0.16b,v1.16b,v0.16b; ret` *(reverses `b >s a`)* | `triangulate_p08_vcltq_s8` |
| `p09` | `vqaddq_u8` | `simd_saturating_add` | `0x6e210c00, 0xd65f03c0` | `uqadd v0.16b,v0.16b,v1.16b; ret` | `triangulate_p09_vqaddq_u8` |
| `p10` | `vqsubq_u8` | `simd_saturating_sub` | `0x6e212c00, 0xd65f03c0` | `uqsub v0.16b,v0.16b,v1.16b; ret` | `triangulate_p10_vqsubq_u8` |
| `p11` | `vshlq_u8` | `neon.ushl.v16i8` | `0x6e214400, 0xd65f03c0` | `ushl v0.16b,v0.16b,v1.16b; ret` *(signed bidir shift)* | `triangulate_p11_vshlq_u8` |
| `p11b` | `vshlq_s8` | `neon.sshl.v16i8` | `0x4e214400, 0xd65f03c0` | `sshl v0.16b,v0.16b,v1.16b; ret` *(signed bidir arith)* | `triangulate_p11b_vshlq_s8` |
| `p12` | `vshlq_n_u32::<7>` | `simd_shl(a, splat(7))` | `0x4f275400, 0xd65f03c0` | `shl v0.4s,v0.4s,#7; ret` | `triangulate_p12_vshlq_n_u32_7` |
| `p12b` | `vshrq_n_u32::<7>` | `simd_shr(a, splat(7))` | `0x6f390400, 0xd65f03c0` | `ushr v0.4s,v0.4s,#7; ret` | `triangulate_p12b_vshrq_n_u32_7` |
| `p12c` | `vshrq_n_u32::<32>` | `if N==32 { splat(0) }` | `0x6f00e400, 0xd65f03c0` | `movi v0.2d,#0; ret` *(boundary `32` guard $\to 0$)* | `triangulate_p12c_vshrq_n_u32_32` |
| `p12d` | `vshrq_n_s32::<32>` | `if N==32 { simd_shr(31) }` | `0x4ea0a800, 0xd65f03c0` | `cmlt v0.4s,v0.4s,#0; ret` *(sign-mask `== >>s 31`!)* | `triangulate_p12d_vshrq_n_s32_32` |
| `p13` | `vqtbl1q_u8` | `neon.tbl1.v16i8` | `0x4e010000, 0xd65f03c0` | `tbl v0.16b,{v0.16b},v1.16b; ret` *(`>=16` $\to 0$)* | `triangulate_p13_vqtbl1q_u8` |
| `p14` | `vpaddq_u8` | `neon.addp.v16i8` | `0x4e21bc00, 0xd65f03c0` | `addp v0.16b,v0.16b,v1.16b; ret` | `triangulate_p14_vpaddq_u8` |
| `p15` | `vpaddlq_u8` | `neon.uaddlp.v8i16.v16i8` | `0x6e202800, 0xd65f03c0` | `uaddlp v0.8h,v0.16b; ret` | `triangulate_p15_vpaddlq_u8` |
| `p16` | `vaddlvq_u8` | `neon.uaddlv.i32.v16i8` | `0x6e303800, 0x1e260000, 0xd65f03c0` | `uaddlv h0,v0.16b; fmov w0,s0; ret` *(3-step `W0`)* | `triangulate_p16_vaddlvq_u8` |
| `p17` | `vmaxvq_u8` | `neon.umaxv.i8.v16i8` | `0x6e30a800, 0x1e260000, 0xd65f03c0` | `umaxv b0,v0.16b; fmov w0,s0; ret` *(3-step `W0`)* | `triangulate_p17_vmaxvq_u8` |
| `p17b` | `vminvq_u8` | `neon.uminv.i8.v16i8` | `0x6e31a800, 0x1e260000, 0xd65f03c0` | `uminv b0,v0.16b; fmov w0,s0; ret` *(3-step `W0`)* | `triangulate_p17b_vminvq_u8` |
| `p18` | `vrev64q_u8` | `simd_shuffle` (128-bit) | `0x4e200800, 0xd65f03c0` | `rev64 v0.16b,v0.16b; ret` | `triangulate_p18_vrev64q_u8` |
| `p18b` | `vrev64_u8` | `simd_shuffle` (64-bit) | `0x0e200800, 0xd65f03c0` | `rev64 v0.8b,v0.8b; ret` *(zeroes `V0[127:64]`!)* | `triangulate_p18b_vrev64_u8` |
| `p19` | `vextq_u8::<5>` | `simd_shuffle` (`k+5`) | `0x6e012800, 0xd65f03c0` | `ext v0.16b,v0.16b,v1.16b,#5; ret` | `triangulate_p19_vextq_u8_5` |
| `p20` | `vbslq_u8` | `(a & m) \| (b & ~m)` | `0x6e621c20, 0xd65f03c0` | `bsl v0.16b,v1.16b,v2.16b; ret` *(destructive `Rd=m`)* | `triangulate_p20_vbslq_u8` |
| `p21` | `vcntq_u8` | `simd_ctpop` | `0x4e205800, 0xd65f03c0` | `cnt v0.16b,v0.16b; ret` | `triangulate_p21_vcntq_u8` |
| `p22` | `vmull_p8` | `neon.pmull.v8i16` | `0x0e21e000, 0xd65f03c0` | `pmull v0.8h,v0.8b,v1.8b; ret` | `triangulate_p22_vmull_p8` |
| `p22b` | `vmull_p64` | `neon.pmull64` | `0x9e670020, 0x9e670001, 0x0ee0e020, 0x4e183c01, 0x9e660000, 0xd65f03c0` | `fmov d0,x1; fmov d1,x0; pmull v0.1q,v1.1d,v0.1d; mov x1,v0.d[1]; fmov x0,d0; ret` *(6-step `X1:X0`)* | `triangulate_p22b_vmull_p64` |
| `p23` | `vaeseq_u8` | `crypto.aese` | `0x4e284820, 0xd65f03c0` | `aese v0.16b,v1.16b; ret` *(pre-`SubBytes` XOR)* | `triangulate_p23_vaeseq_u8` |
| `p23b` | `vaesmcq_u8` | `crypto.aesmc` | `0x4e286800, 0xd65f03c0` | `aesmc v0.16b,v0.16b; ret` | `triangulate_p23b_vaesmcq_u8` |
| `p24` | `vsha512hq_u64` | `crypto.sha512h` | `0xce628020, 0xd65f03c0` | `sha512h q0,q1,v2.2d; ret` | `triangulate_p24_vsha512hq_u64` |
| `p24b` | `vsha512su0q_u64` | `crypto.sha512su0` | `0xcec08020, 0xd65f03c0` | `sha512su0 v0.2d,v1.2d; ret` | `triangulate_p24b_vsha512su0q_u64` |
| `p25` | `__crc32cd` | `crc32cx` | `0x9ac15c00, 0xd65f03c0` | `crc32cx w0,w0,x1; ret` *(`W0` zeroes `[63:32]`!)* | `triangulate_p25_crc32cd` |

### 5. Architectural integration path for Anneal Pass-2 correspondence

Basis: source + derived

Together, these artifacts establish a concrete, zero-axiom two-track AArch64
integration path for `joshlf/anneal`:

1. **MIR-level `core::arch::aarch64` verification (`vendor/lean-miri`):** Wire
   `IntrinsicAarch64Ext.evalAarch64Ext` (`204` constants, `165 ms` private
   kernel replay, `0` `by` blocks, `0` `isPartial`) ahead of
   `Miri.Interpreter.IntrinsicArchitecture.aarch64` to lift 12-crate pure-Rust
   AArch64 SIMD coverage from `88.35%` (`584 / 661`) to **`100.00%` (`661 /
   661`)** without altering Anneal's Pass-1 `Trusted` MIR AST.
2. **Object-level `aarch64` Pass-2 correspondence (`VendorArm64Ref`
   $\leftrightarrow$ `WordArm64`):** Generate `VendorArm64Ref` deterministically
   from pinned `s2n-bignum` + Arm ASL legality guards using `Nat.rec` loops (`0`
   `isPartial`, `489 ms` private replay), parameterize `WordArm64` explicitly by
   `lse2Align16B : Bool` (`false` for portable Armv8.0-A guarantees) and demonic
   `exclSpuriousFail : Bool` on `STLXR`, and reject all constrained-unpredictable
   `Rt == Rt2` / `Rn == Rt` overlap encodings fail-closed at decode time rather
   than inheriting `s2n-bignum`'s `ASSIGNS entirety` havoc.

## Boundaries

- **Scalable Vector Extension (`SVE`/`SVE2`) and Scalable Matrix Extension
  (`SME`) (`not examined` in `VendorArm64Ref`):** While `vendor/lean-miri`'s
  `IntrinsicArchitecture.lean` already models basic SVE predicate/vector MIR
  intrinsics, variable-length `Z0..Z31` (`128..2048`-bit) and `P0..P15`
  encodings were **not examined** in `VendorArm64Ref` or `WordArm64`, which
  model fixed-width 64/128-bit `V0..V31` Advanced SIMD (`NEON`) and Crypto.
- **Floating-point NEON/scalar arithmetic and `FPCR`/`FPSR` status/rounding
  flags (`not examined` in `VendorArm64Ref`):** `VendorArm64Ref` models bit-exact
  GPR$\leftrightarrow$SIMD `FMOV` (`1e260000`, `9e660000`, `9e670000`) because
  Rust/LLVM uses `fmov w0, s0` and `fmov d0, x1` to transfer integer reduction
  and `pmull64` operands without touching `FPSR`, whereas IEEE-754 `FADD`/`FMUL`/`FCVT`
  and `FPCR` rounding/flush-to-zero modes were **not examined**.
- **Pointer Authentication (`PAC`), Memory Tagging (`MTE`), Top-Byte Ignore
  (`TBI`), and `FEAT_LSE` CAS/LDADD (`not examined` here):** `BTI` hints are
  decoded as architectural no-ops (`0xd503241f`..`0xd50324df`), while PAC/MTE/TBI
  address tagging and Armv8.1 `CAS`/`SWP`/`LDADD` atomics are covered separately
  in sibling corpus report
  `aarch64-pac-mte-tbi-provenance-sve-clobbers-and-outlined-atomics-ffi-seams`
  and fail closed as `.undefinedEncoding` in `VendorArm64Ref`.
- **Direct MIR `simd_shl`/`simd_shr` or cross-ISA AES round substitution without
  wrapper/key-schedule alignment (`known not to apply`):** As proved in
  `unguarded_miri_simd_shl_ub_vs_neon_ushl_bidir`,
  `unguarded_miri_simd_shr_32_ub_vs_rustc_cmlt_zero`, and
  `arm_aese_aesmc_ne_x86_vaesenc_single_key`, raw MIR `simd_shl`/`simd_shr` are
  **not** total refinements of NEON `USHL`/`SSHL`/`CMLT #0`, and single-key
  `aesmc(aese(pt, rk0))` is **not** equivalent to x86 `vaesenc(pt, rk0)`;
  equivalence holds only via `stdarch`'s clamped wrappers and the 2-key round
  isomorphism `aesmc(aese(state, rk0)) ^^^ rk1 = x86Vaesenc(state ^^^ rk0, rk1)`.
- **Weak multi-copy-atomic concurrency ordering of `LDAR`/`STLR`/`LDAXR`/`STLXR`
  (`not examined`):** `VendorArm64Ref` and `WordArm64` verify exact sequential
  alignment checks (`FEAT_LSE2` vs Armv8.0-A), local `ExclusiveMonitor`
  clearing (`CLREX`, intervening stores), and demonic `STLXR` spurious failure,
  but multi-thread Armv8 memory-consistency axiomatics (`herd7` `cat` models)
  were **not examined**.
- **Hardware silicon vs `qemu-aarch64` user-mode trap fidelity (`known not to
  apply` for microarchitectural constrained-unpredictable choices):** On
  `qemu-aarch64 11.1.2`, `ldp x0, x0, [x4]` executes a specific microarchitectural
  choice without raising `SIGILL`, and single-threaded `stlxr` never fails
  spuriously (`w2 = 0`). Both behaviors are **known not to apply** as portable
  architectural guarantees across physical Armv8/v9 cores, which is why
  `VendorArm64Ref` rejects constrained-unpredictable overlaps fail-closed and
  `WordArm64` models `STLXR` spurious failure demonically.

## Evidence

### Primary upstream sources and normative specifications

- **Arm Architecture Reference Manual (`normative`):** *Arm Architecture
  Reference Manual for A-profile architecture*, Document `DDI 0487`, Edition
  `L.a` (Arm Limited): Sections B2.2.1 (`FEAT_LSE2` 16-byte single-copy-atomic
  alignment vs base natural alignment), B2.9.5 (`LoadExcl` / `StoreExcl` and
  spurious `ExclusiveMonitorsPass()` failure), C1.2.5 (`XZR`/`WZR` vs `SP`/`WSP`
  register-31 encoding and upper-32/upper-64 register write zeroing), D1.3.2
  (16-byte `SP` alignment fault), K1.1.2 (constrained-unpredictable `LDP`/`STP`
  and writeback register overlap), and C7.2 (`AESE`, `AESMC`, `AESD`, `AESIMC`,
  `PMULL`/`PMULL2`, `SHA512H`, `SHA512H2`, `SHA512SU0`, `SHA512SU1`, `USHL`,
  `SSHL`, `UADDLV`).
- **NIST Cryptographic Standards (`normative`):** `FIPS PUB 197-upd1` (*Advanced
  Encryption Standard*, May 2023, Appendix B cipher example) and `FIPS PUB
  180-4` (*Secure Hash Standard*, August 2015, Section 4.1.3 & B.2 SHA-512
  `"abc"` example).
- **`awslabs/s2n-bignum` (`source`):** Commit
  `d4518712d040485efe621caba1c723a07fbc549e`:
  - `arm/proofs/instruction.ml` (blob `ef9be01f4e078ed0c58da94861c57335046f803e`,
    `181,272` B: `229` `arm_*` definitions, `PC - 4` compensation at `L748-1395`,
    and `21` `ASSIGNS entirety` fallback clauses at `L2945-3502`);
  - `arm/proofs/decode.ml` (blob `d71476c172132a05ea5130eee00017e1b5e5dd66`,
    `111,754` B: `228` bitmatch arms, `~q then NONE` rejections at
    `L1036, 1044, 1321, 1530, 1537`, and `.b`/`.h` `UMOV` rejection at `L1494`);
  - `arm/proofs/arm.ml` (blob `8084bff141e0b0acd81f7b38705990cb3c6b6cfa`,
    `67,256` B: pre-increment `PC := word_add (read PC s) (word 4)` at `L140`);
  - `arm/proofs/neon_helper.ml` (blob `afa2e916317034cb833026f698356014d8f6f0d9`,
    `39,686` B), `arm/proofs/sha256.ml` (blob
    `a4a56982f38ca626f23ef4fe7538c3a1e1122307`, `12,501` B),
    `arm/proofs/sha512.ml` (blob `918a24d3caf47a5cf64a2a24efde0010ee4f03c4`,
    `11,550` B), `arm/proofs/simulator_iclasses.ml` (blob
    `281b03c2cc1f571b04663d1ddfc9cd08de2cff3a`, `29,160` B), and `common/aes.ml`
    (blob `520c48a50f87d7669e42cc154d120c1fae024f29`, `21,668` B).
- **`proofs-rs/lean-miri` & `joshlf/anneal` (`source`):**
  `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
  - `vendor/lean-miri/UPSTREAM_PIN.json` (pinning
    `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, `lean
    v4.34.1`);
  - `vendor/lean-miri/Miri/Interpreter/IntrinsicArchitecture.lean` (`aarch64`
    dispatcher at `L161-306`), `IntrinsicSimd.lean`, and `IntrinsicCrypto.lean`;
  - `trusted/audit/TrustedBoundary.lean` (`ensureReplayableConstant` at
    `L1117-1125` and `replayCorrAndVendor` at `L2140-2201`).

### Preserved package support material (`execution` + `derived`)

All experimental probes, transpiled Lean modules, correspondence and
triangulation proofs, and machine-readable JSON receipts are preserved under
`support/` (observed on `2026-11-21` on `Linux 7.1.6-1rodete1-amd64`):

- **`vendor/lean-miri` AArch64 audit & pure Lean gap-closure extension:**
  `support/IntrinsicAarch64Ext.lean`, `support/probe_lean_miri_aarch64_audit.py`,
  and `support/probe_lean_miri_aarch64_audit_results.json`.
- **Transpiler & emitted `VendorArm64Ref` Lean modules:**
  `support/transpile_s2n_arm_to_lean.py`, `support/s2n_arm_transpiler_audit.json`,
  and `support/VendorArm64Ref/{Types,Decode,SemanticsScalar,SemanticsNeon,Machine}.lean`.
- **Pass-2 `WordArm64` correspondence & counterexample proofs:**
  `support/WordArm64Pass2Correspondence.lean`.
- **3-way `core::arch::aarch64` NEON/Crypto/CRC32 triangulation & asymmetry
  proofs:** `support/NeonTriangulationCore.lean`, `support/NeonTriangulation24.lean`,
  `support/probe_28_core_arch_aarch64_obj.py`, and
  `support/probe_28_core_arch_aarch64_obj_results.json`.
- **Live 224-vector `qemu-aarch64` (`-cpu max` & `-cpu cortex-a53`) & LLVM
  disassembler probe:** `support/probe_qemu_224_aarch64_vectors.py` and
  `support/probe_qemu_224_aarch64_vectors_results.json`.
- **End-to-end compile, `224`-vector kernel `rfl` check, and private kernel
  replay benchmark:** `support/benchmark_lean_aarch64_pass2_and_triangulation.py`
  and `support/lean_aarch64_pass2_and_triangulation_benchmark_results.json`.

## Revalidation

Run these narrow discriminating checks from the package directory (wrapping Lean
invocations in the host cgroup/slot runner where applicable; all scripts create
and clean up their own `tempfile.TemporaryDirectory()` workspaces):

1. **Revalidate all `9` staged Lean modules, `224 / 224` QEMU vectors
   (`QemuCheck224`), `0` `isPartial`/`unsafe`/`sorry` invariants, and standalone
   `(trustLevel := 0, level := .private)` kernel replay (~`85 s` total):**
   ```console
   python3 -B support/benchmark_lean_aarch64_pass2_and_triangulation.py \
     --lean-bin lean \
     --out-json /tmp/reval_aarch64_bench.json
   ```
   Confirm `rc = 0`, `zero_warnings_and_errors: true` on every module, compile
   times `< 15 s` on every staged `.lean` file, and `partial_consts: []`,
   `unsafe_consts: []`, `axiom_consts: []`, `opaque_consts: []`,
   `forbidden_refs: []` under `private_kernel_replay.all`.
2. **Revalidate `rustc -C opt-level=3` AArch64 `.o` word stability and live QEMU
   differential execution across a newer `rustc` or LLVM release (~`5 s`):**
   ```console
   python3 -B support/probe_28_core_arch_aarch64_obj.py \
     --out-json /tmp/reval_aarch64_obj.json
   ```
   Confirm `cross_toolchain_word_identical: true` and `qemu_differential_returncode:
   0`. If a newer LLVM backend selects an alternate instruction sequence for any
   primitive `pXX`, update `pXXWords` and `triangulate_pXX_*` in
   `support/NeonTriangulationCore.lean` or `support/NeonTriangulation24.lean`
   and re-run step 1.
3. **Revalidate `vendor/lean-miri` AArch64 crate coverage and `IntrinsicAarch64Ext`
   FIPS-197 / FIPS-180-4 cross-checks on a bumped `lean-miri` or `stdarch`
   revision (~`8 s`):**
   ```console
   python3 -B support/probe_lean_miri_aarch64_audit.py \
     --vendor-dir <path-to-vendor-lean-miri> \
     --lean-bin lean \
     --out-json /tmp/reval_aarch64_miri.json
   ```
   Confirm `covered_after_ext_pct: 100.0` (`remaining_after_ext: []`),
   `qemu_returncode: 0`, and `partial_consts: []` under
   `intrinsic_aarch64_ext_lean_audit.private_kernel_replay`.
4. **Revalidate live `224`-vector `A64` trap, `FEAT_LSE2` alignment, scalar, and
   NEON/Crypto behavior on a new QEMU version or physical Armv8/v9 host (~`4 s`):**
   ```console
   python3 -B support/probe_qemu_224_aarch64_vectors.py \
     --out-json /tmp/reval_aarch64_qemu.json
   ```
   Confirm `total_vectors: 224` and pass the updated JSON into step 1 to verify
   that every observed transition remains inside `VendorArm64Ref.Step` (and
   therefore `WordArm64.Step`).
