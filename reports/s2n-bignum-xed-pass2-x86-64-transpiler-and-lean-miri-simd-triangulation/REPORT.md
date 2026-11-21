# Mechanical s2n-bignum + Intel XED Pass-2 x86-64 reference transpilation, vendor/lean-miri SIMD/x86 audit, and 3-way core::arch SIMD triangulation in Lean 4

## Summary

Closing the Pass-2 reference-correspondence gap for byte-decoded `x86_64`
machine code and `core::arch::x86_64` SIMD intrinsics in Lean `v4.34.1`
yields four empirically and mechanically verified results:

1. **Combining `awslabs/s2n-bignum` with an `intelxed/xed` legality and opcode
   overlay produces a fast, pure `Init.*` Pass-2 reference model
   (`VendorX86Ref`), whereas raw `s2n-bignum` alone rejects `50.0%` of
   `rustc -O3` SIMD primitives and `20.98%` of hardware trap/encoding
   specimens.** Because zero upstream Lean 4 x86-64 byte-decoding ISA models
   exist and both `llvm-mc 21.1.8` and `objdump 2.47` silently accept **`18 / 24`
   (`75.0%`)** of decode-fault traps (`18 / 18 = 100.0%` of overlong `> 15`-byte
   `#GP(0)` and legacy-prefixed VEX/`LOCK` `#UD` encodings), we built a
   deterministic Python transpiler (`support/transpile_s2n_xed_to_lean.py`) over
   pinned `awslabs/s2n-bignum@d4518712d040485efe621caba1c723a07fbc549e`
   (`x86/proofs/{instruction,decode,x86}.ml`) and
   `intelxed/xed@0bcb6237345c5066726dcc08b3d87928df3b5b26` (`25` ISA datafiles,
   `1,334` `ICLASS` entries). It emits 5 sharded `prelude` + `Init.*` modules
   (`support/VendorX86Ref/*.lean`) covering **`75` architectural opcodes** across
   scalar GP ALU, BMI1/BMI2, ADX, `CMOVcc`/`SETcc`, ModR/M+SIB+displacement,
   `LOCK` atomics, `ENDBR64`, and VEX/EVEX 128/256-bit SIMD + AES-NI +
   `VPCLMULQDQ`. Emitting bounded loops via `Nat.rec` eliminates **`12 / 12`
   (`100%`)** of Lean compiler-generated `*._unsafe_rec` (`isPartial`) helpers.
   All 5 `VendorX86Ref` modules compile in **`9.03 s` sequential wall time**
   (`0.36 s`–`4.26 s` per module, `11.42 MB` `.olean`, peak RSS `387 MB`),
   replay from scratch at `(trustLevel := 0, level := .private)` in **`547 ms`**
   (`1,831` kernel constants, axioms `["Quot.sound", "propext"]`), and match
   **`224 / 224` (`100.0%`)** of controlled execution/trap vectors on live Intel
   Xeon Ice Lake-SP silicon (`SiliconCheck224.all_224_silicon_vectors_match`).
2. **Pass-2 correspondence (`VendorX86Ref.Step ⊆ ByteX86.Step`) catches
   silicon-overfitting in `ByteX86` on `BSF`/`BSR` zero inputs.** On Ice Lake-SP
   silicon, `bsf rax, rcx` (`48 0f bc c1`) with `rcx = 0` preserves `rax`'s
   prior value, tempting an operational model (`ByteX86.StepNarrow`) to
   hardcode `oldDst`. `s2n-bignum` (`x86/proofs/x86.ml:902`,
   `if x = word 0 then UNDEFINED_VALUES[destx]`) instead models Intel SDM's
   normative undefined destination register, falsifying
   `VendorX86Ref.Step ⊆ ByteX86.StepNarrow`
   (`bsf_zero_narrow_refinement_counterexample` in
   `support/ByteX86Pass2Correspondence.lean`). Widening `ByteX86`'s demonic
   nondeterminism witness with `undefGpr : BitVec 64` restores universal
   per-opcode and multi-step Pass-2 simulation
   (`vendorX86Ref_step_sub_byteX86_step` and
   `vendorX86Ref_stepsN_sub_byteX86_stepsN` across all `75` opcodes; `5.61 s`
   compile, **`668 ms`** private kernel replay across `454` constants, `0`
   `sorry`, axioms `["Quot.sound", "propext"]`) while keeping
   `IceLake ⊆ VendorX86Ref ⊆ ByteX86` (`iceLake_bsf_in_vendorX86Ref`).
3. **`proofs-rs/lean-miri@c92d1d97` already contains a pure, kernel-replayable
   `IntrinsicX86` implementation (`13` unwired modules, `2,055` LOC) that lifts
   real-crate SIMD call-site coverage from `88.35%` to `99.67%`.** Auditing and
   compiling all `138` transitive `Miri` modules under Lean `v4.34.1`
   (`-DElab.async=false -Ddebug.skipKernelTC=false`) confirms **`125 / 125`
   (`100.0%`)** `.olean` SHA-256 bit-identity with `joshlf/anneal`'s
   `vendor/lean-miri/UPSTREAM_PIN.json` and zero errors across all `13` unwired
   modules (`Miri/Interpreter/IntrinsicX86.lean`,
   `Miri/Interpreter/IntrinsicX86/{Aes,Basic,Chunks,Crypto,DispatchFloat,DispatchVector,Extras,Float,Integer,Strings}.lean`,
   `Miri/Interpreter/Math/Bindings.lean`, and
   `Miri/Interpreter/IntrinsicVectorMachine.lean`, `1.21 s`–`1.98 s` each).
   Every module has `0` `unsafe`, `0` `partial`, `0` `axiom`, `0` `opaque`, `0`
   `by` tactic blocks, and `0` `set_option`, and replays at
   `(trustLevel := 0, level := .private)` in **`563 ms`** (`405` constants,
   axioms `["Classical.choice", "Quot.sound", "propext"]`). Across `1,227`
   SIMD call sites in `12` production Rust crates, wiring those `13` modules
   raises coverage from `1,084 / 1,227` (`88.35%`) to **`1,223 / 1,227`
   (`99.67%`)**, leaving only `_mm256_permutex2var_epi64`
   (`llvm.x86.avx512.vpermi2var.q.256`, `4` sites = `0.33%`), whose `.512`
   handler is already implemented in `DispatchVector.lean`.
4. **All `24` curated `core::arch::x86_64` primitives (`+ 5` shift/shuffle
   boundary companions = `29` `.o` functions) compile to byte-identical VEX/EVEX
   machine code on `rustc 1.99.1` and `rustc 1.102.0-nightly` and satisfy
   universal 3-way Pass-2 triangulation—provided `stdarch`'s MIR UB guards are
   preserved.** In `support/SimdTriangulation24.lean` (`10.31 s` compile,
   **`1,505 ms`** private kernel replay across `579` constants, `0` `sorry`), we
   prove both (a) **3 MIR-vs-VEX Undefined Behavior asymmetry counterexamples**
   showing that raw MIR `simd_shl`, `simd_bitmask`, and `simd_funnel_shl` raise
   UB on inputs (`count = 32`, mask byte `0x80`) where `rustc -O3` `vpsllvd`,
   `vpmovmskb`, and EVEX `vprolvd` execute total architectural operations, and
   (b) **29 universally quantified (`∀ a b c rsp mem`) 3-way refinement
   theorems** connecting `LeanMiri` + `stdarch`'s UB-guarding wrappers,
   `StdarchSpec`, and the `rustc -O3` `.o` machine bytes stepped in
   `VendorX86Ref` and lifted into `ByteX86.StepsN`—discharging operand
   commutation, FP-domain bitwise substitution (`vandps`/`vorps`/`vxorps`),
   relational reversal (`_mm_cmplt_epi8` $\to$ `vpcmpgtb`), and VEX `L = 0`
   upper-lane zeroing optimizations (`_mm256_slli_epi32::<40>` $\to$
   `vxorps xmm0, xmm0, xmm0` and `_mm256_permute2x128_si256::<0x81>` $\to$
   `vextractf128 xmm0, ymm0, 0x1`).

> **Prefix-Decoding Errata (`hasSegOr67` Correlated Blind Spot):** In `support/VendorX86Ref/Decode.lean`, `scanPrefixes` collapsed `{0x2E, 0x36, 0x3E, 0x26, 0x64, 0x65, 0x67}` into an unused boolean `hasSegOr67`, omitted `fsBase`/`gsBase` from `MachineState`, and omitted `0x66` (`op16`) on `d32` `01/89/8B/8D/B8/0F B1` and `d64` `50/58`. Because `support/ByteX86Pass2Correspondence.lean` shared `VendorX86Ref.decodeRef` and flat-segment addressing, `VendorX86Ref.Step ⊆ ByteX86.Step` passed while both models diverged from silicon on `84 / 318` (`26.42%`) valid Cartesian prefix vectors. Corpus package `x86-64-fs-gs-segment-sfi-escape-addr32-opsize-decoding-and-pass2-prefix-fuzzing` (`VendorX86RefV2`, `ByteX86Pass2CorrespondenceV2`) repairs all prefix classes, achieves `352 / 352` (`100.0%`) kernel-certified silicon + `intelxed` agreement, and proves `VendorX86RefV2.Step ⊆ ByteX86V2.Step` over all `(fsBase, gsBase : BitVec 64)`.

## Applicability

These findings govern the relationship among the eleven concrete subjects
recorded in `REPORT.json`:

- **Target verification architecture (`joshlf/anneal` at
  `c131b320eeeb26ef692e5afd5ec8db49ee518613` and `leanprover/lean4` `v4.34.1` at
  `5045d0056413266e57c625dcd7c365b10e377c52`):** All Lean modules and replay
  harnesses are compiled with Anneal's deterministic single-threaded kernel-check
  flags (`-j1 -M4096 -t0 -DElab.async=false -Ddebug.skipKernelTC=false`) over
  `prelude` + `Init.*` (for `VendorX86Ref`, `ByteX86Pass2Correspondence`, and
  `SimdTriangulation24`) or the pinned `vendor/lean-miri` closure, and audited
  via `importModules ... (trustLevel := 0) (plugins := #[]) (loadExts := false)
  (level := .private)` followed by `base.toKernelEnv.replay`, matching
  `trusted/audit/TrustedBoundary.lean`.
- **Upstream x86-64 reference specifications (`awslabs/s2n-bignum` at
  `d4518712d040485efe621caba1c723a07fbc549e`, `intelxed/xed` at
  `0bcb6237345c5066726dcc08b3d87928df3b5b26`, and Intel SDM `325462-087US`,
  2025 edition):** `VendorX86Ref` interprets `s2n-bignum`'s 64-bit Ring-3
  `instruction.ml` / `decode.ml` / `x86.ml` definitions augmented by `intelxed`
  prefix, length, `LOCK`, VEX, and EVEX legality tables, cross-checked against
  Intel SDM Volume 1 Section 14.5 and Volume 2A Sections 2.1–2.6.
- **Upstream Rust/MIR SIMD reference and compilers (`proofs-rs/lean-miri` at
  `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, pinned internally to
  `rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`,
  `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`, and
  `RustCrypto/block-ciphers` `aes@c1534361e7549e29a16c3505f45a04c92d26b62a`;
  compared against `rustc 1.99.1` `58cf8f9c35b355199727627d07ae34a4e2846d67`
  with `LLVM 23.1.1` and `rustc 1.102.0-nightly`
  `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` with `LLVM 23.1.5` on
  `x86_64-unknown-linux-gnu`):** Object-code triangulation applies to `extern
  "sysv64"` functions compiled with `-C opt-level=3` under explicit
  `#[target_feature(enable = ...)]` (`avx2`, `pclmulqdq`, `aes`, `avx512f,avx512vl`).
  Both compilers emit byte-identical ELF64 `.text` sequences across all `29`
  examined functions; `stdarch` source-level `llvm.x86.*` link-name counts were
  extracted from `rustc 1.99.1`'s `rust-src` `library/stdarch/crates/core_arch`
  tree.
- **Hardware and disassembler baselines (`Intel Xeon Ice Lake-SP`, Family 6
  Model 106 Stepping 6 on `Linux 7.1.6-1rodete1-amd64`, `llvm-mc 21.1.8`, and
  `GNU objdump 2.47`):** Live hardware trap and state observations apply to
  64-bit Ring-3 (`CS.L = 1, CS.D = 0`) execution on Intel AVX-512 silicon with
  standard Linux `SIGILL` (`trapno = 6`, `#UD`), `SIGSEGV` (`trapno = 13` for
  `#GP(0)` and `trapno = 14` for `#PF` page-boundary fetch traps), and `SIGTRAP`
  (`trapno = 3`, `int3`) delivery.

## Findings

### 1. Mechanical `s2n-bignum` + `intelxed` transpilation to `VendorX86Ref` and raw `s2n-bignum` gaps

Basis: normative + source + execution + derived

Parsing `awslabs/s2n-bignum@d4518712` (`x86/proofs/instruction.ml` blob
`e2d3e3c7fcf8238b862795e449819196166a42f4`, `decode.ml` blob
`4c9a45b64f10e89e6314ddd2931ccb87c0058df6`, `x86.ml` blob
`dfcd64bcccb2ff8c9c701609aa13ebc763d541e4`) yields `178` instruction constructors
and `200` `x86_*` semantic definitions with explicit HOL Light
`UNDEFINED_VALUES[...]` relational clauses (for example `x86_BSF` and `x86_BSR`
marking `AF, CF, OF, PF, SF, destx`; `x86_MUL2` marking `AF, PF, SF, ZF`;
`x86_SHL`/`x86_SHR` marking `AF, CF, OF`; `x86_TZCNT`/`x86_LZCNT` marking
`AF, OF, PF, SF`; and `x86_AND`/`x86_OR`/`x86_XOR`/`x86_TEST` marking `AF`).
Cross-checking `decode.ml` against `intelxed/xed@0bcb6237` (`25` ISA datafiles,
`1,334` distinct `ICLASS` definitions), `rustc -C opt-level=3` `.o` outputs, and
`224` Ice Lake-SP silicon vectors exposes **five structural gaps in raw
`s2n-bignum` decoding** that prevent using an unaugmented port of `decode.ml`
for general Rust/SIMD object verification:

1. **`50.0%` (`12 / 24`) rejection rate on `rustc -C opt-level=3` curated
   `core::arch::x86_64` `.o` primitives:** Raw `decode.ml` models only the
   cryptographic subset needed by `s2n-bignum`'s handwritten assembly routines.
   It rejects `12` of the `24` curated SIMD primitives emitted by `rustc 1.99.1`
   and `rustc 1.102.0-nightly`:
   - `p03_simd_and` (`vandps`), `p04_simd_or` (`vorps`), `p05_simd_xor`
     (`vxorps`) — LLVM substitutes 4-byte single-precision FP bitwise opcodes
     (`0F 54` / `0F 56` / `0F 57` with `pp = 0`) for 256-bit integer
     `_mm256_{and,or,xor}_si256`;
   - `p06_simd_eq` (`vpcmpeqb`, `decode.ml` has `VPCMPEQW` only), `p07_simd_gt`
     and `p08_simd_lt` (`vpcmpgtb`, `decode.ml` has `VPCMPGTD` only);
   - `p11_simd_funnel_shl` (EVEX `vprolvd`, `decode.ml` has 512-bit `VPROLVQ`
     only), `p13_simd_saturating_sub` (`vpsubusb`), `p16_simd_shuffle`
     (`vperm2f128`, `decode.ml` has `0F3A 38`/`0F3A 46` `VPERM2I128` but omits
     `0F3A 06` `VPERM2F128`), `p18_aesni` (`vaesenc`, `decode.ml:1174` decodes
     legacy SSE `66 0F 38 DC` `AESENC` only, omitting VEX `VAESENC`),
     `p20_psadbw` (`vpsadbw`), and `p21_vperm` (`vpermps`, `0F38 16`, `decode.ml`
     has `0F38 36` `VPERMD` only).
   In addition, raw `decode.ml` omits BMI2 `SHRX`/`SHLX`/`SARX` (`0F38 F7`),
   `BZHI` (`0F38 F5`), `PDEP` (`0F38 F5` `pp = 3`), and `XCHG`.
2. **Missing 15-byte instruction-length `#GP(0)` cap (`decode.ml:45`):**
   `read_prefixes` recursively peels `0x66` operand-size prefixes without any
   total-length counter, accepting 16-byte `66 × 15 + 90` (`NOP`) and
   `66 × 13 + 48 01 f0` (`ADD`) streams that raise `#GP(0)` (`SIGSEGV`,
   `trapno = 13`) on x86-64 hardware (Intel SDM Vol. 2A Section 2.1.1).
3. **Single-pass REX parsing after legacy prefixes (`decode.ml:76-101`):**
   `decode` invokes `read_prefixes` once and then `read_REX_prefix` once. On
   x86-64 silicon, a REX byte (`0x40..0x4F`) is effective **only** when it
   immediately precedes the primary opcode or `0x0F` escape; any intervening
   legacy prefix (`0x66`, `0xF2`, `0xF3`, segment, `0x67`) nullifies an earlier
   REX byte (`41 66 90` executes a 3-byte `NOP` rather than `xchg r8w, ax`), and
   consecutive REX bytes obey last-wins (`41 40 90` executes `NOP`, whereas
   `40 41 90` swaps `rax` and `r8`).
4. **Blanket `LOCK` (`0xF0`) rejection (`decode.ml:90`):** `decode.ml` rejects
   every `0xF0` prefix unconditionally, excluding Rust `AtomicU64` read-modify-write
   lowerings (`lock add/sub/and/or/xor/inc/dec/neg/not [mem]`, `lock xadd [mem]`,
   `lock cmpxchg [mem]`, and implicit-lock `xchg [mem], reg`) while failing to
   distinguish memory-destination `LOCK` (valid) from register-destination or
   load-only `LOCK` (`#UD`, `trapno = 6`).
5. **Spurious `L = 1` restriction on `VPMOVMSKB` (`decode.ml:1334`):**
   `decode_vex` guards `0xD7` with `l = T` (256-bit only), falsely rejecting
   valid 128-bit `c5 f9 d7 c0` (`vpmovmskb eax, xmm0`, `L = 0`).

`support/transpile_s2n_xed_to_lean.py` closes all five gaps mechanically via an
`intelxed` legality and opcode overlay (`88` provenance-tagged family entries
expanding to `75` architectural opcodes across `VendorX86Ref/{Types,Decode,SemanticsScalar,SemanticsSimd,Machine}.lean`), raising silicon vector agreement from
`177 / 224` (`79.02%`) to **`224 / 224` (`100.0%`)** and curated `core::arch`
`.o` coverage from `12 / 24` (`50.0%`) to **`24 / 24` (`100.0%`)**.

Two Lean `v4.34.1` kernel-engineering rules proved essential during transpiler
construction:

- **Eliminating silent `*._unsafe_rec` (`isPartial`) helpers via `Nat.rec`:**
  When Lean `v4.34.1` compiles an equation-compiler recursive `def` (even a
  structurally terminating `| 0 => ... | k + 1 => ...` loop), its LCNF code
  generator inserts a private `foo._unsafe_rec` entry (`ConstantInfo.isPartial =
  true`) into `ModuleData.constants` (`data.constants`). In Anneal's
  `trusted/audit/TrustedBoundary.lean`, `.vendorMiri` explicitly filters out
  `ci.isPartial` before `Kernel.Environment.replay` (`L2143, 2164`), whereas
  repository-module validation (`collectRepoModuleConstants` ->
  `validateRepoConstant` -> `ensureReplayableConstant`, `L1119, 1246`) rejects
  every `isPartial` constant fail-closed. Emitting all bounded fuel loops
  (`scanPrefixes`, `ctzLoop`, `clzLoop`, `popcntLoop`, `pdepLoop`, `pextLoop`,
  `pmovmskb128Loop`, `pmovmskb256Loop`, `ternlogDwordLoop`, `clmulLoop`,
  `execStepsN`, and `miriBitmaskLoop`) directly via the kernel eliminator
  `Nat.rec` remains 100% computable, preserves exact definitional unfolding on
  `0` and `k + 1`, and reduces `partial_consts` at `(level := .private)` from
  `12` to **`0`** across all 7 staged modules.
- **2-level 16x16 `match` for `aesSbox` to avoid call-by-name `zeta` blowup:**
  In Lean's kernel WHNF reducer, `let`-bound subterms referenced multiple times
  are expanded call-by-name (`zeta`), causing an algebraic $x^{254}$ GF($2^8$)
  inversion chain inside `aesMixCol` to exceed default `maxRecDepth = 512` on
  concrete FIPS-197 vectors. Structuring `aesSbox` as a 2-level `16 × 16` `match`
  on `b.toNat / 16` and `b.toNat % 16` forces call-by-value WHNF reduction on
  the C++ `Nat` scrutinee in depth `2`, enabling `rfl` verification of all `224`
  silicon vectors with zero `set_option` overrides.

| Module (`support/`) | Source LOC / Bytes | Cold Compile (`ms`) | Peak RSS (`kB`) | `.olean` (`B`) | Kernel Consts | Private Replay (`ms`) | Axioms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| `VendorX86Ref/Types.lean` | `375` / `15,035` | `4,258.73` | `386,696` | `6,670,888` | `1,577` | *(in `547`)* | `Quot.sound, propext` |
| `VendorX86Ref/Decode.lean` | `723` / `36,641` | `1,943.14` | `326,464` | `1,853,864` | `115` | *(in `547`)* | `Quot.sound, propext` |
| `VendorX86Ref/SemanticsScalar.lean` | `527` / `22,253` | `1,112.03` | `305,320` | `1,204,792` | `37` | *(in `547`)* | `Quot.sound, propext` |
| `VendorX86Ref/SemanticsSimd.lean` | `417` / `25,453` | `1,359.98` | `315,472` | `1,548,360` | `82` | *(in `547`)* | `Quot.sound, propext` |
| `VendorX86Ref/Machine.lean` | `76` / `3,240` | `357.42` | `291,176` | `141,552` | `20` | **`547`** (`1,831` $\Delta$) | `Quot.sound, propext` |
| `ByteX86Pass2Correspondence.lean` | `1,191` / `57,809` | `5,609.91` | `394,564` | `6,231,776` | `454` | **`668`** (`454` $\Delta$) | `Quot.sound, propext` |
| `SimdTriangulation24.lean` | `1,101` / `64,928` | `10,308.58` | `447,872` | `9,261,048` | `579` | **`1,505`** (`579` $\Delta$) | `Classical.choice, Quot.sound, propext` |
| **Total (`7` staged `.lean` modules)** | **`4,410` / `225,359`** | **`24,949.79`** | **`447,872` max** | **`26,912,280`** | **`2,864`** | **`2,720`** | **`0` `sorry`, `0` `partial`** |

### 2. Live 224-vector Ice Lake-SP silicon cross-check and Pass-2 `ByteX86` correspondence

Basis: normative + source + execution + derived

`support/probe_silicon_220_x86_vectors.py` executes `224` controlled Ring-3
vectors on an Intel Xeon Ice Lake-SP processor using a two-page `mmap` arena
(`PROT_READ | PROT_WRITE | PROT_EXEC` page followed immediately by a `PROT_NONE`
guard page, sweeping `start = page_end - L` for `L = 1..17` under `SA_SIGINFO`
handlers for `SIGILL`, `SIGSEGV`, `SIGTRAP`, and `SIGBUS`):

- **Length and prefix interactions (`32` vectors):** Confirms `#GP(0)`
  (`trapno = 13`) at `>= 16` total bytes (`66×15 + 90`, `2e×15 + 90`,
  `f3×15 + 90`, `66×13 + 48 01 f0`), exact `15`-byte acceptance (`66×14 + 90`,
  `66×12 + 48 01 f0`), REX nullification by trailing `0x66`/`0xF2`/`0xF3`/`0x2E`/`0x67`
  (`41 66 90` len `3`, `rax` unchanged), consecutive REX last-wins (`41 40 90` vs
  `40 41 90`), and ModR/M `mod=00 rm=101` RIP-relative + SIB `base=101` `disp32`
  lengths.
- **`LOCK` and VEX/EVEX `#UD` legality (`32` vectors):** Confirms `#UD`
  (`trapno = 6`) on `lock nop`, `lock add rax, rsi`, `lock mov rax, [rdi]`,
  `lock mov [rdi], rax`, `lock lea`, `lock vmovdqu`, `{66, f2, f3, 48, f0} + VEX`,
  `vzeroupper` with `vvvv != 1111` (`c5 f0 77`) or `L = 1` (`c5 fc 77`),
  `vpclmulqdq` with `L = 1`, `vaesenc` with `L = 1`, `vpermq` with `L = 0`, and
  EVEX `P[3:2] != 00` — while confirming that **segment (`2e c5 f8 77`) and
  address-size (`67 c5 f8 77`) prefixes before VEX are architecturally valid**
  (executing `vzeroupper` in `4` bytes with zero fault, matching Intel SDM Vol.
  2A Section 2.3.5). Across the `24` decode-legality trap specimens, both
  `llvm-mc 21.1.8` and `objdump 2.47` exit `0` with disassembly text on
  **`18 / 24` (`75.0%`)** (`18 / 18 = 100.0%` of prefix/length/LOCK traps,
  rejecting only the `6` internal VEX/EVEX bitfield violations).
- **Scalar GP, BMI1/2, ADX, `CMOVcc`, and VEX/EVEX SIMD (`160` vectors: `96`
  scalar + `64` SIMD):** Verifies exact `RAX`/`RCX`/`RDX`, `[RDI]`/`[RDI+8]`
  memory words, `6`-flag `RFLAGS` masks (`CF, PF, AF, ZF, SF, OF`), VEX `L = 0`
  upper-128-bit `YMM` zeroing (`vmovdqa xmm0, xmm1` zeroes `YMM0[255:128]`),
  `ADCX`/`ADOX` independent `CF`/`OF` carry chains, `MULX` `dstHi == dstLo`
  high-half tie-breaking, `VPSHUFB` bit-7 lane zeroing without cross-128-bit-lane
  bleed, `VPMADDUBSW` signed `i16` saturation (`0xFF * -128 + 0xFF * -128 ->
  -32768 = 0x8000`), `VPCLMULQDQ`, NIST FIPS-197 cipher round 1 `VAESENC`, EVEX
  `VPROLVD`, and EVEX `VPTERNLOGD`.

Proving Pass-2 correspondence between `VendorX86Ref` and `ByteX86` in
`support/ByteX86Pass2Correspondence.lean` exposed a **reverse soundness bug**
where `s2n-bignum` caught hardware overfitting in `ByteX86`:

- On Ice Lake-SP silicon, `bsf rax, rcx` (`48 0f bc c1`, vector `bsf64_zero`)
  with `rax = 0xCAFE_BABE_DEAD_BEEF` and `rcx = 0` leaves `rax` unchanged
  (`0xCAFE_BABE_DEAD_BEEF`) with `ZF = 1`.
- If `ByteX86` hardcodes `dst := oldDst` on `src = 0` (`ByteX86.StepNarrow`),
  a program verified under `ByteX86.StepNarrow` may rely on `rax` retaining its
  prior value when `rcx = 0`—which Intel SDM Vol. 2A ("BSF—Bit Scan Forward":
  *"If the content of the source operand is 0, the content of the destination
  operand is undefined"*) and `s2n-bignum` (`x86/proofs/x86.ml:902`:
  `val_of_option(bitscan ... (if x = word 0 then UNDEFINED_VALUES[destx] ...))`)
  explicitly forbid!
- `bsf_zero_narrow_refinement_counterexample` proves inside Lean `v4.34.1` that
  `VendorX86Ref.Step` with `oracle.gpr = 0x1337#64` steps `s0` (`rax =
  0xDEAD_BEEF_CAFE_BABE#64, rcx = 0`) on `48 0f bc c1` to `rax = 0x1337#64`,
  which no `nd : UndefFlags` in `ByteX86.StepNarrow` can simulate (`¬
  ByteX86.StepNarrow bsfRaxRcxCode (toByteState s0) (toByteState s')`).
- Widening `ByteX86.DemonicChoice` with `undefGpr : BitVec 64` (used on `BSF`
  and `BSR` when `src = 0`) yields universal single-step and `N`-step Pass-2
  refinement across all `75` opcodes (`vendorX86Ref_step_sub_byteX86_step` and
  `vendorX86Ref_stepsN_sub_byteX86_stepsN`) while preserving
  `iceLake_bsf_in_vendorX86Ref` (`∃ oracle, VendorX86Ref.stepWithOracle ... =
  s_iceLake`).

### 3. Source, coverage, and kernel-replay audit of `vendor/lean-miri` `IntrinsicSimd` and `IntrinsicX86`

Basis: source + execution + derived

`joshlf/anneal@c131b320` vendors `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`,
whose `UPSTREAM_PIN.json` currently locks a `160`-module `ExecutionMachine`
closure. That `160`-module closure includes `Miri.Interpreter.IntrinsicSimd`
(`531` LOC), `Miri.Interpreter.IntrinsicCrypto` (`64` LOC), and
`Miri.Interpreter.IntrinsicArchitecture` (`308` LOC, where `IntrinsicArchitecture.eval`
currently stubs `"llvm.x86."` prefixes to `.unsupported`), while **`13`
additional SIMD/x86 modules (`2,055` LOC) are already present in the vendored
directory tree** (`vendor/lean-miri/Miri/Interpreter/`) with an alternate
machine wiring in `Miri/Interpreter/IntrinsicVectorMachine.lean` (`bindX86`,
which routes `"llvm.x86."` intrinsics through `Miri.Interpreter.IntrinsicX86.eval`
before falling back to `IntrinsicArchitecture.eval`):

| `vendor/lean-miri` Module | In `160`-Mod Pin? | LOC / Bytes | Cold Compile (`ms`) | `.olean` (`B`) | Kernel Consts | Role & Audited Coverage |
| --- | :---: | ---: | ---: | ---: | ---: | --- |
| `Miri.Interpreter.IntrinsicSimd` | Yes | `531` / `34,477` | `5,064.25` | `3,838,840` | `165` | `73` portable `simd_*` ops (`elementToBool`, `shift`, `bitmask`, `funnelShift`, `shuffle`, reductions, gather/scatter, masked load/store) |
| `Miri.Interpreter.IntrinsicCrypto` | Yes | `64` / `2,785` | `1,324.67` | `306,792` | `40` | Shared `carrylessMul` (`pclmulqdq`), `sha256msg1/2`, `sha256rnds2` |
| `Miri.Interpreter.IntrinsicArchitecture` | Yes | `308` / `17,724` | `2,164.36` | `1,650,464` | `79` | Generic `llvm.ctpop.v*`, `llvm.prefetch.p0`, Arm NEON/SVE; returns `.unsupported` on `"llvm.x86."` unless `bindX86` is wired |
| `Miri.Interpreter.Math.Bindings` | No | `52` / `2,825` | `1,213.72` | `216,040` | `7` | Exact IEEE-754 `apfloat` rounding/sqrt/fma bindings for `IntrinsicX86.Float` |
| `Miri.Interpreter.IntrinsicX86.Basic` | No | `120` / `7,142` | `1,740.71` | `745,856` | `93` | Vector lane read/write, `movemask`, `ptest` (`testz`/`testc`/`testnzc`), pack/saturate helpers |
| `Miri.Interpreter.IntrinsicX86.Chunks` | No | `125` / `7,474` | `1,874.66` | `810,688` | `10` | `128`-bit chunked lane combinators (`vpmaddwd`, `vpmaddubsw`, `vpsadbw`, `mpsadbw`) for `256`/`512`-bit AVX2/AVX-512 |
| `Miri.Interpreter.IntrinsicX86.Integer` | No | `195` / `9,720` | `1,977.45` | `958,760` | `43` | Saturating/clamping `shiftScalar`/`shiftVector`, `pshufb` bit-7 zeroing, `pavg`, `psign`, `pmulhrsw`, `pternlog`, `vpdpbusd` |
| `Miri.Interpreter.IntrinsicX86.Float` | No | `156` / `8,209` | `1,665.06` | `813,584` | `49` | SSE/AVX FP min/max, `cmp.ps/pd`, `comi`/`ucomi`, `cvt*`, deterministic x86 quiet-NaN canonicalization |
| `Miri.Interpreter.IntrinsicX86.Aes` | No | `391` / `11,364` | `1,632.14` | `431,456` | `22` | Materialized `Vector UInt32 8` Boyar–Peralta boolean S-box, `ShiftRows`, `MixColumns`, `InvMixColumns` (`aes 0.9.3` port) |
| `Miri.Interpreter.IntrinsicX86.Crypto` | No | `196` / `11,488` | `1,926.20` | `1,404,528` | `16` | `aesenc`/`aesenclast`/`aesdec`/`aesdeclast`/`aesimc` (`128`/`256`/`512`-bit VAES), `aeskeygenassist`, `pclmulqdq`, `gf2p8affine*`, `crc32`, `sha256*` |
| `Miri.Interpreter.IntrinsicX86.Strings` | No | `152` / `7,750` | `1,719.25` | `844,600` | `13` | SSE4.2 `pcmpestri*` and `pcmpistri*` string comparison state machines |
| `Miri.Interpreter.IntrinsicX86.Extras` | No | `176` / `9,178` | `1,816.03` | `1,022,856` | `10` | `addcarry`/`subborrow`, BMI1/2 `bextr`/`bzhi`/`pdep`/`pext`, `vpermd`/`vpermps`/`vpermi2var`, `gather` |
| `Miri.Interpreter.IntrinsicX86.DispatchFloat` | No | `75` / `5,278` | `1,466.33` | `790,464` | `4` | `77` SSE/SSE2/SSE4.1/AVX FP `llvm.x86.*` string dispatchers |
| `Miri.Interpreter.IntrinsicX86.DispatchVector` | No | `196` / `10,101` | `1,671.57` | `1,253,584` | `108` | `181` integer/crypto/BMI/AVX2/AVX-512 `llvm.x86.*` string dispatchers (`258` `llvm.x86.*` total) |
| `Miri.Interpreter.IntrinsicX86` | No | `84` / `4,572` | `1,412.38` | `521,768` | `7` | Top-level `"llvm.x86."` prefix stripper and `DispatchFloat` + `DispatchVector` router |
| `Miri.Interpreter.IntrinsicVectorMachine` | No | `137` / `8,510` | `1,360.50` | `429,520` | `17` | `bindX86` machine-hook composer wiring `IntrinsicX86.eval` ahead of `ExecutionMachine` |

Key findings from `support/probe_lean_miri_simd_x86_audit.py`
(`support/probe_lean_miri_simd_x86_audit_results.json`):

- **100% `TrustedBoundary` compatibility and sub-second kernel replay:** Across
  all `138` transitive modules needed by `IntrinsicVectorMachine` (`294.59 s`
  cold sequential build), all `125` modules shared with `UPSTREAM_PIN.json`
  produce **bit-identical `.olean` SHA-256 digests (`125 / 125`)**, and the `13`
  newly compiled modules contain `0` `unsafe`, `0` `partial`, `0` `axiom`, `0`
  `opaque`, `0` `by` tactics, `0` `@[extern]`/`@[implemented_by]`/`@[csimp]`,
  and `0` references to `sorryAx` or `Lean.ofReduceBool`. Replaying the `284`
  constants of `IntrinsicSimd + IntrinsicCrypto + IntrinsicArchitecture` takes
  **`211 ms`** (axioms `["Quot.sound", "propext"]`); replaying the `405`
  constants of `IntrinsicX86* + Math.Bindings + IntrinsicVectorMachine` (plus `6`
  direct edge-case theorems) takes **`563 ms`** (`VmHWM = 4.20 GiB`, axioms
  `["Classical.choice", "Quot.sound", "propext"]`, where `Classical.choice`
  enters solely through `Float.lean` / `Math.Bindings` IEEE-754 `apfloat` helpers).
- **`99.67%` (`1,223 / 1,227`) production SIMD crate call-site coverage:**
  Mapping `rustc 1.99.1`'s `core::arch::x86_64` (`6,004` functions referencing
  `951` distinct `llvm.x86.*` link names, of which `IntrinsicX86` implements
  `197 / 951 = 20.72%` concentrated in integer/crypto/SSE-AVX2 hot paths) onto
  the `1,227` `core::arch` call sites across `12` pure-Rust crates (`zlib-rs`,
  `memchr`, `simdutf8`, `crc32fast`, `simd-adler32`, `blake3`, `aho-corasick`,
  `bytecount`, `hashbrown`, `sha2`, `chacha20`, `aes`) shows:
  1. `1,084 / 1,227` (`88.35%`) lower purely to portable `#[rustc_intrinsic]`
     `simd_*` calls already handled by `IntrinsicSimd.lean`;
  2. Wiring the `13` already-vendored `IntrinsicX86*` modules adds `139` sites,
     reaching **`1,223 / 1,227` (`99.67%`)** (`24 / 24 = 100%` of the curated
     24-primitive basis);
  3. The **sole uncovered intrinsic** across all `1,227` sites is
     `_mm256_permutex2var_epi64` (`4` sites = `0.33%`), which links
     `llvm.x86.avx512.vpermi2var.q.256`. `Extras.lean` and `DispatchVector.lean`
     already implement `llvm.x86.avx512.vpermi2var.q.512` (`L730`); adding the
     `.128` and `.256` AVX-512VL string cases in `DispatchVector.lean` reaches
     **`1,227 / 1,227` (`100.00%`)**.
- **Kernel-checked `lean-miri` edge-case semantics (`EdgeCaseTheorems`):** Six
  theorems compiled directly against `Miri.Interpreter.*` verify:
  1. `aes_round_fips197_round1` and `aes_invMixColumns_roundtrip`: `Aes.round
     false` (`Aes.lean:384-390`) matches NIST FIPS-197 Appendix B cipher round 1
     (`0x49506a0243ea5b6b2b359f68f27f9ca4`), and `Aes.invMixColumns` inverts the
     forward MixColumns transformation cleanly;
  2. `mir_simd_shl_ub_at_width_32`: `IntegerOps.binary .ShlUnchecked` (`invoked`
     by `IntrinsicSimd.shift`, `IntrinsicSimd.lean:165-179`) returns `.ub` when
     lane shift count `== 32` on `U32`;
  3. `x86_pslld_saturates_to_zero_at_32` and `x86_psrad_clamps_sign_bit_at_32`:
     `IntrinsicX86.shiftScalar` (`Integer.lean:17-37`) returns `0` on logical
     shifts `>= 32` and replicates the sign bit (`0xFFFFFFFF` on `0x80000000`) on
     arithmetic right shifts `>= 32` without UB;
  4. `carryless64_crc_fold_specimen`: `IntrinsicCrypto.carrylessMul` reproduces
     polynomial multiplication over $\text{GF}(2)[x]$.

### 4. Three-way Pass-2 triangulation across all 24 curated `core::arch::x86_64` primitives

Basis: normative + source + execution + derived

`support/probe_24_core_arch_primitives_obj.py` compiles all `24` curated
`core::arch::x86_64` primitives (`16` portable `simd_*` operations + `8`
`llvm.x86.*` families) plus `5` shift/shuffle boundary companions (`29` `extern
"sysv64"` functions total) on both `rustc 1.99.1` (`LLVM 23.1.1`) and `rustc
1.102.0-nightly` (`LLVM 23.1.5`) at `-C opt-level=3`. All **`29 / 29` (`100.0%`)**
functions compile to **byte-identical ELF64 `.text` machine code** across both
toolchains and pass differential execution on live Ice Lake-SP silicon.

In `support/SimdTriangulation24.lean`, we prove **three MIR-vs-VEX Undefined
Behavior asymmetry counterexample theorems** demonstrating why a verifier must
never rewrite raw MIR `simd_*` intrinsics directly to x86 VEX/EVEX semantics
without checking `stdarch`'s wrapper guards:

1. **`unguarded_simd_shl_ub_vs_vpsllvd_zero`:** On `u32x8` with lane-0 shift
   count `32`, raw MIR `simd_shl` (`miriSimdShlDwords`) returns
   `.error (.shiftOverflow 32)`, whereas `p14bBytes` (`vpsllvd ymm0, ymm0, ymm1;
   ret`) halts cleanly with `0#256`. `stdarch`'s `_mm256_slli_epi32::<IMM8>`
   avoids MIR UB by guarding `if IMM8 < 32 { simd_shl(...) } else { splat(0) }`,
   while `_mm256_sllv_epi32` calls `llvm.x86.avx2.psllv.d.256` directly rather
   than `simd_shl`.
2. **`unguarded_simd_bitmask_ub_vs_vpmovmskb_msb`:** On `i8x32` with lane-0 byte
   `0x80` (`∉ {0x00, 0xFF}`), raw MIR `simd_bitmask` (`IntrinsicSimd.elementToBool`,
   `L75-79`) raises `.error (.nonBoolMask 128)`, whereas `p09Bytes` (`vpmovmskb
   eax, ymm0; vzeroupper; ret`) extracts `rax = 1#64`. `stdarch`'s
   `_mm256_movemask_epi8(a)` normalizes arbitrary bytes via `simd_lt(a,
   splat(0))` (`0xFF` if negative else `0x00`) before calling `simd_bitmask`,
   which LLVM then fuses back into a single `vpmovmskb`!
3. **`unguarded_simd_funnel_shl_ub_vs_vprolvd_mod32`:** On `u32x8` with lane-0
   rotate count `32`, raw MIR `simd_funnel_shl` (`L495-524`) raises
   `.error (.funnelShiftOverflow 32)`, whereas `p11Bytes` (EVEX `vprolvd ymm0,
   ymm0, ymm1; ret`) rotates modulo `32` cleanly. `stdarch`'s
   `_mm256_rolv_epi32(a, b)` pre-masks `simd_and(b, splat(31))` before
   `simd_funnel_shl(a, a, masked)`, which LLVM fuses into a single `vprolvd`!

With `stdarch`'s exact wrapper lowerings modeled in `evalMiri_*`, all **`29`
universally quantified (`∀ a b c rsp mem`) 3-way triangulation theorems**
(`TriangulatedYmm` / `TriangulatedXmm` / `TriangulatedGpr`, bundling
`evalMiri = .ok spec ∧ sFinal.halted = true ∧ sFinal.fault = none ∧ sFinal.ret =
spec ∧ ByteX86.StepsN code steps (toByteState s0) (toByteState sFinal)`) hold in
`support/SimdTriangulation24.lean`:

| ID | `core::arch::x86_64` API | MIR Intrinsic / Wrapper | Exact `rustc -O3` `.o` Bytes (`1.99.1` == `1.102.0`) | Decoded x86-64 Sequence & Backend Optimization | Theorem in `SimdTriangulation24.lean` |
| --- | --- | --- | --- | --- | --- |
| `p01` | `_mm256_add_epi8` | `simd_add` | `c5 f5 fc c0 c3` | `vpaddb ymm0,ymm1,ymm0; ret` *(commutes `a,b`)* | `triangulate_p01_simd_add` |
| `p02` | `_mm256_sub_epi8` | `simd_sub` | `c5 fd f8 c1 c3` | `vpsubb ymm0,ymm0,ymm1; ret` | `triangulate_p02_simd_sub` |
| `p03` | `_mm256_and_si256` | `simd_and` | `c5 f4 54 c0 c3` | `vandps ymm0,ymm1,ymm0; ret` *(FP domain + commute)* | `triangulate_p03_simd_and` |
| `p04` | `_mm256_or_si256` | `simd_or` | `c5 f4 56 c0 c3` | `vorps ymm0,ymm1,ymm0; ret` *(FP domain + commute)* | `triangulate_p04_simd_or` |
| `p05` | `_mm256_xor_si256` | `simd_xor` | `c5 f4 57 c0 c3` | `vxorps ymm0,ymm1,ymm0; ret` *(FP domain + commute)* | `triangulate_p05_simd_xor` |
| `p06` | `_mm256_cmpeq_epi8` | `simd_eq` | `c5 fd 74 c1 c3` | `vpcmpeqb ymm0,ymm0,ymm1; ret` | `triangulate_p06_simd_eq` |
| `p07` | `_mm256_cmpgt_epi8` | `simd_gt` | `c5 fd 64 c1 c3` | `vpcmpgtb ymm0,ymm0,ymm1; ret` | `triangulate_p07_simd_gt` |
| `p08` | `_mm_cmplt_epi8` | `simd_lt` | `c5 f1 64 c0 c3` | `vpcmpgtb xmm0,xmm1,xmm0; ret` *(swaps `a,b` + VEX `L=0` zero)* | `triangulate_p08_simd_lt` |
| `p09` | `_mm256_movemask_epi8` | `simd_lt(a,0)` + `simd_bitmask` | `c5 fd d7 c0 c5 f8 77 c3` | `vpmovmskb eax,ymm0; vzeroupper; ret` *(fuses guard)* | `triangulate_p09_simd_bitmask` |
| `p10` | `_mm_extract_epi64::<1>` | `simd_extract` | `c4 e3 f9 16 c0 01 c3` | `vpextrq rax,xmm0,0x1; ret` | `triangulate_p10_simd_extract` |
| `p11` | `_mm256_rolv_epi32` | `simd_and(b,31)` + `simd_funnel_shl` | `62 f2 7d 28 15 c1 c3` | `vprolvd ymm0,ymm0,ymm1; ret` *(EVEX, fuses `& 31`)* | `triangulate_p11_simd_funnel_shl` |
| `p12` | `_mm256_testz_si256` | `simd_and` + `== 0` (`ptestz`) | `31 c0 c4 e2 7d 17 c8 0f 94 c0 c5 f8 77 c3` | `xor eax,eax; vptest ymm1,ymm0; sete al; vzeroupper; ret` | `triangulate_p12_simd_reduce_or` |
| `p13` | `_mm256_subs_epu8` | `simd_saturating_sub` | `c5 fd d8 c1 c3` | `vpsubusb ymm0,ymm0,ymm1; ret` | `triangulate_p13_simd_saturating_sub` |
| `p14` | `_mm256_slli_epi32::<7>` | `if 7<32 { simd_shl }` | `c5 fd 72 f0 07 c3` | `vpslld ymm0,ymm0,0x7; ret` | `triangulate_p14_simd_shl` |
| `p14b` | `_mm256_sllv_epi32` | `avx2.psllv.d.256` | `c4 e2 7d 47 c1 c3` | `vpsllvd ymm0,ymm0,ymm1; ret` | `triangulate_p14b_simd_shl_var` |
| `p14c` | `_mm256_slli_epi32::<40>` | `else { splat(0) }` | `c5 f8 57 c0 c3` | `vxorps xmm0,xmm0,xmm0; ret` *(128b VEX `L=0` zeroes all 256b!)* | `triangulate_p14c_simd_shl_oob40` |
| `p15` | `_mm256_srli_epi32::<7>` | `if 7<32 { simd_shr }` | `c5 fd 72 d0 07 c3` | `vpsrld ymm0,ymm0,0x7; ret` | `triangulate_p15_simd_shr` |
| `p15b` | `_mm256_srai_epi32::<7>` | `simd_shr` (signed) | `c5 fd 72 e0 07 c3` | `vpsrad ymm0,ymm0,0x7; ret` | `triangulate_p15b_simd_sar` |
| `p15c` | `_mm256_srai_epi32::<40>` | `clamp(40,31)` + `simd_shr` | `c5 fd 72 e0 1f c3` | `vpsrad ymm0,ymm0,0x1f; ret` *(folds `40 -> 31`)* | `triangulate_p15c_simd_sar_oob40` |
| `p16` | `_mm256_permute2x128_si256::<0x21>` | `simd_shuffle` | `c4 e3 7d 06 c1 21 c3` | `vperm2f128 ymm0,ymm0,ymm1,0x21; ret` | `triangulate_p16_simd_shuffle` |
| `p16b` | `_mm256_permute2x128_si256::<0x81>` | `simd_shuffle` (bit-3 zero) | `c4 e3 7d 19 c0 01 c3` | `vextractf128 xmm0,ymm0,0x1; ret` *(VEX `L=0` zeroes upper 128b!)* | `triangulate_p16b_simd_shuffle_zero` |
| `p17` | `_mm_clmulepi64_si128::<0x10>` | `llvm.x86.pclmulqdq` | `c4 e3 79 44 c1 10 c3` | `vpclmulqdq xmm0,xmm0,xmm1,0x10; ret` | `triangulate_p17_pclmulqdq` |
| `p18` | `_mm_aesenc_si128` | `llvm.x86.aesni.aesenc` | `c4 e2 79 dc c1 c3` | `vaesenc xmm0,xmm0,xmm1; ret` | `triangulate_p18_aesni` |
| `p19` | `_mm256_shuffle_epi8` | `llvm.x86.avx2.pshuf.b` | `c4 e2 7d 00 c1 c3` | `vpshufb ymm0,ymm0,ymm1; ret` | `triangulate_p19_pshufb` |
| `p20` | `_mm256_sad_epu8` | `llvm.x86.avx2.psad.bw` | `c5 fd f6 c1 c3` | `vpsadbw ymm0,ymm0,ymm1; ret` | `triangulate_p20_psadbw` |
| `p21` | `_mm256_permutevar8x32_epi32` | `llvm.x86.avx2.permd` | `c4 e2 75 16 c0 c3` | `vpermps ymm0,ymm1,ymm0; ret` *(`idx` in `vvvv`, `a` in `rm`)* | `triangulate_p21_vperm` |
| `p22` | `_mm256_ternarylogic_epi32::<0x96>` | `avx512.pternlog.d.256` | `62 f3 75 28 25 c2 96 c3` | `vpternlogd ymm0,ymm1,ymm2,0x96; ret` *(EVEX 3-source)* | `triangulate_p22_pternlog` |
| `p23` | `_mm256_madd_epi16` | `llvm.x86.avx2.pmadd.wd` | `c5 fd f5 c1 c3` | `vpmaddwd ymm0,ymm0,ymm1; ret` | `triangulate_p23_pmaddwd` |
| `p24` | `_mm256_maddubs_epi16` | `avx2.pmadd.ub.sw` | `c4 e2 7d 04 c1 c3` | `vpmaddubsw ymm0,ymm0,ymm1; ret` | `triangulate_p24_pmaddubsw` |

### 5. Architectural integration path for Anneal Pass-2 correspondence

Basis: source + derived

Together, these artifacts provide a concrete, low-TCB two-track integration path
for `joshlf/anneal`:

1. **MIR-level `core::arch` SIMD verification (`vendor/lean-miri`):** Add the
   `13` already-vendored `Miri.Interpreter.IntrinsicX86*`, `Math.Bindings`, and
   `IntrinsicVectorMachine` modules (`405` constants, `563 ms` replay) to
   `vendor/lean-miri/UPSTREAM_PIN.json` and add a 2-line `.128`/`.256` alias for
   `vpermi2var.q` in `DispatchVector.lean` to reach `100.00%` (`1,227 / 1,227`)
   pure-Rust SIMD call-site coverage without expanding Anneal's Pass-1 `Trusted`
   MIR AST beyond intrinsic call dispatch.
2. **Object-level `x86_64` Pass-2 correspondence (`VendorX86Ref` $\leftrightarrow$
   `ByteX86`):** Generate `VendorX86Ref` deterministically from pinned
   `s2n-bignum` + `intelxed` sources using `Nat.rec` loops (`0` `isPartial`
   helpers, `547 ms` replay), ensure `ByteX86`'s demonic nondeterminism witness
   includes `undefGpr : BitVec 64` alongside `undefFlags` (`BSF`/`BSR` on zero),
   and require every `trusted/lean` x86-64 opcode addition to discharge both a
   live silicon page-boundary/state vector and a `VendorX86Ref.Step ⊆
   ByteX86.Step` case. *(Errata: when both models share a decoder helper such as `scanPrefixes`, Pass-2 forward simulation alone cannot catch a shared prefix projection bug (`hasSegOr67`); pair Pass-2 simulation with a Cartesian `(prefix-ordering × opcode-class)` silicon + `intelxed` differential sweep as mechanized in `VendorX86RefV2` / `ByteX86Pass2CorrespondenceV2` under corpus package `x86-64-fs-gs-segment-sfi-escape-addr32-opsize-decoding-and-pass2-prefix-fuzzing`.)*

## Boundaries

- **512-bit `ZMM` and masked EVEX `{k1}{z}` predicates (`not examined` in
  `VendorX86Ref`):** `VendorX86Ref` models `16 × 256`-bit `YMM` registers and
  unmasked (`aaa = 0, z = 0`) EVEX `VL = 128`/`256` encodings (`VPROLVD`,
  `VPTERNLOGD`), rejecting `aaa != 0` or `z != 0` fail-closed with
  `.fault .udEvexField`. Full `32 × 512`-bit `ZMM` and `K0`–`K7` opmask register
  files were **not examined** in `VendorX86Ref` (though `vendor/lean-miri`'s
  `IntrinsicX86` already models 512-bit vector intrinsics at the MIR level).
- **Floating-point SIMD arithmetic and `MXCSR` exception/rounding flags (`not
  examined` in `VendorX86Ref`):** While `VendorX86Ref` models FP-domain bitwise
  instructions (`VANDPS`, `VORPS`, `VXORPS`) and `VPERM2F128`/`VEXTRACTF128`/`VPERMPS`
  whose behavior is pure bit-level data movement/logic independent of `MXCSR`,
  IEEE-754 arithmetic instructions (`VADDPS`, `VMULPD`, `VCVT*`) and `MXCSR`
  rounding/denormal modes were **not examined** in `VendorX86Ref` (at the MIR
  level, `vendor/lean-miri/Miri/Interpreter/IntrinsicX86/Float.lean` models
  default round-to-nearest-even and canonical quiet-NaN bit patterns without
  `MXCSR` status flags).
- **System, privileged, x87, MMX, and segment-base instructions (`unsupported`):**
  `VendorX86Ref` targets 64-bit Ring-3 user-space computation (`CS.L = 1, CS.D =
  0`, flat zero segment bases); privileged instructions (`CLI` ->
  `.fault .gp0Privilege`), x87/MMX, and unmapped opcodes fail closed. *(Errata: `VendorX86Ref.Decode.scanPrefixes` accepted `0x64` (`FS:`), `0x65` (`GS:`), and `0x67` (`addr32`) without failing closed or applying `fsBase`/`gsBase`/32-bit truncation, and omitted `0x66` `op16` on `PUSH`/`POP` and `MOV`/ALU opcodes; repaired in `VendorX86RefV2` under corpus package `x86-64-fs-gs-segment-sfi-escape-addr32-opsize-decoding-and-pass2-prefix-fuzzing`.)*
- **Direct MIR `simd_*` lowering without `stdarch` guards (`known not to
  apply`):** As proved by the three counterexamples in Section 3 of
  `support/SimdTriangulation24.lean`, raw MIR `#[rustc_intrinsic]` `simd_shl`,
  `simd_shr`, `simd_bitmask`, and `simd_funnel_shl` are **not** total refinements
  of x86 VEX/EVEX `vpsllvd`, `vpmovmskb`, or `vprolvd`; equivalence holds only
  across the guarded `core::arch` wrapper functions in `stdarch` (or when target
  preconditions explicitly bound shift counts `< bit_width` and mask bytes `∈
  {0x00, 0xFF}`).
- **Concurrency memory-ordering semantics of `LOCK` instructions (`not
  examined`):** `VendorX86Ref` and `ByteX86` verify exact sequential read-modify-write
  state transitions, `RAX` witness updates (`CMPXCHG`, `XADD`), and `#UD`
  rejection of non-memory `LOCK` forms, but multi-core TSO store-buffer
  linearizability was **not examined**.
- **Microarchitectural portability of hardware-undefined values (`known not to
  apply`):** Ice Lake-SP's preservation of `oldDst` on `BSF`/`BSR` with zero
  source and specific undefined `RFLAGS` values on `IMUL`/`SHL` are
  microarchitectural observations, **known not to apply** as architectural
  guarantees across all x86-64 CPUs—which is precisely why `VendorX86Ref` and
  widened `ByteX86` model them demonically via `UndefOracle` / `DemonicChoice`.

## Evidence

### Primary upstream sources and normative specifications

- **Intel SDM (`normative`):** *Intel 64 and IA-32 Architectures Software
  Developer's Manual*, Order Number `325462-087US` (2025): Vol. 1 Section 14.5
  (VEX 128-bit upper-lane zeroing); Vol. 2A Section 2.1.1 (15-byte instruction
  length limit `#GP(0)`), Section 2.2.1 (REX immediate-predecessor placement rule),
  Section 2.3.5 (VEX prefix exclusions: `#UD` after `LOCK`/`66H`/`F2H`/`F3H`/REX,
  segment/`67H` allowed), and Section 3.2 (`BSF`/`BSR` undefined destination on
  zero source); Vol. 2B–2C (`VAESENC`, `VPCLMULQDQ`, `VPSHUFB`, `VPMADDUBSW`,
  `VPROLVD`, `VPTERNLOGD`).
- **`awslabs/s2n-bignum` (`source`):** Commit
  `d4518712d040485efe621caba1c723a07fbc549e`:
  - `x86/proofs/instruction.ml` (blob `e2d3e3c7fcf8238b862795e449819196166a42f4`,
    `26,071` B, `178` instruction constructors);
  - `x86/proofs/decode.ml` (blob `4c9a45b64f10e89e6314ddd2931ccb87c0058df6`,
    `180,031` B: `read_prefixes` at `L45-95`, single-pass `read_REX_prefix` at
    `L76-101`, legacy-only `AESENC` at `L1174`, `VPMOVMSKB` `l = T` guard at
    `L1334`);
  - `x86/proofs/x86.ml` (blob `dfcd64bcccb2ff8c9c701609aa13ebc763d541e4`,
    `331,579` B: `200` `x86_*` semantic definitions including `x86_BSF` /
    `x86_BSR` `UNDEFINED_VALUES[destx]` at `L898-912`).
- **`intelxed/xed` (`source`):** Commit
  `0bcb6237345c5066726dcc08b3d87928df3b5b26`, `datafiles/**/*.txt` and
  `datafiles/**/*.xed.txt` (`25` ISA grammar and legality files covering base
  x86-64, `LOCK`, BMI1/BMI2, ADX, CET, AVX, AVX2, AES, PCLMULQDQ, AVX-512F, and
  AVX-512VL/`skx-isa.xed.txt`, `1,334` distinct `ICLASS` entries).
- **`proofs-rs/lean-miri` & `joshlf/anneal` (`source`):**
  `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
  - `vendor/lean-miri/UPSTREAM_PIN.json` (pinning
    `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, built with
    `leanprover/lean4:v4.34.1`);
  - `vendor/lean-miri/Miri/Interpreter/IntrinsicSimd.lean` (`elementToBool` at
    `L75-79`, `shift` at `L165-179`, `bitmask` at `L369-396`, `funnelShift` at
    `L495-524`), `IntrinsicCrypto.lean`, `IntrinsicArchitecture.lean`,
    `IntrinsicVectorMachine.lean`, `Math/Bindings.lean`, `IntrinsicX86.lean`,
    and `IntrinsicX86/{Aes,Basic,Chunks,Crypto,DispatchFloat,DispatchVector,Extras,Float,Integer,Strings}.lean`;
  - `trusted/audit/TrustedBoundary.lean` (`ensureReplayableConstant` at `L1117-1125`,
    `validateRepoConstant` at `L1136-1153`, `collectRepoModuleConstants` at
    `L1240-1265`, and `collectCorrEnv` / `replayCorrAndVendor` at `L2140-2201`).

### Preserved package support material (`execution` + `derived`)

All experimental probes, transpiled Lean modules, correspondence proofs, and
machine-readable JSON receipts are preserved under `support/` (observed on
`2026-11-21` on `Linux 7.1.6-1rodete1-amd64` with Intel Xeon Ice Lake-SP):

- **Transpiler & emitted `VendorX86Ref` Lean modules:**
  `support/transpile_s2n_xed_to_lean.py`, `support/s2n_xed_transpiler_audit.json`,
  and `support/VendorX86Ref/{Types,Decode,SemanticsScalar,SemanticsSimd,Machine}.lean`.
- **Pass-2 `ByteX86` correspondence & `BSF` counterexample proof:**
  `support/ByteX86Pass2Correspondence.lean`.
- **3-way `core::arch` SIMD triangulation & UB asymmetry proofs:**
  `support/SimdTriangulation24.lean`, `support/probe_24_core_arch_primitives_obj.py`,
  and `support/probe_24_core_arch_primitives_obj_results.json`.
- **Live 224-vector Ice Lake-SP silicon & disassembler probe:**
  `support/probe_silicon_220_x86_vectors.py` and
  `support/probe_silicon_220_x86_vectors_results.json`.
- **`vendor/lean-miri` `IntrinsicSimd` + `IntrinsicX86` compile & replay audit:**
  `support/probe_lean_miri_simd_x86_audit.py` and
  `support/probe_lean_miri_simd_x86_audit_results.json`.
- **End-to-end compile, `224`-vector kernel check, and private kernel-replay
  benchmark:** `support/benchmark_lean_pass2_and_triangulation.py` and
  `support/benchmark_lean_pass2_and_triangulation_results.json`.

## Revalidation

Run these narrow discriminating checks from the package directory (wrapping Lean
invocations in the host cgroup/slot runner where applicable; all scripts create
and clean up their own `tempfile.TemporaryDirectory()` workspaces):

1. **Revalidate all `7` staged Lean modules, `224 / 224` silicon vectors, `0`
   `isPartial`/`unsafe`/`sorry` invariants, and standalone `(level := .private)`
   kernel replay (~`90 s` total, or ~`25 s` without `SiliconCheck224`):**
   ```console
   python3 -B support/benchmark_lean_pass2_and_triangulation.py \
     --transpiler-script support/transpile_s2n_xed_to_lean.py \
     --pass2-lean support/ByteX86Pass2Correspondence.lean \
     --triangulation-lean support/SimdTriangulation24.lean \
     --silicon-json support/probe_silicon_220_x86_vectors_results.json \
     --lean-bin lean \
     --out-json /tmp/reval_bench.json
   ```
   Confirm `rc = 0`, `zero_warnings_and_errors: true` on every module, and
   `partial_consts: []`, `unsafe_consts: []`, `axiom_consts: []`,
   `opaque_consts: []`, `forbidden_refs: []` under
   `standalone_private_kernel_replay.triangulation`.
2. **Revalidate `rustc -C opt-level=3` `.o` byte stability across a newer `rustc`
   or LLVM release (~`3 s`):**
   ```console
   python3 -B support/probe_24_core_arch_primitives_obj.py \
     --rustc-a rustc \
     --out-json /tmp/reval_obj.json
   ```
   Diff `primitives.*.hex_bytes` against
   `support/probe_24_core_arch_primitives_obj_results.json`. If a newer LLVM
   backend selects an alternate instruction sequence for any primitive `pXX`,
   only `pXXBytes`, `dec_pXX_*`, and `triangulate_pXX_*` in
   `support/SimdTriangulation24.lean` need to be updated and re-checked.
3. **Revalidate `vendor/lean-miri` `IntrinsicSimd` + `IntrinsicX86` on a bumped
   `lean-miri` commit or Lean toolchain (~`5 min` cold closure compile + `< 1 s`
   kernel replay):**
   ```console
   python3 -B support/probe_lean_miri_simd_x86_audit.py \
     --vendor-dir <path-to-vendor-lean-miri> \
     --lean-bin lean \
     --out-json /tmp/reval_miri.json
   ```
   Check `kernel_replay_and_audit` (`unsafe_consts: []`, `partial_consts: []`,
   `forbidden_refs: []`) and `EdgeCaseTheorems` compilation.
4. **Revalidate live hardware trap/length/flag/SIMD behavior on a new x86-64
   microarchitecture (~`2 s`, requires AVX-512 Linux x86-64 host):**
   ```console
   python3 -B support/probe_silicon_220_x86_vectors.py \
     --out-json /tmp/reval_silicon.json
   ```
   Then feed `/tmp/reval_silicon.json` to `--silicon-json` in step 1 to verify
   that every observed hardware transition remains inside `VendorX86Ref.Step`
   (and therefore `ByteX86.Step`).
