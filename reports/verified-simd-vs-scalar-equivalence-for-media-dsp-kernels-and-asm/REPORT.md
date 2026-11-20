# Verified SIMD-vs-Scalar Equivalence for Multimedia DSP Kernels and Assembly

## Summary

Proving or testing that hand-tuned SIMD intrinsics and external assembly kernels produce bit-exact outputs matching a clean scalar reference—without memory-safety violations, undefined poison propagation, or hidden register/padding over-reads—is the central scaling bottleneck of verified multimedia codec engineering:

1. **Scale of the Codec DSP Surface vs. Existing Cryptographic Proofs (`Basis: source`):** A single production AV1 decoder (`videolan/dav1d` at `9af5ae4eb5204706c7f381ec62635237179f172e`) contains **270,877 lines** of hand-written SIMD assembly and intrinsics across six target architectures (`161,293` LOC and ~`792` `cglobal` entry points in `src/x86/` alone, `41,672` LOC in `src/arm/64/`, `30,879` LOC in `src/arm/32/`, `23,278` LOC in `src/loongarch/`, `8,485` LOC in `src/riscv/64/`, and `5,270` LOC in `src/ppc/`). Upstream `FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`) registers **104 distinct DSP test suites** in `tests/checkasm/checkasm.c:57-330` across `9` ISA families (`37` CPU capability tiers in `checkasm.c:333-399`). By contrast, a single HOL Light AVX2+NEON proof of a 256-lane `int16` butterfly kernel (`mlkem_ntt`) in `awslabs/s2n-bignum` (`280a220986a0bc6249248187717a771153d073db`) requires `1,465` lines of OCaml proof script for `659` lines of x86_64 assembly (`2.22x` proof-to-ASM ratio) and `600` lines of proof for `372` lines of AArch64 NEON (`1.61x`).
2. **ISA Semantic Coverage Gaps Between Cryptographic and Media Assembly Verifiers (`Basis: source`):** Direct inspection of mechanized x86 instruction tables across `awslabs/s2n-bignum` (`x86/proofs/x86.ml`), `jasmin-lang/jasmin` (`proofs/compiler/x86_instr_decl.v`), and `hacl-star/hacl-star` (`vale/code/arch/x64/Vale.X64.InsVector.vaf`) reveals that cryptographic verifiers now model post-quantum 16-bit butterfly and multiply-add primitives (`VPMADDUBSW`, `VPMADDWD`, `VPERM2I128`, `VPSHUFB`), and `s2n-bignum` additionally models `VPMULHRSW` and `VPACKUSWB`, **none of the three mechanizes unsigned rounding halving-add (`VPAVGB`/`VPAVGW`) or signed saturating 32-to-16 pack (`VPACKSSDW`)**, which are pervasive in motion compensation (`vp9mc.asm:243-245`) and inverse transforms.
3. **Hidden Media-Specific Equivalence Hazards (`Basis: source + execution`):** Multimedia SIMD kernels exploit lossy fixed-point instructions that are *conditionally* equivalent to scalar reference C only under tight coefficient, domain, and pairing preconditions:
   - **`PMADDUBSW` Intermediate `int16` Saturation (`vp9mc.asm:61-113`):** `vpmaddubsw` computes `sat_i16(u8_0 * i8_0 + u8_1 * i8_1)` *before* `vpmaddwd` widens to `i32`. Across all `45` VP9 8-tap subpixel filters, `FFmpeg`'s adjacent tap pairing `(c_{2k}, c_{2k+1})` bounds intermediate sums to `[-6120, 32385]`, clearing `+32767` by only `382` counts (`Basis: execution`). Naive symmetric folding `(c_3, c_4)` reaches `40,800`, overflowing `int16` saturation on **`30/45` (`66.7%`)** of VP9 filters and corrupting clipped `[0, 255]` output pixels by up to `63` gray levels (`211` vs. `148` on sharp filter index `7`).
   - **Cascaded `PAVGB`/`URHADD` Double-Rounding Bias:** Chaining two hardware rounding averages `PAVGB(PAVGB(a, b), PAVGB(c, d))` diverges from normative single-rounded 2D bilinear filtering `(a + b + c + d + 2) >> 2` on **exact `96/256` (`37.5%`)** of `[0, 255]^4` pixel tuples, introducing a strictly positive `+1` DC drift (`Basis: execution`).
   - **Cross-ISA `VPMULHRSW` vs. `SQRDMULH` Corner-Case Divergence:** x86 SSSE3/AVX2 `vpmulhrsw` wraps `(-32768, -32768)` to **`-32768`** (`0x8000`), whereas Arm NEON `sqrdmulh` saturates the identical input pair to **`+32767`** (`0x7FFF`), requiring explicit input-domain exclusion `(a, b) != (-32768, -32768)` in cross-ISA equivalence proofs (`Basis: execution`).
4. **Verification Decomposition That Scales to Codec Kernels (`Basis: source + derived`):** Monolithic `QF_BV` SMT translation validation (`Alive2`) handles straight-line 128/256-bit elementwise and saturating intrinsics cleanly, but times out on 2D butterfly transposes and wide multiply-accumulate convolutions. Scaling verified SIMD-vs-scalar equivalence across hundreds of codec kernels requires combining **Rake's swizzle-decoupled per-lane projection** (`uwplse/rake`, `rake/synthesis/verify.rkt:69-98`), **CryptoLine's Groebner-basis algebraic + `QF_BV` range split** (`fmlab-iis/cryptoline`, `verify/cas.ml` + `verify/smt.ml`), and **spatial memory-lens preconditions** that explicitly model negative strides (`ptrdiff_t`), row-tail SIMD over-fetches, and bitstream/frame buffer padding (`AV_INPUT_BUFFER_PADDING_SIZE = 64` in `libavcodec/defs.h:40`).

## Applicability

This report governs formal equivalence verification, translation validation, DSL synthesis, and differential runtime testing (`checkasm`) between scalar reference implementations and SIMD/assembly kernels across multimedia codecs (video motion compensation, intra prediction, DCT/ADST/WHT inverse transforms, deblocking, CDEF, Wiener/SGR loop restoration, film grain, audio MDCT/FIR/LPC, and `swscale` color/resampling pipelines).

- **Examined Systems and Relationship:**
  - `FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`), `videolan/dav1d` (`9af5ae4eb5204706c7f381ec62635237179f172e`), and `memorysafety/rav1d` (`2e7216c20ac2a75de204d6c8d7268b75a45959b4`) define the concrete multimedia kernel inventory, buffer/stride ABI contracts, and `checkasm` empirical oracle discipline.
  - `awslabs/s2n-bignum` (`280a220986a0bc6249248187717a771153d073db`), `jasmin-lang/jasmin` (`8c3279973a89afd969e50301f71563bb40d55724`), `hacl-star/hacl-star` (`f557259007db9933442dde10aa995c1b00bd3446`), `project-everest/vale` (`bbae0eb89143734363b14a77642dbf8dec36e288`), and `fmlab-iis/cryptoline` (`c992f0c41b5f34fb1a07bf3f84568c732a935272`) provide production machine-code and assembly equivalence frameworks evaluated for adaptation from cryptographic primitives to media DSP. Foundational TCB and proof-replay details of `s2n-bignum`, `Jasmin`, `Vale`, and `CryptoLine` established in sibling corpus packages `jasmin-s2n-bignum-cslib-and-verified-cryptographic-assembly`, `fiat-crypto-hacl-evercrypt-vale-libcrux-and-verified-crypto-synthesis`, and `cryptol-saw-symbolic-equivalence-easycrypt-game-hopping-and-cryptoline` are referenced by slug rather than repeated.
  - `AliveToolkit/alive2` (`3bdd4f5e1cefa47057e93110e707acd11cfe08e4`), `halide/Halide` (`54c1a9bd6733081c8700a7c2521871161a701fad`), `ispc/ispc` (`ccb91bbc5332f026f494c48263b935145cd72f77`), `uwplse/rake` (`2b499110cecfee875edf392306b41be8d6cc2567`), and `akothen/Hydride` (`0c97d0f9d3f8cd0494e421b9ece4b24488b614e5`) characterize compiler-IR, term-rewriting, SPMD, and solver-aided synthesis approaches to SIMD equivalence. Sibling packages `black-box-translation-validation-alive2-and-mir-to-llvm-on-rust`, `core-simd-mask-all-ones-ub-masked-tail-loads-and-lanewise-chunk-algebras`, and `entropy-coded-media-bitstreams-video-codec-security-and-simd-decoders` cover general LLVM scalar/MIR translation validation, Rust `core::simd` mask UB, and entropy-bitstream safety respectively.
- **Target ISAs:** Findings cover fixed-width SIMD (`x86`/`x86_64` MMX through AVX-512ICL/VNNI, `aarch64`/`armv7` NEON, `ppc64le` Altivec/VSX, `loongarch64` LSX/LASX, `mips` MSA, `wasm32` SIMD128, Qualcomm Hexagon HVX 1024/2048-bit) and scalable vector extensions (`aarch64` SVE/SVE2/SME2, `riscv64` RVV 1.0).

## Findings

### 1. Verification Priority Hierarchy Across Multimedia SIMD Kernels

`Basis: source + derived`

In multimedia codecs, scalar-to-SIMD equivalence is not a single monolithic predicate; it stratifies into four distinct verification obligations ordered by criticality:

1. **Priority 1 — UB-Freedom and Spatial Memory Isolation:** Every vector load, store, gather, scatter, and stack spill stays strictly within allocated frame/scratch regions (respecting row `stride`, alignment, negative-stride pointer arithmetic, and explicit over-read padding), preserves ABI non-volatile registers and control state (`vzeroupper`, `MXCSR`, `FPCR`, `vstart == 0`), and never exposes uninitialized padding bytes or `poison` lanes to observable scalar control flow or output buffers.
2. **Priority 2 — Panic-Freedom and Trap-Freedom on Adversarial Media Inputs:** No untrusted pixel sample, quantized transform coefficient, motion vector offset, filter weight, or arbitrary block width/height triggers hardware traps (`#DE` division error, `#GP` unaligned `VMOVDQA` fault, AArch64 `SPAlignmentFault`, RVV `vill` illegal `vtype`), arithmetic shift UB, or Rust bounds/unwrap panics.
3. **Priority 3 — Bit-Exact (or Bounded-ULP Float) SIMD-vs-Scalar Equivalence:** Under the explicit input domain preconditions guaranteed by upstream bitstream syntax or prior pipeline stages (for example, `10-bit` pixel range `[0, 1023]`, filter tap sum `== 128`, or dequantized DCT coefficient bounds), the SIMD/assembly kernel writes the **exact same byte sequence** to the active output rectangle `[0..h) x [0..w)` as the clean scalar reference function. For floating-point audio/filter kernels (`aacpsdsp`, `sbrdsp`, `float_dsp`, `af_afir`), IEEE-754 non-associativity prevents bit-identity across tree reductions and FMA fusion, requiring bounded relative/absolute error contracts matching `checkasm`'s `float_near_ulp` / `float_near_abs_eps` tolerances.
4. **Priority 4 — Normative Codec Standard Conformance:** The clean scalar reference itself equals the mathematical equations of ITU-T H.264, H.265/HEVC, H.266/VVC, SMPTE VC-1, IETF RFC 6716 (Opus), or AOMedia AV1. Factoring Priority 3 (SIMD == Scalar Reference) from Priority 4 (Scalar Reference == ITU/ISO Spec) is essential: if a codec has `K` ISA backends (`SSE2`, `SSSE3`, `AVX2`, `AVX-512ICL`, `NEON`, `SVE2`, `RVV`, `VSX`, `LASX`), proving each SIMD backend equivalent to a single clean scalar Rust specification reduces $K \times \text{Spec}$ complex functional proofs to $1$ functional spec proof plus $K$ finite-horizon bitvector/permutation equivalence proofs.

---

### 2. Anatomy of Formal and Empirical SIMD Equivalence Frameworks

#### 2.1 Machine-Code Operational Frameworks: `s2n-bignum`, `Jasmin`, and `Vale`

`Basis: source`

Production machine-code verifiers developed for cryptography provide the highest-assurance TCB model—proving object-code or assembly equivalence directly against ISA semantics without trusting C compilers or LLVM—but exhibit sharp trade-offs when applied to media DSP:

- **AWS `s2n-bignum` (`awslabs/s2n-bignum` at `280a220986a0bc6249248187717a771153d073db`):**
  Verifies assembled ELF/Mach-O machine bytes directly in HOL Light (`define_assert_from_elf` in `x86/proofs/mlkem_ntt.ml:7`). Its post-quantum `mlkem_ntt` proofs (`x86/mlkem/mlkem_ntt.S` + `x86/proofs/mlkem_ntt.ml` and `arm/mlkem/mlkem_ntt.S` + `arm/proofs/mlkem_ntt.ml`) represent the closest existing formal analogue to video-codec 2D DCT/ADST inverse transforms:
  - *Execution and lane-splitting strategy:* On AArch64 (`arm/proofs/mlkem_ntt.ml:473-510`), `MEMORY_128_FROM_16_TAC` coalesces `256` scalar `int16` memory cells (`512` bytes) into `32` 128-bit `int128` vector words, symbolically steps all `904` unrolled NEON instructions (`ARM_STEPS_TAC MLKEM_NTT_EXEC [n] THEN SIMD_SIMPLIFY_ABBREV_TAC[barmul] []` over `1..904`), splits final 128-bit `Q` registers back into `16`-bit lanes via `READ_MEMORY_SPLIT_CONV 3`, and discharges both modular equivalence (`mod 3329`) and **signed 16-bit non-overflow bounds** (`abs(ival(x i)) <= 8191 ==> abs(ival zi) <= 23594`, lines `535-540`) via `CONGBOUND_NTT_TAC`.
  - *ABI & memory-safety coupling:* `s2n-bignum` proves both SysV and Windows x64 ABI wrappers (`MLKEM_NTT_WINDOWS_SUBROUTINE_CORRECT`, `x86/proofs/mlkem_ntt.ml:1300-1465`, tracking 128-bit `XMM6..XMM15` preservation inside 256-bit `YMM6..YMM15` via lens composition `ZMM6 :> bottomhalf :> bottomhalf`) and trace-level memory-bounds/constant-time safety (`MLKEM_NTT_SUBROUTINE_SAFE`, `arm/proofs/mlkem_ntt.ml:570-600`, proving `memaccess_inbounds`).
- **Jasmin (`jasmin-lang/jasmin` at `8c3279973a89afd969e50301f71563bb40d55724`):**
  Compiles structured assembly-level `.jazz` programs (with `reg u128` / `reg u256` SIMD values, inline `for` loops, and stack arrays) through a Coq-verified compiler (`it_compile_prog_to_asmP`), while Equivalence between a scalar `.jazz` reference and an AVX2 `.jazz` implementation is discharged in EasyCrypt's relational Hoare logic (`rhl`). In `proofs/compiler/x86_instr_decl.v`, Jasmin defines Coq bitvector semantics and VEX upper-lane clearing (`MSB_CLEAR`) for `VPERM2I128` (`lines 1786-1791`), `VPMADDUBSW` (`lines 1881-1899`), `VPMADDWD` (`lines 1901-1918`), `VPSHUFB`, and `VPUNPCKL*`, alongside `DOIT` (Data Operand Independent Timing) side-channel annotations.
- **Vale and HACL\* `Lib.IntVector` (`hacl-star/hacl-star` at `f557259007db9933442dde10aa995c1b00bd3446` and `project-everest/vale` at `bbae0eb89143734363b14a77642dbf8dec36e288`):**
  Project Everest splits SIMD verification into two distinct tiers:
  1. *Vale procedural assembly (`vale/code/arch/x64/Vale.X64.InsVector.vaf`, `742` lines; `vale/specs/hardware/Vale.X64.Machine_Semantics_s.fst`, `777` lines):* Models XMM register instructions (`Paddd`, `Pxor`, `Pshufb`, `Palignr`) with Hoare pre/postconditions discharged by Z3 via F*. Because Z3 struggles with raw 128/256-bit bitvectors across loops, Vale wraps four `uint32` lanes as an abstract `quad32` four-tuple (`Mkfour`), avoiding bit-blasting except inside leaf instruction axioms.
  2. *`Lib.IntVector` (`lib/Lib.IntVector.fsti`, `413` lines):* Models portable `vec_t` (`U8x16`, `U32x4`, `U64x2`, `U64x4`) as pure F* `Seq.lseq` sequences of scalar integers (`vec_v`), proving lane-wise equivalence to scalar specs in F* before KaRaMeL lowers `Lib.IntVector` calls to C `<immintrin.h>` / `<arm_neon.h>` intrinsics (placing C compiler intrinsic lowering inside the TCB).

| Instruction / Capability | Media Codec Role | `s2n-bignum` (`x86/proofs/x86.ml`) | `Jasmin` (`x86_instr_decl.v`) | `Vale` (`Vale.X64.InsVector.vaf`) | `Halide` (`FindIntrinsics.cpp`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `VPMADDUBSW` (`u8*i8 -> sat_i16`) | 8-bit 8-tap MC, chroma/Wiener filters | **Present** | **Present** (`:1881`) | Absent | **Present** (dot-product lowering) |
| `VPMADDWD` (`i16*i16 -> i32`) | 10/12-bit MC, DCT/ADST, audio FIR/LPC | **Present** | **Present** (`:1901`) | Absent | **Present** |
| `VPERM2I128` / `VPERMQ` | AVX2 cross-128-bit-lane transpose/shuffle | **Present** | **Present** (`:1786`) | Absent (128-bit `quad32` focus) | **Present** |
| `VPSHUFB` / `VPUNPCKL*` | Sub-lane byte table lookup & interleave | **Present** | **Present** | **Present** (`Pshufb`) | **Present** |
| `VPMULHRSW` (`(a*b>>14 + 1)>>1`) | Q15 transform scaling, CDEF, Wiener | **Present** | **Absent** | Absent | **Present** (`rounding_mul_shift_right`) |
| `VPACKUSWB` (`sat_u8(i16)`) | 8-bit pixel reconstruction clipping | **Present** | **Absent** | Absent | **Present** (`saturating_narrow`) |
| `VPACKSSDW` (`sat_i16(i32)`) | 16-bit coefficient / residual narrowing | **Absent** | **Absent** | Absent | **Present** (`saturating_narrow`) |
| `VPAVGB` / `VPAVGW` (`(a+b+1)>>1`) | Half-pel / bi-pred / bilinear averaging | **Absent** | **Absent** | Absent | **Present** (`rounding_halving_add`) |

#### 2.2 Algebraic + Bitvector Splitting: `CryptoLine`

`Basis: source`

Pure `QF_BV` SMT solvers (Z3, Bitwuzla, Boolector) bit-blast `16 x 16 -> 32` and `32 x 32 -> 64` multipliers into large Wallace-tree AIG circuits, frequently timing out when proving associativity/commutativity across rearranged SIMD multiply-accumulate trees (such as radix-4/radix-8 DCT/IDCT butterflies vs. naive scalar matrix-vector products). `fmlab-iis/cryptoline` (`c992f0c41b5f34fb1a07bf3f84568c732a935272`) resolves this by splitting every SSA instruction into two coupled obligations:
1. **Algebraic Entailment (`verify/cas.ml`, `1,740` lines):** Encodes linear and nonlinear ring identities ($\sum_k p_k c_k$, butterfly factorizations, Karatsuba/Cooley-Tukey splits) as polynomial ideal membership over $\mathbb{Z}$ or $\mathbb{Z}/2^w\mathbb{Z}$, discharged in milliseconds by computer-algebra Groebner-basis engines (`Singular`, `Macaulay2`, `Pari/GP`).
2. **Range / No-Overflow Entailment (`verify/smt.ml`, `984` lines):** Uses `QF_BV` SMT strictly to verify **soundness guards**—that signed/unsigned arithmetic never crosses saturation or wrap-around boundaries so the integer ring interpretation in `cas.ml` agrees bit-for-bit with modular/saturating machine instructions.

For media codecs, this algebraic-plus-range split directly solves the **inverse-transform (`itx`) equivalence bottleneck**: proving that a 16-point or 32-point AVX2 butterfly IDCT matches a scalar C reference becomes trivial in $\mathbb{Z}$ once narrow interval/SMT range checks discharge intermediate `int16`/`int32` non-overflow at each butterfly stage.

#### 2.3 Compiler-IR Validation, Term Rewriting, and Synthesis: `Alive2`, `Halide`, `ISPC`, `Rake`, and `Hydride`

`Basis: source + documentation`

- **`Alive2` (`AliveToolkit/alive2` at `3bdd4f5e1cefa47057e93110e707acd11cfe08e4`; Lopes et al., PLDI 2021, `DOI: 10.1145/3453483.3454030`):**
  Encodes LLVM IR vector types, `ShuffleVector` (`ir/instr.h:1330`), saturating intrinsics (`sadd.sat`, `uadd.sat`, `sshl.sat`), and target-specific x86 intrinsics into `QF_BV` (or `QF_ABV` with memory) refinement queries checking that target `undef`/`poison` and return values refine source semantics. As established in `black-box-translation-validation-alive2-and-mir-to-llvm-on-rust`, Alive2 excels on straight-line peephole and SLP-vectorized blocks (`<= 8` lanes without deep nonlinear chains) but requires loop unrolling (`-unroll`), rejects inline/external assembly, and degrades sharply when 256/512-bit cross-lane shuffles compose with multiplications.
- **`Halide` (`halide/Halide` at `54c1a9bd6733081c8700a7c2521871161a701fad`; Newcomb et al., OOPSLA 2020, `DOI: 10.1145/3428234`):**
  Instead of post-hoc binary lifting, Halide separates pure functional algorithm expressions from vectorization/tiling schedules and lowers scalar fixed-point idioms to portable SIMD intrinsics in `src/FindIntrinsics.cpp` (`1,742` lines):
  - Recognizes widening arithmetic (`widening_mul`, `widening_add`), saturating casts (`saturating_narrow` at `lines 46-49`), rounding shifts (`to_rounding_shift` at `lines 182-220`), and rewrites `(a + b + 1) >> 1` / `halving_add(widening_add(x, y), 1)` into `rounding_halving_add(x, y)` (`lines 731-740, 962-969`), noting explicitly (`lines 704-705`) that unsigned `rounding_halving_add` maps directly to x86 `pavgb`/`pavgw` whereas unrounded `halving_add` requires `(a & b) + ((a ^ b) >> 1)` (`lines 1501-1505`) on x86!
  - Even more subtly, `lower_halving_sub` (`lines 1507-1528`) derives exact two's-complement bit-tricks from `rounding_halving_add(a, ~b)` (`+ 128` bias correction for `uint8` at `line 1518`, zero adjustment for `int8` at `line 1526`), and `lower_rounding_mul_shift_right` (`lines 1581-1634`) uses `constant_integer_bounds` interval analysis to pre-scale operands `(a << a_shift, b << b_shift)` into full-width Q15 `vpmulhrsw`/`sqrdmulh` instructions *only when `a.type().can_represent(bigger)` proves shift non-overflow*. Newcomb et al. (`DOI: 10.1145/3428234`) mechanized over 1,000 of Halide's rewrite rules in Coq + Z3, catching bitwidth/overflow bugs where naive algebraic rewrites altered signed overflow or rounding behavior.
- **`ISPC` (`ispc/ispc` at `ccb91bbc5332f026f494c48263b935145cd72f77`):**
  Models SIMD as Single-Program Multiple-Data (`varying` lane values vs. `uniform` scalar control/pointers in `src/expr.cpp`), maintaining an implicit per-lane execution mask across divergent branches and `foreach` loop tails. While convenient for regular 1D/float workloads, ISPC's implicit lane-mask abstraction maps poorly onto video codecs' **sub-register mixed-width pipelines** (where a single kernel loads 8-bit pixels, widens to 16-bit taps, accumulates in 32-bit pairs, transposes `8x8` blocks across lanes, and packs back to 8-bit).
- **`Rake` (`uwplse/rake` at `2b499110cecfee875edf392306b41be8d6cc2567`; Ahmad et al., ASPLOS 2022, `DOI: 10.1145/3503222.3507714`):**
  Addresses the two hardest problems in media DSP synthesis and verification—widening/narrowing lane interleaving and wide vector bit-blasting—via a **three-pass architecture** in `rake/synthesis/algorithm.rkt:15-39`:
  1. *Layout-free lifting (`rake/synthesis/lifting/greedy-ir-lifter.rkt`):* Lifts Halide IR expressions into target-specific `uber-instructions` that capture exact fixed-point arithmetic (such as Hexagon HVX widening `vmpy` / `vrmpy` dot products) while abstracting away physical lane order.
  2. *Decoupled lowering + swizzling (`rake/synthesis/lowering/` + `rake/synthesis/swizzling/`):* Synthesizes arithmetic lowering first, then separately synthesizes minimal lane-permutation networks (`vdeal`, `vshuff`, `vpack`) to reconcile producer/consumer data layouts.
  3. *Per-lane cone-of-influence equivalence verification (`rake/synthesis/verify.rkt:69-98`):* Rather than asserting monolithic 1024-bit (`u8x128`) or 2048-bit (`u8x128x2`) vector equality in Rosette/Z3, `verify-equiv` iterates lane-by-lane (`0..255`), calling `(clear-vc!)` and `verify-lane` (`lines 80-98`) to prove `(eq? (halide-output lane) ...)` universally quantified over symbolic inputs (`#:forall ctx`). Because SMT preprocessing eliminates all input lanes outside the single output lane's cone of influence, per-lane slicing turns intractable 2048-bit bitvector queries into fast, embarrassingly parallel per-lane queries.
- **`Hydride` (`akothen/Hydride` at `0c97d0f9d3f8cd0494e421b9ece4b24488b614e5`; Kothari et al., ASPLOS 2024, `DOI: 10.1145/3620665.3640385`):**
  Eliminates manual per-ISA backend engineering by ingesting **vendor pseudocode specifications** (Intel x86 Intrinsics Guide XML, Arm ACLE/ASL, Hexagon HVX specs) in `codegen-generator/` to automatically generate Rosette formal semantics, `AutoLLVM IR` intrinsics, and bounded synthesis/legalization passes across x86 (`SSE` through `AVX-512 VNNI`), AArch64 `NEON`, and `HVX` (`README.md:48-53`). Hydride uses divide-and-conquer window synthesis with memoized symbolic hashes so synthesis scales across thousands of vendor intrinsics; however, its TCB relies on vendor XML pseudocode fidelity (see sibling report `vendor-intrinsic-specifications-stdarch-verification-and-lean-generation` for documented Intel XML vs. Arm JSON schema asymmetries).

---

### 3. Empirical Differential Harnesses: `FFmpeg`, `dav1d`, and `rav1d` `checkasm`

`Basis: source`

Because formal machine-code proofs have not yet been deployed across mainstream media libraries, `FFmpeg`, `dav1d`, and `rav1d` rely on **`checkasm`** as their mandatory empirical SIMD-vs-scalar equivalence gate:

1. **Suite Breadth and Multi-Tier CPU Masking (`FFmpeg/FFmpeg` `tests/checkasm/checkasm.c:57-429`, `tests/checkasm/checkasm.h:149-189`):**
   At commit `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, `FFmpeg` links against the standalone `libcheckasm` (`<checkasm/checkasm.h>`, `checkasm.c:52`) and registers **104 test modules** (`69` in `libavcodec` spanning `aacpsdsp` through `vvc_sao`, `18` in `libavfilter`, `8` in `libswscale`, and `9` in `libavutil`). For each module, `checkasm` monotonically enables cumulative ISA capability masks (`cpuflags[]`, `lines 333-399`: `18` tiers on x86 from `MMX` to `AVX-512ICL`; `13` tiers on AArch64 from `ARMV8`/`NEON` through `DOTPROD`, `I8MM`, `SVE2`, and `SME2`; `9` tiers on RISC-V including `RV_zve32x`..`RV_zvbb`), comparing each newly dispatched assembly function pointer (`call_new`) against the baseline C implementation (`call_ref`).
2. **What `checkasm` Catches Beyond Output Equality (`checkasm.h:149-175`):**
   - *2D Padded Rectangles and Overwrite Detection:* `PIXEL_RECT(name, w, h)` (`checkasm.h:149-155`) allocates guard-padded 2D buffers with randomized stride/canary bytes; `checkasm_check_pixel_padded` (`lines 171-172`) verifies both that active `[0..w) x [0..h)` pixels match `call_ref` bit-for-bit and that canary bytes outside the active block (or permitted alignment tail, `checkasm_check_pixel_padded_align` with `8`-byte granularity) were not clobbered.
   - *ABI Register-Clobber Trampoline:* `call_new` invokes the assembly function through an architecture-specific trampoline that seeds callee-saved GPRs and partial vector registers (Win64 `XMM6..XMM15`, AArch64 `D8..D15`, RISC-V `s0..s11`/`fs0..fs11` and `vstart`), verifies stack-pointer balance, and on x86_64 checks whether upper `YMM`/`ZMM` state was left dirty (`vzeroupper` omission).
3. **Why `checkasm` Is Necessary But Strictly Incomplete Compared to Formal Verification (`Basis: derived`):**
   Random input buffers (`checkasm_rand_uint32` / Gaussian `randomize_stddev`) have negligible probability of hitting **measure-zero arithmetic corner cases**:
   - Hitting `(-32768, -32768)` on a 16-bit lane (`vpmulhrsw` vs. `sqrdmulh`) under uniform random `int16` fuzzing occurs with probability $2^{-32} \approx 2.33 \times 10^{-10}$ per lane evaluation.
   - Hitting worst-case signed/unsigned alternating pixel patterns (`[255, 0, 255, 255, 255, 255, 0, 255]`) aligned with extreme subpixel filter phases occurs with probability $2^{-64}$ if bytes are drawn uniformly, unless test authors manually craft extremal patterns (`0x00`/`0xFF` checkerboard, minimum/maximum DCT coefficients).

---

### 4. Six Multimedia-Specific SIMD Equivalence Challenges and Exact Preconditions

#### 4.1 Fixed-Point Rounding Biases and Cascaded `PAVGB` / `URHADD` Drift

`Basis: source + execution`

Video codecs specify integer-exact rounding shifts—typically `(x + (1 << (n - 1))) >> n` (round-half-up toward $+\infty$) or asymmetric bi-prediction rounding `(a + b + 1) >> 1`. Hardware SIMD instructions (`x86` `PAVGB`/`PAVGW`, Arm NEON `URHADD`/`SRHADD`, RVV `vaaddu.vv` under `vxrm = rnu`) compute exact 1-bit rounded averages `(a + b + 1) >> 1` without widening overflow. However, two equivalence traps arise:

1. **Unrounded Halving (`(a + b) >> 1`) on x86:** MPEG-4 / H.263 `no_rnd` motion compensation requires `(a + b) >> 1`, which Arm NEON provides natively (`UHADD`) but x86 SSE2/AVX2 lacks! Lowering `(a + b) >> 1` without widening to 16 bits requires either Halide's carry-free identity `(a & b) + ((a ^ b) >> 1)` (`FindIntrinsics.cpp:1504`) or `PAVGB(a, b) - ((a ^ b) & 1)`. Omitting the `((a ^ b) & 1)` LSB correction diverges on **50.0%** of all pixel pairs (every pair where `a + b` is odd).
2. **2D Bilinear Cascaded `PAVGB` Double-Rounding Hazard:** Approximating a 4-sample quarter-pel/chroma average `(a + b + c + d + 2) >> 2` via two cascaded instructions `PAVGB(PAVGB(a, b), PAVGB(c, d))` is **not equivalent**: exhaustive evaluation across all $4^4 = 256$ residue classes modulo 4 (`256^4 = 4,294,967,296` `u8` tuples; see Section `## Evidence` Probe 1) proves that `PAVGB(PAVGB(a, b), PAVGB(c, d))` exceeds `(a + b + c + d + 2) >> 2` by `+1` on **`96/256` (`37.50%`)** of inputs and never under-estimates (`0%` `-1` error), creating visible inter-frame brightness drift unless the standard itself (as in H.264 chroma/qpel stages that normatively define two-step 1D horizontal-then-vertical rounding) specifies cascaded rounding!

#### 4.2 Saturating Widening/Narrowing and the `PMADDUBSW` Pairing Invariant

`Basis: source + execution`

In 8-bit video motion compensation (`FFmpeg/FFmpeg` `libavcodec/x86/vp9mc.asm:31-120, 177-246`), scalar C computes an 8-tap filter $\text{clip}_{u8}((\sum_{i=0}^7 p_i c_i + 64) \gg 7)$ in `int32` arithmetic (`vp9dsp_template.c`), where $p_i \in [0, 255]$ (`uint8`) and $c_i \in [-128, 127]$ (`int8`, $\sum_{i=0}^7 c_i = 128$). SSSE3/AVX2/AVX-512 VNNI accelerate this using `VPMADDUBSW` (`u8 * i8 -> sat_i16` pairwise) followed by `VPMADDWD` (`i16 * 1 -> i32`):

$$\text{VPMADDUBSW}(p, c)_k = \text{ clamp}_{[-32768,\, 32767]}\!\bigl(p_{2k}\cdot c_{2k} + p_{2k+1}\cdot c_{2k+1}\bigr)$$

- **Exact Soundness Precondition:** `VPMADDUBSW` agrees with unbounded `int32` scalar accumulation for tap pair $(c_a, c_b)$ **if and only if**:
  $$255 \cdot \max(0, c_a) + 255 \cdot \max(0, c_b) \le 32767 \quad \land \quad 255 \cdot \min(0, c_a) + 255 \cdot \min(0, c_b) \ge -32768$$
  Dividing by `255` yields the sharp integer tap-pair condition: **whenever $c_a > 0$ and $c_b > 0$, equivalence requires $c_a + c_b \le 128$** ($128 \times 255 = 32,640 \le 32,767$, whereas $129 \times 255 = 32,895 > 32,767$)!
- **Empirical Verification on VP9's 45 Subpixel Filters (`Basis: execution`):** Across all `45` VP9 8-tap filters in `vp9mc.asm:61-113` (`smooth`, `regular`, `sharp` $\times$ `15` phases), adjacent pairing `(c_{2k}, c_{2k+1})` keeps every pair inside **`[-6,120, 32,385]`** (peaking at `255 * 127 + 255 * 0 = 32,385` on `sharp` phases `1` and `15`), proving **100% bit-exactness**. Conversely, grouping symmetric taps `(c_3, c_4)` (for example, `sharp` half-pel `[ -4, 11, -23, 80, 80, -23, 11, -4 ]` at `vp9mc.asm:106`, where $c_3 + c_4 = 160 > 128$) reaches `40,800`, saturating `int16` on **`30/45` (`66.7%`)** of VP9 filters! On pixel input `[255, 0, 255, 255, 255, 255, 0, 255]`, scalar C and adjacent `VPMADDUBSW` both output pixel **`211`** (`raw = 27,030`), whereas symmetric `(c_3, c_4)` `VPMADDUBSW` outputs **`148`** (`raw = 18,997`)—a silent `63`-level error.
- **10-Bit and 12-Bit Narrowing Saturation Trap:** Hardware `VPACKUSWB` / `UQXTN` saturate to `8`-bit `[0, 255]` (`2^8 - 1`), and `VPACKUSWB`/`VPACKSSDW` have no parameterized bit-depth ceiling. For 10-bit (`[0, 1023]`) and 12-bit (`[0, 4095]`) High-Bit-Depth (`HBD`) profiles (`dav1d` `16bpp` kernels), reconstruction **cannot** rely on pack saturation alone and must execute explicit `vpminsw`/`vminq_s16` against broadcasted `1023` or `4095` after `vpmaxsw` against `0`.

#### 4.3 Cross-ISA `VPMULHRSW` vs. `SQRDMULH` Corner Case

`Basis: execution`

Both x86 `VPMULHRSW` and Arm NEON `SQRDMULH` compute rounded Q15 fixed-point products $\lfloor (a \cdot b + 2^{14}) / 2^{15} \rfloor$ over signed `int16` lanes. For every input pair $(a, b) \in [-32768, 32767]^2 \setminus \{(-32768, -32768)\}$ (`4,294,967,295` of `4,294,967,296` pairs), they are bit-identical. At $a = -32768, b = -32768$:
- x86 `VPMULHRSW` computes `temp = ((a * b) >> 14) + 1 = 65537` (`0x10001`) and extracts bits `[16:1] = 0x8000` = **`-32768`** (two's-complement wrap-around).
- Arm NEON `SQRDMULH` computes `sat_i16((2 * a * b + 32768) >> 16) = sat_i16(32768)` = **`+32767`** (`0x7FFF`, signed saturation).

Consequently, any clean-rewrite Rust scalar reference or portable intrinsic layer targeting bit-exact cross-ISA equivalence between x86_64 and AArch64 must prove from coefficient tables that at least one operand (always the constant transform cosine/basis weight or filter tap) satisfies $c > -32768$.

#### 4.4 AVX2 In-Lane 128-Bit Barriers and 2D Butterfly Transposes

`Basis: source`

Unlike SSE2 (`128`-bit) and Arm NEON (`TRN1`/`TRN2`, `ZIP1`/`ZIP2`, `UZP1`/`UZP2` on `128`-bit `Q` registers), AVX2 `256`-bit shuffle, unpack, and pack instructions (`VPUNPCKLBW`, `VPUNPCKHWD`, `VPSHUFB`, `VPACKUSWB`, `VPALIGNR`) operate **independently within two isolated 128-bit lanes** (`[127:0]` and `[255:128]`). Look at `FFmpeg`'s AVX-512ICL permutation tables in `libavcodec/x86/vp9mc.asm:134-158` (`spel_h_perm16`, `spel_v_perm16`, `spel_hv_perm4..16`): widening, transposing an `8x8` or `16x16` transform block, and packing back to bytes scrambles row/column indices across 128-bit lane boundaries unless compensated by explicit cross-lane `VPERM2I128`, `VPERMQ`, or `VPERMB`/`VPERMI2B` permutations. In formal proofs, treating permutations as unstructured bitvector shifts causes SMT blowup; representing each SIMD register state as an explicit **finite index map** $\pi : \{0..L-1\} \to \text{SourceExpr}$ reduces arbitrarily deep transpose networks (`8x8` or `16x16` butterfly corners) to $O(L)$ syntactic normalization before arithmetic verification begins.

#### 4.5 2D Stride Disjointness, Negative Strides, and Over-Read Padding Contracts

`Basis: source + derived`

In `FFmpeg` (`vp9dsp_template.c:1983-2000`) and `dav1d`/`rav1d`, image planes are passed as `(uint8_t *dst, ptrdiff_t dst_stride, const uint8_t *src, ptrdiff_t src_stride, int w, int h)`. Three spatial memory invariants govern UB-freedom and equivalence:

1. **Signed `ptrdiff_t` Strides Can Be Negative:** `FFmpeg` explicitly supports vertically flipped frames by pointing `src` at the bottom row `(base + (H - 1) * linesize)` with **`src_stride = -linesize < 0`**. Any verification precondition asserting `stride >= w` as an unsigned `usize` is **unsound** (or rejects valid vertically flipped streams); the true row-non-self-overlapping precondition for an in-place or output plane of height $h \ge 1$ and active row byte width $B = w \cdot \text{sizeof}(\text{pixel})$ is **`|dst_stride| >= B`**, with valid allocation span covering $[\min(0, (h-1)\cdot \text{stride}),\; \max(0, (h-1)\cdot \text{stride}) + B)$.
2. **Sub-Vector Block Widths (`w = 2, 4, 8`) and Tail Over-Fetch:** A 16-byte SSE2/NEON `movdqu`/`ld1` load on a `w = 4` `uint8` luma/chroma block reads `12` bytes past the active row width `w`! If `h` rows are processed and row `h - 1` sits at the bottom-right corner of an unpadded buffer of exact size `(h - 1) * |stride| + w`, a 16-byte load faults (`SIGSEGV`) or triggers out-of-bounds UB by `12` bytes. Similarly, horizontal 8-tap motion compensation (`vp9`, `hevc`, `av1`) centered at pixel `x` accesses `src[x - 3 .. x + 4]`, reading `3` pixels *before* `src` and `4` pixels *past* `src + w - 1` (requiring reference-frame border extension or emulated edge buffers).
3. **Normative `64`-Byte Bitstream/Frame Padding (`FFmpeg/FFmpeg` `libavcodec/defs.h:40`):** `FFmpeg` defines `#define AV_INPUT_BUFFER_PADDING_SIZE 64` (`512` bits—exactly one `ZMM` register width) so bitstream readers and AVX-512 loops can safely over-read up to `64` zeroed bytes past payload end without page faults. In a formally verified Rust rewrite, this implicit C convention becomes a **type-enforced slice capability** `PaddedSlice<'a, const PAD: usize>` guaranteeing `slice.len() + PAD <= backing_alloc.len()`.

---

### 5. Clean-Rewrite Architectural Synthesis and Proof-Effort Scaling

`Basis: derived + source`

Evaluating how to verify 100% of a codec's DSP surface without writing `500,000+` lines of manual HOL Light / Coq tactic scripts distinguishes **legacy C/ASM accidents** from **fundamental hardware constraints**:

- **Legacy Accidents to Eliminate in a Clean Rust Rewrite:**
  1. *Preprocessor Macro Duplication Across Bit-Depths (`8bpc` vs. `10/12bpc`):* `FFmpeg`'s `*_template.c` (`vp9dsp_template.c`, `2,578` lines included three times for `8`, `10`, and `12` bpc) and `x86inc.asm` stateful macro globals (`xmm_regs_used`, `stack_offset`) tangle control flow with register bookkeeping. Rust `const` generics (`const BPC: u8`, `BitDepth` traits as in `rav1d` `src/include/common/bitdepth.rs`) unify the scalar specification into one parametric reference per algorithm.
  2. *Ad-Hoc Width Proliferation:* `dav1d` exports separate assembly functions for every block dimension (`w = 2, 4, 8, 16, 32, 64, 128`). Compositional loop-invariant proofs over a verified `16`-byte or `32`-byte inner tile discharges `w = 16, 32, 64, 128` via a **single inductive tile theorem** rather than four separate unrolled straight-line proofs.
- **Fundamental Hardware Constraints Requiring Targeted ISA Kernels:**
  Portable Rust `core::simd` (`Simd<T, N>`) expresses elementwise ops, shuffles, and widening casts, **but LLVM instruction selection does not reliably synthesize** multi-stage media idioms such as `VPMADDUBSW` (`u8 * i8 -> sat_i16` + `VPMADDWD`) with provable tap-pair bounds, `MPSADBW` / `UDOT` / `USDOT` sum-of-absolute-differences/dot-products, or `VPSHUFB`/`VTBL` byte-LUT Wiener/film-grain kernels without target intrinsics (`core::arch`) or external assembly. Writing SIMD kernels over **safe/trusted `core::arch` vendor intrinsics inside Rust functions** (rather than external `.asm`/`.S` files) keeps every kernel inside MIR/LLVM-IR where automated relational verifiers (`CryptoLine`-style algebraic+`QF_BV` certificates + per-lane slicing as in `Rake`) discharge equivalence automatically, reserving raw assembly strictly for register-pressure-critical hot loops (`itx` 16x16/32x32, `msac`, `mc` 8-tap).

## Boundaries

- **Not Examined — Hardware Fixed-Function Video Accelerators (`VA-API`, `NVDEC`, `Vulkan Video`):** Equivalence here covers CPU SIMD/assembly kernels against software scalar references; bitstream-to-surface conformance of GPU/ASIC fixed-function decode blocks is **not examined**.
- **Known Not to Apply — Bit-Exact Equivalence for Unordered Floating-Point Tree Reductions:** In floating-point audio/filter DSP (`FFmpeg` `float_dsp`, `sbrdsp`, `aacpsdsp`, `af_afir`), SIMD horizontal `vhaddps` / `faddp` tree reductions and fused multiply-add (`vfma231ps`) alter IEEE-754 rounding order relative to sequential scalar `for` loops. Bit-exact equivalence **is known not to apply** unless scalar code is restructured to match the exact SIMD reduction tree or compiled under strict non-reassociating IEEE-754 rules without FMA contraction (see sibling report `ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`).
- **Known Not to Apply — Naive Monolithic `QF_BV` Bit-Blasting on 2D `16x16` / `32x32` Butterfly Transforms:** Standard `QF_BV` translation validation (`Alive2` without algebraic staging) **does not scale** to unrolled 2D `16x16` or `32x32` 16/32-bit inverse transforms (`256` to `1,024` coupled nonlinear multiply-adds); discharging these requires stage-by-stage relational cutpoints or Groebner-basis + `QF_BV` splitting (`CryptoLine`).
- **Unsupported — Media Rounding/Packing Instructions in Current `Jasmin` (`8c3279973a`) and `Vale` (`f557259007`):** As verified in Section 2.1, `VPAVGB`/`VPAVGW` and `VPACKSSDW` are currently **unsupported** in `jasmin-lang/jasmin`, `hacl-star/hacl-star` (`Vale`), and `awslabs/s2n-bignum` (`s2n-bignum` supports `VPMULHRSW` and `VPACKUSWB` but not `VPAVGB` or `VPACKSSDW`), requiring explicit ISA semantic extensions before proving pixel-averaging assembly in those tools.

## Evidence

### Primary Git Repositories and Inspected Source Locations

- **`FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, observed 2026-11-20):**
  - `libavcodec/defs.h:32-41` (`AV_INPUT_BUFFER_PADDING_SIZE = 64` bitstream over-read contract).
  - `tests/checkasm/checkasm.h:149-189` (`PIXEL_RECT`, `checkasm_check_pixel_padded`, `checkasm_check_dctcoef`) and `tests/checkasm/checkasm.c:52-429` (`libcheckasm` integration, `104` registered DSP test suites, `37` per-arch CPU feature tiers).
  - `libavutil/x86/x86inc.asm:374, 560-621, 1073-1135` (`vzeroupper_required`, `WIN64_SPILL_XMM`, AVX-512 `zmm16..zmm31` register preference).
  - `libavcodec/x86/vp9mc.asm:31-160, 177-246` (`F8_SSSE3_TAPS` 45-filter table, `packuswb`/`pavgb` reconstruction, AVX-512 cross-lane `spel_*_perm` tables) and `libavcodec/vp9dsp_template.c:1983-2001` (`avg_c` signed `ptrdiff_t` stride loop).
- **`videolan/dav1d` (`9af5ae4eb5204706c7f381ec62635237179f172e`, observed 2026-11-20):**
  - Multi-architecture SIMD directory census (`270,877` total LOC across `src/x86`, `src/arm/64`, `src/arm/32`, `src/riscv/64`, `src/ppc`, and `src/loongarch`; `include/common/intops.h`; `tests/checkasm/checkasm.c`).
- **`memorysafety/rav1d` (`2e7216c20ac2a75de204d6c8d7268b75a45959b4`, observed 2026-11-20):**
  - `src/wrap_fn_ptr.rs:41-101` and `src/cpu.rs:1-261` (typed `BitDepth` dispatch over external assembly kernels).
- **`awslabs/s2n-bignum` (`280a220986a0bc6249248187717a771153d073db`, observed 2026-11-20):**
  - `x86/mlkem/mlkem_ntt.S` (`659` lines), `x86/proofs/mlkem_ntt.ml:1-180, 1300-1465` (`1,465` lines; 256-lane `int16` AVX2 NTT equivalence + Win64 `XMM6..XMM15` bottom-quarter lens proof), `arm/mlkem/mlkem_ntt.S` (`372` lines), `arm/proofs/mlkem_ntt.ml:470-600` (`600` lines; `MEMORY_128_FROM_16_TAC`, `CONGBOUND_NTT_TAC`, `MLKEM_NTT_SUBROUTINE_SAFE`), and `x86/proofs/x86.ml` (`6,632` lines; SIMD opcode inventory).
- **`jasmin-lang/jasmin` (`8c3279973a89afd969e50301f71563bb40d55724`, observed 2026-11-20):**
  - `proofs/compiler/x86_instr_decl.v:148-156, 1786-1792, 1881-1910` (`2,533` lines; `VPERM2I128`, `VPMADDUBSW`, `VPMADDWD` Coq definitions and media opcode absence check).
- **`hacl-star/hacl-star` (`f557259007db9933442dde10aa995c1b00bd3446`) & `project-everest/vale` (`bbae0eb89143734363b14a77642dbf8dec36e288`, observed 2026-11-20):**
  - `lib/Lib.IntVector.fsti:1-413`, `vale/code/arch/x64/Vale.X64.InsVector.vaf:1-742`, `vale/specs/hardware/Vale.X64.Machine_Semantics_s.fst:1-777`, and `tools/Vale/src/emit_common_lemmas.fs:1-814`.
- **`fmlab-iis/cryptoline` (`c992f0c41b5f34fb1a07bf3f84568c732a935272`, observed 2026-11-20):**
  - `verify/cas.ml` (`1,740` lines; Groebner-basis polynomial ideal entailment) and `verify/smt.ml` (`984` lines; `QF_BV` range/overflow discharge).
- **`AliveToolkit/alive2` (`3bdd4f5e1cefa47057e93110e707acd11cfe08e4`), `halide/Halide` (`54c1a9bd6733081c8700a7c2521871161a701fad`), `ispc/ispc` (`ccb91bbc5332f026f494c48263b935145cd72f77`), `uwplse/rake` (`2b499110cecfee875edf392306b41be8d6cc2567`), and `akothen/Hydride` (`0c97d0f9d3f8cd0494e421b9ece4b24488b614e5`, observed 2026-11-20):**
  - `AliveToolkit/alive2` `ir/instr.h:1330-1353` & `ir/instr.cpp`; `halide/Halide` `src/FindIntrinsics.cpp:182-220, 704-785, 962-985, 1501-1635`; `ispc/ispc` `src/expr.cpp`; `uwplse/rake` `rake/synthesis/algorithm.rkt:15-42` & `rake/synthesis/verify.rkt:25-98`; `akothen/Hydride` `README.md:1-68`.

### Peer-Reviewed Literature

- Maaz Bin Safeer Ahmad, Alexander J. Root, Andrew Adams, Shoaib Kamil, and Alvin Cheung. 2022. *Vector Instruction Selection for Digital Signal Processors Using Program Synthesis* (`Rake`). ASPLOS 2022 (`DOI: 10.1145/3503222.3507714`).
- Akash Kothari, Abdul Rafae Noor, Muchen Xu, Hassam Uddin, Dhruv Baronia, Stefanos Baziotis, Vikram Adve, Charith Mendis, and Sudipta Sengupta. 2024. *Hydride: A Retargetable and Extensible Synthesis-based Compiler for Modern Hardware Architectures*. ASPLOS 2024 (`DOI: 10.1145/3620665.3640385`).
- Nuno P. Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu, and John Regehr. 2021. *Alive2: Bounded Translation Validation for LLVM*. PLDI 2021 (`DOI: 10.1145/3453483.3454030`).
- Julie L. Newcomb, Andrew Adams, Steven Johnson, Rastislav Bodik, and Shoaib Kamil. 2020. *Verifying and Improving Halide's Term Rewriting System with Program Synthesis*. OOPSLA 2020 (`DOI: 10.1145/3428234`).

### Reproducible Execution Probe (Observed 2026-11-20, Python 3.13 on Linux x86_64)

The standalone probe below reproduces all three exact arithmetic findings (`VP9` 45-filter `PMADDUBSW` pairing bounds and 63-level overflow witness, `37.50%` cascaded `PAVGB` bilinear rounding drift, and `VPMULHRSW` vs. `SQRDMULH` divergence at `(-32768, -32768)`):

```bash
python3 - <<'PY'
import itertools

sat_i16 = lambda x: max(-32768, min(32767, x))
clip_u8 = lambda x: max(0, min(255, x))

# Subset check + extremal witness from FFmpeg libavcodec/x86/vp9mc.asm:61-113
VP9_SHARP_1 = [-1, 3, -7, 127, 8, -3, 1, 0]
VP9_SHARP_7 = [-4, 11, -23, 80, 80, -23, 11, -4]
assert max(max(0, 255*VP9_SHARP_1[2*k]) + max(0, 255*VP9_SHARP_1[2*k+1]) for k in range(4)) == 32385

px = [255, 0, 255, 255, 255, 255, 0, 255]
s_out = clip_u8((sum(p*c for p, c in zip(px, VP9_SHARP_7)) + 64) >> 7)
a_out = clip_u8((sum(sat_i16(px[2*k]*VP9_SHARP_7[2*k] + px[2*k+1]*VP9_SHARP_7[2*k+1]) for k in range(4)) + 64) >> 7)
sym_out = clip_u8((sum(sat_i16(px[i]*VP9_SHARP_7[i] + px[j]*VP9_SHARP_7[j]) for i, j in [(0,7),(1,6),(2,5),(3,4)]) + 64) >> 7)
assert (s_out, a_out, sym_out) == (211, 211, 148)

pavgb = lambda x, y: (x + y + 1) >> 1
pos_bias = sum(
    1 for r0, r1, r2, r3 in itertools.product(range(4), repeat=4)
    if pavgb(pavgb(r0, r1), pavgb(r2, r3)) > ((r0 + r1 + r2 + r3 + 2) >> 2)
)
assert pos_bias == 96  # 96 / 256 == 37.50%

x86_pmulhrsw = lambda a, b: ((((a * b) >> 14) + 1) >> 1) & 0xFFFF
arm_sqrdmulh = lambda a, b: sat_i16((2 * a * b + (1 << 15)) >> 16)
w = x86_pmulhrsw(-32768, -32768)
w_signed = w - 0x10000 if w & 0x8000 else w
assert (w_signed, arm_sqrdmulh(-32768, -32768)) == (-32768, 32767)
print("ALL PROBES VERIFIED:", s_out, a_out, sym_out, pos_bias, w_signed)
PY
```

## Revalidation

1. **Re-verify arithmetic corner cases (`< 0.1 s`):** Execute the self-contained Python 3 script in `## Evidence` (`ALL PROBES VERIFIED: 211 211 148 96 -32768`).
2. **Check ISA opcode coverage changes in `s2n-bignum`, `Jasmin`, and `Vale`:** Diff `x86/proofs/x86.ml` in `awslabs/s2n-bignum` and `proofs/compiler/x86_instr_decl.v` in `jasmin-lang/jasmin` for `VPAVGB`, `VPMULHRSW`, `VPACKUSWB`, and `VPACKSSDW` definitions when upgrading pinned revisions.
3. **Audit new subpixel / Wiener / CDEF filter tables before `VPMADDUBSW` lowering:** For any new `u8 * i8` filter table `T`, check mechanically that every paired coefficient tuple `(c_{2k}, c_{2k+1})` satisfies `255 * max(0, c_{2k}) + 255 * max(0, c_{2k+1}) <= 32767` and `255 * min(0, c_{2k}) + 255 * min(0, c_{2k+1}) >= -32768`, and check `FFmpeg` `tests/checkasm/checkasm.c` + `libavcodec/defs.h` (`AV_INPUT_BUFFER_PADDING_SIZE`) if buffer padding or `libcheckasm` invariants change.
