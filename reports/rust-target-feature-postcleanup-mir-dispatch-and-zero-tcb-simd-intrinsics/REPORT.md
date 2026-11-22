# Rust `#[target_feature]` Runtime Dispatch, `Runtime(PostCleanup)` MIR Lowering, and Zero-TCB-Bloat SIMD Intrinsic Verification

## Summary

Verifying real Rust SIMD code at pre-optimization `Runtime(PostCleanup)` MIR (`-Zmir-opt-level=0 -Zmir-preserve-ub -Zinline-mir=no`) exposes four concrete semantic facts and one dominant verification architecture:

1. **RFC 2396 `safe_target_features` capture trap:** In `rustc`, a safe function annotated with `#[target_feature(enable = "...")]` sets `codegen_fn_attrs.safe_target_features = true` while `fn_sig.safety()` still reports `Safety::Unsafe`. Treating `fn_sig.safety()` as a boolean `isUnsafe` flag conflates hardware-capability preconditions with arbitrary `unsafe fn` preconditions; verifiers must instead classify functions with a three-way `FnSafetyKind` (`safe`, `safeTargetFeatures`, `unsafe_`) paired with an explicit `requiredFeatures : CpuFeatureSet`.
2. **`Runtime(PostCleanup)` MIR shape of `core::arch` and `std_detect`:** Under `-Zinline-mir=no`, `core::arch` SIMD operations remain ordinary `TerminatorKind::Call` sites to wrapper functions whose bodies lower to (a) plain MIR deref / `ptr::read_unaligned` / `ptr::write_unaligned` / `transmute`, (b) portable `#[rustc_intrinsic]` `simd_*` intrinsics, and (c) architecture-specific `#[link_name = "llvm.<arch>.*"]` intrinsics. AVX-512 opmasks (`__mmask8`/`16`/`32`/`64`) lower directly to plain integer types (`u8`/`u16`/`u32`/`u64`) in MIR. `std::arch::is_x86_feature_detected!("avx2")` expands to a compile-time `cfg!` boolean branch short-circuiting a call to `std_detect::detect::arch::x86::__is_feature_detected::avx2`.
3. **Zero-TCB-bloat SIMD architecture (layered hybrid):** Keeping a lane-structured `MirTy.simd` / `Val.simd` representation (preserving per-lane pointer provenance and `AllocByte` initialization masks, matching `lean-miri`'s `IntrinsicSimd` and `IntrinsicVectorMachine`), a fixed ~12-op portable `simd_*` core, and **one** generic data-driven `ArchIntrinsicContract` seam adds **zero** trusted-kernel operational-semantics LOC per new hardware instruction while allowing platform intrinsics, inline `asm!`, and compiled `.o` kernels to share one Pass-2 ISA correspondence bus (`s2n-bignum`+XED, SoftFloat, `sail-arm`, `sail-riscv-lean`, `Wasm SpecTec`, and `lean-miri`).
4. **Live `AeneasVerif/kraken` SIMD coverage boundary:** At commit `4a6ec0c61b189c53911903c4c0d129d6e78c05f6`, Kraken's `Kraken/X64/Syntax.lean` defines 25 `AvxOperation` constructors (5 FP SSE/AVX, 7 SSE integer, 4 AVX moves, 3 SHA-256, 6 AVX-512 32-bit/ternlog ops) with **0 opmask registers (`k0`–`k7`)** and **0 AArch64 NEON/SVE instructions** (`Kraken/AArch64/Syntax.lean` is scalar GPR-only). Kraken therefore cannot serve as a standalone turnkey SIMD oracle for opmask AVX-512 or AArch64 NEON/SVE2 workloads today.

## Applicability

These findings apply to:
- **Pre-optimization `Runtime(PostCleanup)` MIR verifiers** targeting Rust 1.86+ (RFC 2396 / `target_feature_11` safe `#[target_feature]` calls), empirically probed on `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` for target `x86_64-unknown-linux-gnu` with `-C opt-level=0 -Zmir-opt-level=0 -Zmir-preserve-ub -Zinline-mir=no`.
- **Anneal's MIR capture, trusted Lean 4 semantics, and vendored `lean-miri` interpreter** as observed at `google/zerocopy` commit `d2f63ce1c3c04ffabb4442b028caf612c9508387` (`anneal/`).
- **Runtime IFUNC SIMD dispatch crates** following `vsimd` `0.8.0`'s `AtomicPtr<()>` lazy-resolution pattern (`Nugine/simd`, `vsimd/src/macros.rs`).
- **Kraken ISA coverage claims** specifically for `AeneasVerif/kraken` commit `4a6ec0c61b189c53911903c4c0d129d6e78c05f6`.

The MIR lowering observations hold specifically when MIR inlining is disabled (`-Zinline-mir=no`); enabling MIR inlining or capturing `Runtime(Optimized)` MIR changes call structure and erases UB checks and storage/borrow boundaries.

## Findings

### 1. Per-Function `#[target_feature]` and Runtime Dispatch Lowering in `Runtime(PostCleanup)` MIR

Basis: source + execution + normative

#### 1.1 RFC 2396 / Rust 1.86 `safe_target_features` Capture Trap
In `google/zerocopy@d2f63ce1c3c04ffabb4442b028caf612c9508387`, `anneal/trusted/rustc-capture/src/extract.rs:560–575` refuses every item with `!target_features.is_empty() || *safe_target_features` because `rustc_hir::HeaderSafety::SafeTargetFeatures` causes `tcx.fn_sig(def).safety()` to return `Safety::Unsafe` even when the source function is declared safe (`#[target_feature(enable = "avx2")] pub fn f(...)`). If capture maps `fn_sig.safety()` directly to `Body.isUnsafe : Bool`, verification would silently grant a safe `#[target_feature]` function an arbitrary user-supplied `Specs.safety` precondition instead of restricting its entry assumption strictly to CPU feature availability.

Sound capture therefore requires a three-way `FnSafetyKind`:
- `safe`: no `unsafe fn` qualifier, `requiredFeatures = ∅`, no custom `Specs.safety`.
- `safeTargetFeatures`: `codegen_fn_attrs.safe_target_features == true`; entry assumes **only** `requiredFeatures.subset st.cpuCaps`, with no arbitrary `Specs.safety`. Calling a `safeTargetFeatures` callee from a caller whose `requiredFeatures` is a superset discharges the call obligation statically, matching Rust 1.86's safe intra-feature call rule.
- `unsafe_`: genuine `unsafe fn`; entry assumes `requiredFeatures.subset st.cpuCaps ∧ Specs.safety body.identity q`.

#### 1.2 Observed `Runtime(PostCleanup)` MIR for `core::arch`, `__mmask64`, and `is_x86_feature_detected!`
Running `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` on `support/probe_simd_postcleanup_mir.rs` with `-C opt-level=0 -Zmir-opt-level=0 -Zmir-preserve-ub -Zinline-mir=no` produces the four golden dumps in `support/mir/`:
1. **AVX-512 opmasks are plain integers in MIR:** `pub fn avx512_ops(mask: __mmask64, idx: __m512i, v: __m512i) -> __m512i` lowers to `fn avx512_ops(_1: u64, _2: std::arch::x86_64::__m512i, _3: std::arch::x86_64::__m512i) -> std::arch::x86_64::__m512i`. Similarly, `__mmask8`/`16`/`32` are type aliases for `u8`/`u16`/`u32`; no dedicated opmask `MirTy` is required.
2. **Intrinsics appear as `TerminatorKind::Call` to `core::arch` wrappers:** `_mm256_loadu_si256`, `_mm256_load_si256`, `_mm256_shuffle_epi8`, `_mm256_add_epi8`, `_mm512_maskz_expand_epi8`, and `_mm512_permutexvar_epi8` are preserved verbatim as direct calls in `PostCleanup` MIR. Inside `core::arch`, those wrappers lower strictly into:
   - ordinary MIR memory/cast operations (`*ptr` aligned deref for `_mm256_load_si256`, `ptr::read_unaligned`/`write_unaligned` for `loadu`/`storeu`, `transmute`);
   - portable `#[rustc_intrinsic]` `simd_*` intrinsics (`simd_add`, `simd_shuffle`, `simd_select_bitmask`, `simd_masked_load`/`store`, `simd_cast`);
   - architecture-specific `extern "unadjusted"` `#[link_name = "llvm.<arch>.*"]` intrinsics (`llvm.x86.avx2.pshuf.b`, `llvm.x86.avx512.mask.expand.b.512`, `llvm.aarch64.neon.tbl1.v16i8`).
3. **Runtime feature detection lowering:** `std::arch::is_x86_feature_detected!("avx2")` lowers to:
   ```text
   bb0: { _2 = const false; switchInt(move _2) -> [0: bb1, otherwise: bb3]; }
   bb1: { _3 = std_detect::detect::arch::x86::__is_feature_detected::avx2() -> [return: bb2, unwind continue]; }
   bb2: { switchInt(move _3) -> [0: bb5, otherwise: bb3]; }
   bb3: { _4 = safe_tf_caller(move _5) -> [return: bb4, unwind continue]; }
   ```
   Under `-C target-feature=+avx2`, `_2` is `const true`, bypassing `bb1`.

#### 1.3 Sound Feature-State, One-Directional Detection, ABI Coercion, and IFUNC Dispatch Model
Basis: source + derived

1. **Effective architectural + OS capability set (`CpuFeatureSet`):** Machine state carries an immutable process-wide `cpuCaps : CpuFeatureSet` (`arch`, normalized `features`, and scalable vector multiplier `vscale : Nat` with `1 ≤ vscale ≤ 16` for SVE/RVV; `vscale = 1` for fixed vectors). Membership `f ∈ st.cpuCaps` means **effective architectural and OS-enabled execution** (e.g., on x86-64, `"avx2"` includes OS `XCR0[2:1] == 0b11` `OSXSAVE`, and `"avx512f"` includes `XCR0[7:5] == 0b111` opmask+ZMM state saving; raw `CPUID` alone is insufficient because executing EVEX instructions without OS `XCR0` enablement raises `#UD`).
2. **Static `-C target-feature` receipt accounting:** Crate-level static features (`tcx.sess.target_features`) constrain `initState` (`p.staticTargetFeatures.subset q.cpuCaps`), and any feature beyond the target triple baseline must be itemized in verification receipt assumptions (`assumed_target_features`) as a deployment-environment precondition.
3. **One-directional `DetectFeature` postcondition:** Modeling `std_detect::detect::arch::*::__is_feature_detected::<feat>` as a demonic boolean choice permits `ret = false` unconditionally and permits `ret = true` **only** when `impliesClosure(feat) ⊆ st.cpuCaps`. One-directionality (`ret = true → feat ∈ cpuCaps`, not `↔`) preserves soundness when emulation, Miri, or OS policy conservatively disables a feature.
4. **ABI safety on `#[target_feature]` function-pointer coercions:** Passing non-baseline SIMD vector types (such as `__m256i`) by value across a mismatched-feature function-pointer boundary causes calling-convention mismatch UB (e.g., `ymm0` vs. indirect stack passing). Capture must verify that any `#[target_feature]` function coerced to a `FnPtr` either avoids non-baseline by-value SIMD parameters/returns or carries matching feature requirements in the `FnPtr` ABI signature.
5. **Atomic IFUNC dispatch (`vsimd` `0.8.0`, `src/macros.rs:101–131`):** `vsimd::dispatch!` initializes `static IFUNC: AtomicPtr<()> = AtomicPtr::new(init_ifunc as *mut ())`, lazily resolves a target function `f = resolve()`, executes `IFUNC.store(f as *mut (), Relaxed)`, and in `auto` runs `core::mem::transmute::<*mut (), unsafe fn(...)>(IFUNC.load(Relaxed))`. Extending indirect-call capabilities (`CodeCap`) with `reqFeatures : CpuFeatureSet` discharges this pattern via a single global invariant: every pointer stored in `IFUNC` is a valid `CodeCap` for the dispatch signature with `cap.reqFeatures.subset st.cpuCaps`. Because `init_ifunc` has `reqFeatures = ∅`, `resolve()` guards every specialized branch with `detectFeature` or static `cfg!(target_feature)`, `st.cpuCaps` is process-immutable, and code pointers refer to static immutable `.text`, concurrent first-call races with `Ordering::Relaxed` preserve the invariant without `Acquire`/`Release` heap synchronization.

---

### 2. Existing `lean-miri` SIMD Semantics vs. `AeneasVerif/kraken` ISA Coverage

Basis: source

#### 2.1 Vendored `lean-miri` Coverage (`google/zerocopy@d2f63ce1c3c04ffabb4442b028caf612c9508387`)
Direct inspection of `anneal/vendor/lean-miri/Miri/Interpreter/` shows substantial existing Lean 4 SIMD operational semantics:
- **`IntrinsicSimd.lean` (531 LOC):** Models Rust's portable `#[rustc_intrinsic]` SIMD operations (`simd_add/sub/mul/div/rem/shl/shr/and/or/xor/eq..ge`, `simd_insert/extract/splat`, `simd_neg/fabs/ceil/floor/round/trunc/ctlz/ctpop/cttz/bswap/bitreverse`, `simd_saturating_{add,sub}`, `simd_arith_offset` pointer lanes, `simd_cast`/`simd_as`/`simd_cast_ptr`/provenance casts, `simd_reduce_*`, `simd_select_bitmask`, `simd_masked_load`/`store`, and `SimdAlignment.{unaligned,element,vector}` checks). Crucially, `elementToBool` (lines 75–79) enforces that mask lanes are strictly `0` or `-1` (all-zero or all-one bits), faulting with UB otherwise; `floatMinMax` (lines 84–93) explicitly models `chooseEqualFloatRight` (`-0.0` vs. `+0.0`) and `FloatOps.adjustNaN`.
- **`IntrinsicVectorMachine.lean` (137 LOC):** Retains per-lane field/index projection over `RuntimePlace` so initialization (`InitMask`), pointer provenance (`Option Provenance`), and borrow hooks are enforced at each lane read/write rather than flattened into a provenance-free bitvector.
- **`IntrinsicX86.lean` + `IntrinsicX86/DispatchVector.lean` (10 submodules):** Dispatches `llvm.x86.*` across SSE2, SSE3, SSSE3, SSE4.1, SSE4.2, AVX, AVX2, AVX-512F/BW/VL/VBMI/VNNI, AES, SHA, GFNI, BMI, PCLMULQDQ, and CRC32—checking target features per intrinsic (e.g., `avx2.pshuf.b`, `avx2.pmadd.ub.sw`, `avx2.packuswb`, `avx512.permvar.qi.512`, `avx512.vpermi2var.qi.512`, `avx512.pternlog.*`, `avx512.vpdpbusd.*`). Notably absent from `DispatchVector.lean` at this commit: AVX-512 VBMI2 `avx512.mask.expand.b.512` (`VPEXPANDB`) and VBMI `avx512.vpmultishift.qb.512` (`VPMULTISHIFTQB`).
- **`IntrinsicArchitecture.lean` (308 LOC):** Dispatches AArch64 `llvm.aarch64.*` including `neon.tbl1..4.{v8i8,v16i8}` (table lookup with OOB zeroing, lines 171–194), `neon.addp`, `neon.umaxp.v16i8`, `neon.uaddlp`, `neon.sqdmulh`, `neon.pmull64`, `crc32*`, and `crypto.sha256*`.

#### 2.2 Live `AeneasVerif/kraken` Coverage (`4a6ec0c61b189c53911903c4c0d129d6e78c05f6`)
Direct inspection of `Kraken/X64/Syntax.lean:251–282` and `Kraken/AArch64/Syntax.lean` establishes:
- **X64 (`AvxOperation`, 25 constructors total):** 5 FP SSE/AVX (`movups`, `vmovups`, `movaps`, `subps`, `addps`), 7 SSE integer (`movdqu`, `movdqa`, `paddd`, `pshufb`, `pshufd`, `palignr`, `pblendw`), 4 AVX moves (`vmovdqu`, `vmovIn`, `vmovOut`, `vmovq`), 3 SHA-256 (`sha256rnds2`, `sha256msg1`, `sha256msg2`), and 6 AVX-512 32-bit/ternlog ops (`vmovdqu32`, `vmovdqa32`, `vpaddd`, `vprord`, `vpsrld`, `vpternlogd`).
- **Gaps:** **0 opmask registers (`k0`–`k7`)**, **0 masked AVX-512 operations**, **0 VBMI/VBMI2 byte permute/expand/multishift ops**, and **0 AArch64 NEON/DotProd/I8MM/SVE/SME instructions** (`Kraken/AArch64/Syntax.lean` defines only scalar `XReg`/`MemWidth` `W8..W64` operations).

---

### 3. Model Refinement: Zero-TCB-Bloat SIMD Intrinsic Semantics

Basis: derived + source

Comparing three architectural designs against minimal trusted-base growth, Rust memory/provenance fidelity, and multi-ISA generality:

| Architecture | Trusted Core (`trusted/lean/`) | Off-TCB / Pass-2 Layer | Discriminating Trade-Offs & Counterexamples |
| :--- | :--- | :--- | :--- |
| **Fixed Lane-Algebra Core** | `MirTy.simd`, `Val.simd`, `CpuFeatureSet`, plus ~16 combinators (`laneMap`, `laneLookup`, `laneCompactExpand`, etc.); capture translates `llvm.*` to combinators. | Algebraic rewrite lemmas; Pass-2 checks combinator lowering. | **Fails zero-TCB-growth & capture-TCB goals:** Cryptographic/bit-matrix ops (`AESENC`, `SHA256RNDS2`, `PCLMULQDQ`, `VPMULTISHIFTQB`, `VPDPBUSD`) and dynamic-length RVV (`vsetvl`) force continual combinator expansion, and translating `llvm.*` inside `rustc-capture` puts every opcode mapping into the capture TCB. |
| **Flat Machine-Instruction Seam** | Single `IsaCall` terminator lowering `core::arch`, inline `asm!`, and compiled `.o` kernels through one flat-memory + physical-register interface. | All ISA specs in Pass-2 vendor anchors (`s2n-bignum`, `sail-arm`, `sail-riscv`, `SpecTec`). | **Fails MIR memory/SSA fidelity:** In `PostCleanup` MIR, `core::arch` operates on typed SSA values (`__m256i`, `Simd<*const T, N>`) and Rust `MemoryState` (`InitMask`, alignment UB, Tree Borrows), not physical registers and flat `BitVec 64 → UInt8` memory. Flattening breaks pointer provenance and alignment/`MaybeUninit` checks. |
| **Layered Lane-Structured MIR + Data-Driven `ArchIntrinsicContract` Seam (Recommended)** | (1) `MirTy.simd (elem : MirTy) (shape : SimdShape) (alignLog2 : Nat)` + lane-structured `Val.simd`; (2) `CpuFeatureSet`, `FpCtrlState`, `FnSafetyKind`; (3) ~12 portable `#[rustc_intrinsic]` `simd_*` ops matching `lean-miri` `IntrinsicSimd`; (4) **one** generic `TerminatorKind.archIntrinsic` dispatching `ArchIntrinsicContract` (~220–280 TCB LOC fixed; **0 LOC per new opcode**). | (1) `0`-TCB `BitVec` pack/unpack bridge lemmas for fast integer SIMD proofs (e.g., F₂-linear / LRAT checkers); (2) declarative `ArchIntrinsicContract` table entries; (3) **shared Pass-2 ISA correspondence bus** verifying `ArchIntrinsicContract`, inline `asm!`, and `.o` leaves against one pinned vendor ISA anchor set (`s2n-bignum`+XED, SoftFloat, `sail-arm`, `sail-riscv-lean`, `SpecTec`, `lean-miri`). | **Dominates across all axes:** Preserves exact Rust MIR provenance/`InitMask`/alignment semantics, adds zero trusted operational-semantics LOC per new instruction, scales to opmasks/NEON/SVE2/RVV/Wasm/crypto, and unifies receipt accounting via explicit correspondence tiers (`isa_correspondence_proved` vs. `difftest_validated_only` logged in `unproved_arch_intrinsics[]`). |

#### 3.1 Stress-Testing the Layered Hybrid Across Six Instruction Classes
1. **Fixed 128/256/512-bit integer SIMD:** `Val.simd` preserves lane structure in `Trusted.MirModel`; `0`-TCB theory lemmas pack initialized, provenance-free integer vectors into `BitVec 128/256/512` for algebraic or bit-blasted proofs. Crucially distinguishes in-lane 128-bit shuffles with MSB-zeroing (`_mm256_shuffle_epi8` / `VPSHUFB`) from cross-lane modulo-64 permutes (`_mm512_permutexvar_epi8` / `VPERMB`).
2. **AVX-512 opmasks `k0`–`k7` (zero- and merge-masking):** Mask operands are ordinary `u8`/`u16`/`u32`/`u64` MIR scalars. Critically separates **by-value masking** (`_mm512_mask_blend_epi8(k, a, b)`, where Rust calling semantics require **every** lane of both `a` and `b` to be initialized before the call) from **memory-masked loads/stores** (`_mm512_maskz_loadu_epi8(k, p)` / `simd_masked_load`, where `ArchMemPolicy.maskedMem` does not dereference, bounds-check, or `InitMask`-check inactive lanes `k[i] == 0`).
3. **AArch64 NEON multi-vector table lookups (`vtbl`/`vqtbl1..4`, `vtbx`/`vqtbx`):** Directly modeled as pure `ArchIntrinsicContract` entries matching `lean-miri` `IntrinsicArchitecture.tableLookup` (zeroing on `idx ≥ 16 * k` for `vtbl`/`vqtbl` vs. preserving fallback lane for `vtbx`/`vqtbx`).
4. **Scalable vectors (`SVE2` and `RVV 1.0`):** `SimdShape.scalable baseLanes` quantifies proofs universally over `st.cpuCaps.vscale` (`1 ≤ vscale ≤ 16`, i.e., 128–2048 bits). For RVV 1.0, dynamic active vector length `vl` returned by `vsetvl` is carried explicitly as a scalar operand into predicated ops.
5. **Wasm `SIMD128` (+ relaxed SIMD):** Relaxed SIMD operations (`f32x4.relaxed_madd`, `i8x16.relaxed_swizzle` for `idx ≥ 16`) use demonic `Choice` to quantify over all implementation-permitted outcomes specified by Wasm SpecTec.
6. **Floating-point SIMD & FMA:** Governed by `FpEffectPolicy.requiresCanonicalCtrl` (or `dynamicRounding` for EVEX embedded rounding) over unified `FpCtrlState` and SoftFloat.

---

### 4. SIMD Memory, Alignment, `MaybeUninit`, `MXCSR`/`FPCR`, and IEEE-754 Edge Cases

Basis: source + normative + derived

1. **Alignment UB vs. unaligned and overlapping stores:** Anneal's `Trusted.MirSemantics.Memory.isAligned` (`Memory.lean:185–245`) enforces both `alignLog2 ≤ a.alignLog2` and `offset % 2^alignLog2 == 0` on every non-empty `readBytes`/`writeBytes`. Consequently:
   - `_mm256_load_si256` / `_mm512_load_si512` require `alignLog2 = 5` (32B) / `6` (64B) and fault with `FaultKind.undefined` on misalignment;
   - `_mm256_loadu_si256` / `_mm256_storeu_si256` / `vld1q_u8` / `vst1q_u8` use `alignLog2 = 0` (1B);
   - Sequential overlapping unaligned stores (such as 16B stores at `dst` and `dst + 12` in SIMD base64 codecs) require only in-bounds slack (`dst + 28 ≤ buf.len`) and no non-overlapping precondition (unlike `copy_nonoverlapping`).
2. **`MaybeUninit` vector lanes:** Loading even one `AllocByte.uninit` byte into a typed `#[repr(simd)]` integer/float vector (`__m256i`) is immediate UB (`FaultKind.undefined`). Raw `MaybeUninit<__m256i>` buffers retain per-byte `.uninit` markers via `Val.bytes (List AllocByte)` until initialized; only memory-masked loads (`simd_masked_load`, `_mm512_maskz_loadu_*`) suppress reading uninitialized or out-of-bounds memory at inactive mask positions.
3. **`MXCSR` / `FPCR` non-volatile vs. volatile split:** Model `FpCtrlState` with:
   - **Non-volatile control (`FpNonVolatileCtrl`):** rounding mode (`RNE`), `FTZ = false`, `DAZ = false`, and all FP exception masks enabled (`MXCSR & 0xffc0 == 0x1f80` on x86-64; unmasked exceptions cause hardware `#XM` / `SIGFPE` traps on division by zero or invalid operations). Rust assumes canonical non-volatile control at every FP operation and FFI entry.
   - **Volatile sticky flags (`BitVec 6`):** `MXCSR[5:0]` / `FPSR` / `fcsr.fflags` are mutated by FP ops and are **not** callee-saved.
   - **Optional streaming state:** `smeZaActive : Bool` for AArch64 `FEAT_SME`.
   Integer-only SIMD (`FpEffectPolicy.none`) imposes zero `FpCtrlState` obligation.
4. **IEEE-754 NaN and FMA nondeterminism:** Following Rust/Miri (`IntrinsicSimd.lean:84–93`), FP SIMD operations returning `NaN` select nondeterministically among quiet-NaN bit patterns (`adjustNaN`), `min`/`max` on `(-0.0, +0.0)` selects nondeterministically (`chooseEqualFloatRight`), and `simd_relaxed_fma` chooses nondeterministically between fused single-rounding and unfused two-rounding (`fuseMulAdd`). Cross-backend FP SIMD equivalence (`SSE4.2 ≡ AVX2+FMA ≡ AVX-512 ≡ NEON ≡ SIMD128 ≡ Scalar`) must therefore be stated as finite-domain ULP / NaN-class equivalence rather than raw bit equality on NaNs.

## Boundaries

- **Not examined:**
  - `rustc` `Runtime(PostCleanup)` MIR lowering on `aarch64-unknown-linux-gnu`, `riscv64gc-unknown-linux-gnu`, and `wasm32-unknown-unknown` targets was not executed on this x86-64 host; the `std_detect` / `core::arch` lowering claims for non-x86 targets are derived from `core::arch` / `std_detect` architecture and `lean-miri`'s `IntrinsicArchitecture.lean`, not host execution.
  - Non-LLVM backends (`rustc_codegen_cranelift`, `rustc_codegen_gcc`) and custom LLVM pass interaction with `#[target_feature]` inlining were not examined.
- **Known not to apply:**
  - The observed `Runtime(PostCleanup)` MIR structure does **not** apply to `Runtime(Optimized)` MIR or builds where `-Zinline-mir=yes` inlines `core::arch` wrappers before capture.
  - Kraken (`AeneasVerif/kraken@4a6ec0c61b189c53911903c4c0d129d6e78c05f6`) is known not to cover AVX-512 opmask registers (`k0`–`k7`), AVX-512 VBMI/VBMI2 byte permute/expand/multishift instructions, or any AArch64 NEON/SVE/SME instructions.
  - Raw bit-for-bit cross-backend equivalence does **not** hold in general for IEEE-754 FP SIMD outputs producing `NaN`, `min`/`max` of `±0.0`, or relaxed FMA.
- **Unknown / open:**
  - Exact TCB LOC count (~220–280 LOC) for implementing the layered hybrid in Anneal's `Trusted.MirAst`/`MirModel`/`MirSemantics` is an engineering estimate until mechanized in Lean 4.
  - Whether `std_detect`'s internal `AtomicUsize` cache initialization under concurrent first-call execution has any target-specific ordering edge cases on non-x86 platforms was not audited beyond treating `std_detect` as a trusted `DetectFeature` intrinsic with one-directional soundness.

## Evidence

- **Anneal MIR capture & trusted semantics (source, observed `2026-11-22`):**
  - `google/zerocopy` @ `d2f63ce1c3c04ffabb4442b028caf612c9508387`:
    - `anneal/trusted/rustc-capture/src/extract.rs:560–575` (`target_features` / `safe_target_features` refusal and `HeaderSafety::SafeTargetFeatures` citation) and `:698–718` (`#[rustc_intrinsic]` refusal).
    - `anneal/trusted/lean/Trusted/MirAst/Body.lean:90–96` (`Body.isUnsafe`), `Trusted/MirModel.lean:86–127` (`AllocByte`, `Val`), `Trusted/MirSemantics/Memory.lean:185–260` (`isAligned`, `readBytes`, `writeBytes`, `writeUninit`).
    - `anneal/vendor/lean-miri/Miri/Interpreter/IntrinsicSimd.lean:1–320`, `IntrinsicVectorMachine.lean:1–137`, `IntrinsicX86.lean:1–84`, `IntrinsicX86/DispatchVector.lean:1–160`, `IntrinsicArchitecture.lean:1–250`.
- **Empirical `rustc` `Runtime(PostCleanup)` MIR probe (execution, observed `2026-11-22`):**
  - Toolchain: `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` on `x86_64-unknown-linux-gnu`.
  - Preserved input: `support/probe_simd_postcleanup_mir.rs`.
  - Preserved golden MIR outputs: `support/mir/probe.{safe_tf_add,safe_tf_caller,avx512_ops,dispatch_entry}.runtime-post-cleanup.after.mir`.
  - Command:
    ```console
    rustc --edition=2024 --crate-type=lib -C opt-level=0 -Zmir-opt-level=0 -Zmir-preserve-ub -Zinline-mir=no \
      -Zdump-mir='safe_tf_add|safe_tf_caller|avx512_ops|dispatch_entry' \
      -Zdump-mir-dir=/tmp/mir support/probe_simd_postcleanup_mir.rs -o /tmp/libprobe.rlib
    ```
- **Runtime IFUNC dispatch (source, observed `2026-11-22`):**
  - `Nugine/simd` crate `vsimd` `0.8.0`, `src/macros.rs:55–180` (`macro_rules! dispatch`, `static IFUNC: AtomicPtr<()>`, `Relaxed` load/store + `core::mem::transmute`).
- **Kraken ISA coverage (source, observed `2026-11-22`):**
  - `AeneasVerif/kraken` @ `4a6ec0c61b189c53911903c4c0d129d6e78c05f6`: `Kraken/X64/Syntax.lean:251–282` (`inductive AvxOperation`, 25 constructors, 0 opmask registers) and `Kraken/AArch64/Syntax.lean:13–354` (scalar GPR/load/store/branch only, 0 NEON/SVE constructors).

## Revalidation

1. **Revalidate `rustc` `Runtime(PostCleanup)` MIR lowering on a newer compiler:** Re-run the exact `rustc` command in **Evidence** against `support/probe_simd_postcleanup_mir.rs` and diff the four `*.runtime-post-cleanup.after.mir` files against `support/mir/`. Verify: (a) `__mmask64` still lowers to `u64`, (b) `core::arch` SIMD calls remain uninlined `TerminatorKind::Call` sites under `-Zinline-mir=no`, and (c) `is_x86_feature_detected!("avx2")` still expands to a `cfg!` boolean branch gating `std_detect::detect::arch::x86::__is_feature_detected::avx2`.
2. **Revalidate `safe_target_features` handling in `rustc`:** Check `compiler/rustc_middle/src/middle/codegen_fn_attrs.rs` (`target_features`, `safe_target_features`) and `compiler/rustc_hir/src/hir.rs` (`HeaderSafety::SafeTargetFeatures`) to confirm whether `FnHeader::safety` still maps `SafeTargetFeatures` to `Safety::Unsafe`.
3. **Revalidate `AeneasVerif/kraken` SIMD coverage:** Inspect `Kraken/X64/Syntax.lean` (`inductive AvxOperation` and register definitions for `k0`–`k7`) and `Kraken/AArch64/Syntax.lean` (for `VReg`/`NEON`/`SVE` constructors) at the target Kraken commit.
4. **Revalidate `lean-miri` intrinsic coverage:** Inspect `IntrinsicX86/DispatchVector.lean` (`def vectorSpec`) and `IntrinsicArchitecture.lean` (`def aarch64`) for newly added AVX-512 VBMI/VBMI2 or AArch64 NEON/SVE intrinsics.
