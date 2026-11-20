# Object-Level Assembly Lifting, core::arch LLVM Lowering, and Pass-2 ISA Correspondence for Media SIMD Kernels

## Summary

Verifying media codec SIMD and bitstream kernels at the Rust Mid-Level Intermediate Representation (MIR) boundary leaves an unverified lowering gap whenever functions cross into `#[target_feature]` `core::arch` vendor intrinsics, `core::arch::asm!`, or external NASM/GAS object files. In `rust-lang/stdarch` (`ca26a96d57b295dcd927622877242940a0f3c02e`), intrinsics such as `_mm256_maddubs_epi16` lower through `#[link_name = "llvm.x86.avx2.pmadd.ub.sw"]` inside `unsafe extern "unadjusted"` blocks (`crates/core_arch/src/x86/avx2.rs:1858-1860, 3744-3745`) to opaque `TerminatorKind::Call` nodes in post-cleanup MIR, delegating vector layout, constant-pool formation, instruction selection, upper-lane `vzeroupper` hygiene, and callee-saved register preservation to `rustc_codegen_llvm` and LLVM.

Closing this gap uniformly for both `#[target_feature]` `core::arch` Rust kernels and external NASM/GAS kernels requires **relocatable object-level binary lifting** (`--emit=obj` / `.o` / `.obj`) paired with **sandboxed Pass-2 per-opcode ISA correspondence**:

1. **Object-level section and relocation binding is mandatory even for pure intrinsic code:** Empirical compilation on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM 22.1.6) demonstrates that LLVM synthesizes anonymous read-only constant-pool sections (`.rodata.cst8`/`.rodata` on ELF64, `__TEXT,__literal8` on Mach-O, `.rdata` COMDAT on Win64 COFF) for constant SIMD tap vectors and accesses them via PC-relative relocations (`R_X86_64_PC32` with `-4` addend, `X86_64_RELOC_SIGNED`, `IMAGE_REL_AMD64_REL32`, `R_AARCH64_ADR_PREL_PG_HI21` + `R_AARCH64_LDST128_ABS_LO12_NC`, and `R_RISCV_PCREL_HI20` + `R_RISCV_PCREL_LO12_I`). Lifting `.text` bytes without relocation resolution against immutable constant sections misbinds filter weights to zeroed instruction displacements.
2. **Control-flow integrity (CFI) markers and Win64 `.pdata`/`.xdata` metadata govern indirect-call and unwind soundness:** FFmpeg's `libavutil/x86/x86inc.asm` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, lines `910-918`) emits `GNU_PROPERTY_X86_FEATURE_1_SHSTK` (`0x2`) without `GNU_PROPERTY_X86_FEATURE_1_IBT` (`0x1`) or `endbr64` (`F3 0F 1E FA`), causing GNU `ld`/`lld` bitwise-AND property merging to silently strip CET-IBT protection from any mixed Rust+NASM shared library. On Win64, `x86inc.asm` (`lines 500-621`) spills `xmm6`/`xmm7` into caller shadow space (`[rsp+8]`/`[rsp+24]`) and `xmm8..xmm15` onto the stack without emitting `.pdata` `RUNTIME_FUNCTION` or `.xdata` `UNWIND_INFO` records, violating the Microsoft PE32+ x64 unwind contract. On AArch64, `leanprover/LNSym` (`49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`, `Arm/Insts/BR/Hints.lean:18-23`) rejects `BTI` (`hint #34`/`#36`/`#38`) and `PACIASP` (`hint #25`) with `StateError.Unimplemented`.
3. **Upstream golden ISA specifications require per-opcode slicing and consumer-side soundness patches before Pass-2 kernel replay:** `rems-project/sail-arm` (`5416ef6b43e9527c38dc71fb752259c1d01a47e1`, `arm-v9.4-a/lean/ArmExtras.lean:19-23`) overrides `decreasing_trivial` with a fallback to `grind | decide | sorry`, injecting `sorryAx` into recursive helpers; partially evaluating concrete opcodes via `UQ-PAC/ASLp` (`92e4fd949402056e16e3747e66922060be57ecc8`, `libASL/rASL_check.ml:104-276`) yields loop-free Reduced ASL (`rASL`) free of termination `sorry`s. In `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`), `LeanRV64D/VextUtilsInsts.lean:498-523, 663-666` hardcodes RVV `AGNOSTIC` (`vta`/`vma`) to deterministic undisturbed (`vd_val[i]`), `LeanRV64D/VextVsetInsts.lean:328-341` hardcodes `vl_use_ceil := false` (clamping `VLMAX < AVL < 2 * VLMAX` deterministically to `VLMAX`), and `LeanRV64D/RiscvExtras.lean:31-112` introduces 75 custom `axiom` declarations.
4. **Empirical LLVM 22.1.6 codegen parity with FFmpeg inline/external assembly:** Dissection of H.264/HEVC `get_cabac_inline` shows that naive ternary Rust over an `extern` table triggers two LLVM 22 regressions (`X86CmovConversion` turning the ~50/50 LPS decision back into a conditional `jle` branch, plus three `R_X86_64_GOTPCREL` loads), whereas 100% safe, panic-free Rust passing `&CabacTables` by reference with power-of-two index masking (`& 0x1FF`, `& 0xFF`) and arithmetic `>> 31` bitmasking compiles to a 30-instruction branchless BMI2 `shlx` sequence matching FFmpeg's 29-instruction `get_cabac_inline_x86` inline assembly (`libavcodec/x86/cabac.h:72-106`). For 8-tap HEVC `vpmaddubsw` vertical filtering, `core::arch::x86_64` matches `libavcodec/x86/hevc/mc.asm` up to 12–14 live YMM registers, leaving external assembly necessary only where 16-YMM register pressure requires memory-operand `[reg + disp]` fusion (`hevc/mc.asm:586-589`) or cross-iteration register pinning.

## Applicability

This report governs the compiler lowering, binary object lifting, TCB boundary design, and ISA correspondence verification of media DSP and entropy-coding kernels across x86-64 (SSSE3/AVX2/AVX-512, CET-IBT), AArch64 (NEON, BTI/PAC), and RISC-V (`RV64GCV` RVV 1.0, `Zicfilp`), across ELF64, Mach-O 64, and Windows PE32+/COFF object formats.

Subject relationships:
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)** defines the two-pass TCB audit architecture (`trusted/audit/TrustedBoundary.lean` and `trusted/audit/src/lib.rs`) whose Pass-2 `CorrOrigin` mechanism (`vendor/lean-miri` kernel replay) is analyzed and generalized here to per-opcode ISA correspondence.
- **`rust-lang/rust` (`ec65cd52bba13d491ff65c9d218b39753755c84a` source; `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` executed nightly binary bundling LLVM `22.1.6`)** and **`rust-lang/stdarch` (`ca26a96d57b295dcd927622877242940a0f3c02e`)** define how `#[target_feature]` and `core::arch` SIMD intrinsics lower from MIR to machine objects.
- **`FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`)** supplies the concrete assembly macro frameworks (`libavutil/x86/x86inc.asm`, `libavutil/aarch64/asm.S`, `libavutil/riscv/asm.S`), CABAC entropy decoder (`libavcodec/cabac_functions.h`, `libavcodec/x86/cabac.h`), and 6/8-tap motion-compensation kernels (`libavcodec/x86/h264_qpel_8bit.asm`, `libavcodec/x86/hevc/mc.asm`) against which clean-room Rust codegen and binary lifters are evaluated.
- **`intelxed/xed` (`0bcb6237345c5066726dcc08b3d87928df3b5b26`)**, **`rems-project/sail-arm` (`5416ef6b43e9527c38dc71fb752259c1d01a47e1`)**, **`UQ-PAC/ASLp` (`92e4fd949402056e16e3747e66922060be57ecc8`)**, **`leanprover/LNSym` (`49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`)**, **`opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`)**, and **`riscv/sail-riscv` (`ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`)** are the concrete upstream decoder and ISA semantics artifacts evaluated as Pass-2 golden correspondence targets.

For broader background on FFmpeg's CPU-flag dispatch tables, general ISA model comparisons, and MIR inline-assembly contracts, see companion corpus packages `ffmpeg-codebase-architecture-cpuflags-dispatch-and-asm-corpus-census`, `x86-64-and-aarch64-simd-isa-formalizations-sail-asl-acl2-hol-k-comparison`, `riscv-rvv-ppc-vsx-loongarch-and-wasm-simd-isa-formalizations`, `verified-simd-vs-scalar-equivalence-for-media-dsp-kernels-and-asm`, and `rust-inline-asm-and-external-asm-abi-seams-in-formal-verifiers`.

## Findings

### 1. The MIR-to-Machine Lowering Gap on `#[target_feature]` and `core::arch` Intrinsics

`Basis: source + derived`

In an Anneal-style verification pipeline (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`), `trusted/rustc-capture/src/driver.rs` (`lines 32-85`) hooks `rustc_driver` and captures post-cleanup runtime MIR (`Trusted.MirAst` / `Trusted.MirSemantics`), while Pass 2 (`trusted/correspondence/Trusted/Correspondence.lean:34-126`) proves simulation equivalence against `proofs-rs/lean-miri`. While this closes MIR operational semantics for pure scalar Rust, `core::arch` vendor intrinsics bypass MIR operational semantics through a three-stage lowering chain:

1. **Unadjusted LLVM intrinsic FFI in `stdarch`:** In `rust-lang/stdarch@ca26a96d57b295dcd927622877242940a0f3c02e`, vendor wrappers such as `_mm256_maddubs_epi16` (`crates/core_arch/src/x86/avx2.rs:1854-1860`) and `_mm_maddubs_epi16` (`crates/core_arch/src/x86/ssse3.rs:288-290`) transmute `#[repr(simd)]` types (`__m256i` -> `u8x32`, `i8x32`) and invoke foreign functions declared inside `unsafe extern "unadjusted"` blocks carrying `#[link_name = "llvm.x86.avx2.pmadd.ub.sw"]` (`avx2.rs:3744-3745`). Other intrinsics (such as `_mm_maskload_epi32`, `avx2.rs:1872-1875`) lower to `#[rustc_intrinsic]` SIMD operations (`simd_shr`, `simd_masked_load!`).
2. **Opaque MIR `TerminatorKind::Call` boundary:** At `Runtime(PostCleanup)` MIR, calls to `#[rustc_intrinsic]` and `#[link_name = "llvm.*"]` functions appear as `TerminatorKind::Call` terminators (`compiler/rustc_codegen_ssa/src/mir/block.rs:1051-1066` in `rust-lang/rust@ec65cd52bba13d491ff65c9d218b39753755c84a`). `Trusted.MirSemantics` has no native evaluator rule for `llvm.x86.*`, `llvm.aarch64.*`, or `llvm.riscv.*` target intrinsics (`TerminatorKind.call` to unmodeled foreign items yields `.fault .unsupported` / `.blocked` in `Trusted.Correspondence:578-580`).
3. **`rustc_codegen_llvm` attribute synthesis and LLVM backend passes:** `Builder::codegen_intrinsic_call` (`compiler/rustc_codegen_llvm/src/intrinsic.rs:965-999`) dispatches `Intrinsic::Rustc` to `codegen_rustc_intrinsic_call` and `Intrinsic::Backend { llvm }` / `codegen_llvm_intrinsic_call` to `LLVMBuildCallWithOperandBundles` (`lines 940-961`) after `autocast` bitcasting between Rust `#[repr(simd)]` LLVM types (`<32 x i8>`) and LLVM intrinsic signatures (`<16 x i16>`). Concurrently, `attributes::target_features_attr` (`compiler/rustc_codegen_llvm/src/attributes.rs:454-465`) concatenates `tcx.sess.global_backend_features` with per-function `#[target_feature(enable = "...")]` strings into an LLVM `"target-features"` function attribute.

Consequently, assigning Axiom-free MIR specifications to `core::arch` functions without inspecting emitted machine code leaves four concrete classes of backend soundness hazards inside the unverified LLVM TCB across the media verification priority stack:

| Priority Tier | Unverified `core::arch` -> LLVM Lowering Hazard | Concrete Failure Mechanism | Closure via Object-Level Lifting |
| :--- | :--- | :--- | :--- |
| **1. UB-freedom** | Target-feature leakage & ABI register clobbers | Inlining or cross-ABI calls missing `vzeroupper`, corrupting Win64 `xmm6..xmm15`, or emitting AVX-512 EVEX instructions before CPUID dispatch (`target_features.rs:164-187`) | Decodes exact emitted opcodes (`xed` `ISA_SET`), verifies `vzeroupper` before `ret`, and proves callee-saved register preservation on the `.o` CFG |
| **2. Panic-freedom** | Residual bounds-check / unwind edges | Failed dead-branch elimination leaving `call core::panicking::panic_bounds_check` or unexpected `UD2`/trap instructions inside media hot loops | Proves on the lifted `.o` CFG that zero external call/trap terminators are reachable from entry under the precondition |
| **3. Behavioral & SIMD-vs-scalar equivalence** | LLVM `InstCombine` / `VectorCombine` / `SelectionDAG` miscompilations | Poison propagation across `simd_shuffle`/`simd_masked_load`, lane-crossing `vperm2i128`/`vpackuswb` ordering errors, or signed saturation rewrites | Proves bit-exact input-output refinement between the lifted `.o` machine semantics and the Pass-1 pure scalar Rust specification |
| **4. Spec conformance** | Rounding, shift, and saturation corner cases | ITU-T H.264/H.265 bi-prediction `((a + b + offset) >> shift)` intermediate 16-bit signed overflow in `pmaddubsw` (`u8 * i8` saturates `i16` at `[-32768, 32767]`!) | Discharges exact `BitVec` lane bounds (e.g., sum of positive/negative filter taps $\times 255 \le 32767$) directly against ISA `vpmaddubsw` semantics |

Notice the crucial saturation subtlety in row 4: x86 `(v)pmaddubsw` multiplies unsigned bytes `u8` by signed bytes `i8` and **horizontally adds adjacent pairs with signed 16-bit saturation** (`SATSW(a[2i]*b[2i] + a[2i+1]*b[2i+1])`), NOT modular `i16` wrap and NOT `i32` widening. For HEVC 8-tap luma qpel filters `[-1, 4, -10, 58, 17, -5, 1, 0]`, the maximum adjacent pair `(58, 17)` achieves $255 \times (58 + 17) = 19,125 \le 32,767$ (no saturation), whereas arbitrary `i8` pairs `(127, 127)` reach $255 \times 254 = 64,770 > 32,767$ and saturate to `32767`! Lifting the compiled `.o` exposes the exact `vpmaddubsw` opcode semantics to the Lean proof obligation.

---

### 2. Object-Level Relocatable Binary Lifting Across ELF64, Mach-O 64, and Win64 COFF

`Basis: execution + source + normative`

A central finding from executing cross-target compilation on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`) is that **object-level lifting cannot operate solely on `.text` bytes**, even when the source Rust function references no external `static` symbol at the HIR/MIR level. When compiling `mc_8tap_probe` (which loads a 32-byte constant tap array `[0xff, 4, 0xf6, 58, 17, 0xfb, 1, 0; x4]` and applies eight `llvm.x86.avx2.pmadd.ub.sw` operations), LLVM `22.1.6` deduplicated the repeating 8-byte pattern into an anonymous read-only constant-pool symbol and emitted `vpbroadcastq` with a PC-relative relocation:

```text
37: c4 62 7d 59 05 00 00 00 00   vpbroadcastq ymm8, QWORD PTR [rip+0x0]
                                 3c: R_X86_64_PC32  .LCPI0_0-0x4
```

In the unlinked relocatable `.o` file, bytes `0x3c..0x40` of `.text.mc_8tap_probe` are literally `00 00 00 00`. An instruction-only lifter that decodes `.text` without applying the object file's relocation table interprets `QWORD PTR [rip + 0]` as reading the 8 bytes immediately following the `vpbroadcastq` instruction (`c4 c2 7d 04 c0 c4 c2 75` — the encoded bytes of the next two `vpmaddubsw` instructions!), silently proving or refuting behavior over corrupted filter weights.

Across the five target/format combinations needed for cross-platform media builds, a sound object-level lifter must parse section headers, symbol tables, and relocation records according to the following verified matrix:

| Target & Format | Code Section | Constant Table Section(s) | PC-Relative Constant Relocation(s) | Effective Target Address Formula ($S$ = sym addr, $A$ = addend, $P$ = reloc site) |
| :--- | :--- | :--- | :--- | :--- |
| **Linux/BSD x86-64 (ELF64)** | `.text` / `.text.<fn>` | `.rodata`, `.rodata.cst8`, `.rodata.cst16`, `.rodata.cst32` (`SHF_ALLOC \| SHF_MERGE`) | `R_X86_64_PC32` (type `2`, `SHT_RELA`) | $\text{EA} = \text{RIP}_{\text{next}} + (S + A - P)$; since $P = \text{RIP}_{\text{next}} - 4$ (or $-4 - \text{imm\_bytes}$), compiler sets $A = \text{offset} - (\text{RIP}_{\text{next}} - P)$ (e.g., $A = -4$), simplifying to $\text{EA} = S + (A + \text{RIP}_{\text{next}} - P)$ |
| **Windows x64 (PE32+/COFF)** | `.text` (`IMAGE_SCN_CNT_CODE`, COMDAT `one_only`) | `.rdata` (`IMAGE_SCN_CNT_INITIALIZED_DATA \| IMAGE_SCN_MEM_READ`, e.g. `__real@0001fb113af604ff`) | `IMAGE_REL_AMD64_REL32` (type `0x0004`), `REL32_1`..`REL32_5` (`0x0005`..`0x0009`) | Implicit addend $I_0$ stored inline at $P$; for `REL32_k` ($k \in \{0..5\}$), $\text{disp32} = S + I_0 - (P + 4 + k)$ so $\text{EA} = S + I_0$ |
| **macOS x86-64 (Mach-O 64)** | `__TEXT,__text` | `__TEXT,__const`, `__TEXT,__literal8`, `__TEXT,__literal16` | `X86_64_RELOC_SIGNED` (`1`), `SIGNED_1` (`2`), `SIGNED_2` (`3`), `SIGNED_4` (`4`) | Inline 32-bit signed displacement corrected by $0, 1, 2, 4$ trailing immediate bytes so $\text{EA}$ resolves to `LCPI*` or `_sym` |
| **Linux AArch64 (ELF64)** | `.text` / `.text.<fn>` | `.rodata`, `.rodata.<sym>` | `R_AARCH64_ADR_PREL_PG_HI21` (`275`) + `R_AARCH64_ADD_ABS_LO12_NC` (`277`) or `R_AARCH64_LDST128_ABS_LO12_NC` (`299`) | Two-instruction sequence: `adrp x_base, sym` sets $x_{\text{base}} = ((S + A) \ \& \ \neg\text{0xFFF})$; paired `add` or `ldr q_d, [x_base, :lo12:sym]` adds $(S + A) \ \& \ \text{0xFFF}$ |
| **Linux RISC-V 64 (ELF64)** | `.text` / `.text.<fn>` | `.rodata`, `.rodata.<sym>` | `R_RISCV_PCREL_HI20` (`23`) + `R_RISCV_PCREL_LO12_I` (`24`) + **`R_RISCV_RELAX` (`51`)** | `1: auipc reg, %pcrel_hi(sym)` sets $\text{reg} = P_1 + \text{hi20}(S + A - P_1)$; `addi`/`vl*` references label `1b` (`R_RISCV_PCREL_LO12_I` targets the `auipc` PC $P_1$, **not** `sym` directly!) |

Two object-lifting hazards require explicit fail-closed checks in the lifter:
1. **RISC-V Linker Relaxation (`R_RISCV_RELAX`):** When GAS or LLVM emits `R_RISCV_RELAX` (`type 51`) alongside `R_RISCV_PCREL_HI20`/`LO12_I` or `R_RISCV_CALL_PLT`, `ld`/`lld` may delete the `auipc` or shorten jumps during final DSO linking, invalidating intra-function branch offsets verified at `.o` time. Any `.o`-level RISC-V lifter must either reject `R_RISCV_RELAX` relocations in verified kernel sections (compiled with `-C target-feature=-relax` or GAS `.option norelax`) or run verification post-relocation on the linked DSO.
2. **GOT Indirection on `extern` Tables (`R_X86_64_GOTPCREL` / `R_X86_64_REX_GOTPCRELX`):** In `mc_core_arch.o` (`hevc_put_v8_row_avx2`), declaring `pub static HEVC_LUMA_TAPS` without `#[hidden]` / internal visibility under PIC caused `rustc` to emit `mov rax, QWORD PTR [rip+0x0]` with `R_X86_64_GOTPCREL` (`offset 0x9`), introducing an extra pointer indirection through `.got` whose slot could in principle be interposed unless `-Bsymbolic` or hidden visibility (`STV_HIDDEN`) is enforced. Marking internal constant tables `private` (non-`pub`) or `.hidden` (`const` macro in `libavutil/x86/x86inc.asm:890-900` emits `global %1:data hidden` on ELF and `:private_extern` on Mach-O) collapses the access to direct `R_X86_64_PC32` against `.rodata` and allows the object lifter to bind the exact immutable byte contents of the target `.rodata` slice into the verification precondition.

 Formally, the object lifter constructs a pure static memory map $M_{\text{ro}} : \text{Addr} \rightharpoonup \text{UInt8}$ by assigning disjoint synthetic high-canonical virtual base addresses (aligned to $\max(\text{sh\_addralign}, 4096)$) to `.text.<fn>` and every read-only `SHF_ALLOC` data section (rejecting `SHF_WRITE` sections!), resolving all `SHT_RELA` / COFF / Mach-O relocations inside `.text.<fn>` against those bases, and asserting that every resolved relocation target lies within an admitted read-only section with zero unresolved external symbols.

---

### 3. Decoding, CFI Landing Pads (`endbr64`, `BTI`, `lpad`), and Win64 `.pdata`/`.xdata` Unwind Contracts

`Basis: source + execution + normative`

Media codecs invoke SIMD DSP kernels almost exclusively through indirect function-pointer tables (`H264QpelContext`, `HEVCDSPContext`, `SwsContext`), making hardware forward-edge Control-Flow Integrity (CFI) landing pads mandatory on modern OS distributions (Fedora/Ubuntu/Android/Windows). Simultaneously, Windows x64 (`PE32+`) requires static unwind metadata for every non-leaf function that modifies `rsp` or saves non-volatile `xmm6..xmm15` registers.

#### 3.1 x86-64 `intelxed/xed` Decoding and the `x86inc.asm` CET-IBT Linker Downgrade Trap

In `intelxed/xed@0bcb6237345c5066726dcc08b3d87928df3b5b26`, `datafiles/cet/cet-isa.xed.txt` (`lines 57-68`) defines `ENDBR64`:

```text
ICLASS:      ENDBR64
CATEGORY:    CET
EXTENSION:   CET
ISA_SET:     CET
PATTERN:     0x0F 0x1E MOD[0b11] MOD=3 REG[0b111] RM[0b010] f3_refining_prefix CET=1
OPERANDS:
IFORM:       ENDBR64
```

Note the decoder state-machine condition `CET=1`: if XED's `xed_state_t` chip/feature mode disables `CET`, `F3 0F 1E FA` decodes instead into the legacy `NOP` space (`0F 1E /r`), whereas with `CET=1` it decodes to `XED_ICLASS_ENDBR64` with zero explicit operands (transitioning the architectural `CET_U_MSR` indirect-branch state machine `TRACKER` from `WAIT_FOR_ENDBRANCH` to `IDLE`, and acting as a 4-byte `RIP += 4` no-op when `TRACKER == IDLE`). Similarly, `VPMADDUBSW` (`datafiles/avx512-skx/skx-isa.xed.txt:15511-15598` and `datafiles/hswavx/hsw-int256-isa.txt:525`) splits across three distinct encoding spaces—legacy SSSE3 (`66 0F 38 04 /r`, preserving bits `255:128` on legacy SSE! vs zeroing upper bits in VEX), VEX.128/VEX.256 (`C4 E2 ... 04 /r`, zeroing `ZMM[MAXVL-1:256]`), and EVEX.128/256/512 (`62 ... 04 /r` with `MASKmskw` write-masking). Using XED's table-driven decoder (`ICLASS` + `IFORM` + explicit/suppressed operand widths) avoids hand-rolled prefix-parsing bugs on VEX/EVEX `W`/`L`/`vvvv` bits.

Inspecting `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (`libavutil/x86/x86inc.asm:820-922`) reveals a critical production defect when mixing FFmpeg NASM objects with CET-enabled Rust objects:
- `cglobal_internal` (`x86inc.asm:826-861`) emits **zero** `endbr64` instructions at function entry.
- Lines `910-918` of `x86inc.asm` emit a `.note.gnu.property` section setting `GNU_PROPERTY_X86_FEATURE_1_AND` (`0xc0000002`) to `0x00000002` (`GNU_PROPERTY_X86_FEATURE_1_SHSTK` only, omitting bit 0 `GNU_PROPERTY_X86_FEATURE_1_IBT = 0x1`).
- **Executed linker verification (`Basis: execution`):** Compiling `simd_obj.rs` with `rustc -Z cf-protection=full` emits `endbr64` (`f3 0f 1e fa`) at offset `0x0` of `mc_8tap_probe` and sets `NT_GNU_PROPERTY_TYPE_0` to `x86 feature: IBT, SHSTK` (`0x3`). Linking `elf_x86.o` alone via `ld -shared` preserves `IBT, SHSTK`. Linking `elf_x86.o` together with a single object carrying `x86inc.asm`'s `0x2` note (`ld -shared elf_x86.o fake_nasm.o -o mixed_nasm_cet.so`) causes `ld` to compute `0x3 & 0x2 = 0x2`, **silently stripping `IBT` from the entire output shared library**. Conversely, forcing `-Wl,-z,ibt` without patching `cglobal` to emit `endbr64` causes every indirect DSP call on Intel Tiger Lake+ / AMD Zen 4+ CET kernels to raise `#CP` (`ENDBRANCH`). Any external x86-64 `.asm` kernel retained in a hardened build must therefore emit `endbr64` at every `cglobal` entry and set `pr_data = 0x00000003`.

#### 3.2 AArch64 `BTI` / `PACIASP` and RISC-V `Zicfilp` `lpad`

On AArch64, `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (`libavutil/aarch64/asm.S:213-262`) emits `hint #34` (`BTI c`, `0xd503245f`) at `function` entry (`AARCH64_VALID_CALL_TARGET`), `hint #38` (`BTI jc`, `0xd50324df`) at jump targets, `paciasp` (`hint #25`, `0xd503233f`) when branch-protection PAC-RET is enabled, and `.note.gnu.property` `GNU_PROPERTY_AARCH64_FEATURE_1_AND` (`0xc0000000`). Compiling `simd_obj.rs` with `rustc --target aarch64-unknown-linux-gnu -Z branch-protection=bti,pac-ret` identically emits `hint #34` as instruction 0 of `mc_aarch64_probe` (omitting `paciasp` because `mc_aarch64_probe` is a leaf function that never spills `x30`/`lr`!).
- **Critical `LNSym` incompatibility (`Basis: source`):** In `leanprover/LNSym@49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`, `Arm/Insts/BR/Hints.lean` (`lines 18-23`) implements `exec_hints` as:
  ```lean
  def exec_hints (inst : Hints_cls) (s : ArmState) : ArmState :=
    if inst.CRm = 0b0000#4 ∧ inst.op2 = 0b000#3 then
      write_pc ((read_pc s) + 4#64) s
    else
      write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s
  ```
  Because `BTI c` encodes `CRm = 0b0100, op2 = 0b010` (`hint #34`), `BTI j` encodes `CRm = 0b0100, op2 = 0b100` (`hint #36`), `BTI jc` encodes `CRm = 0b0100, op2 = 0b110` (`hint #38`), and `PACIASP` encodes `CRm = 0b0011, op2 = 0b001` (`hint #25`), unpatched `LNSym` immediately halts with `StateError.Unimplemented` at offset `0x0` of any BTI-enabled kernel. By contrast, `rems-project/sail-arm@5416ef6b43e9527c38dc71fb752259c1d01a47e1` (`arm-v9.4-a/src/v8_base.sail:10585-10595, 22591-22638` and `instrs64.sail:4320`) models `PSTATE.BTYPE`, `BTypeCompatible_BTI(op2[2..1])`, and `BranchTargetCheck()` completely.

On RISC-V (`RV64GCV`), `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (`libavutil/riscv/asm.S:78-82`) defines the `Zicfilp` landing-pad macro:
```asm
#if !defined (__riscv_zicfilp)
        .macro  lpad    lpl
        auipc   zero, \lpl
        .endm
#endif
```
Because `rd = x0` (`zero`) discards the `auipc` PC+imm20 result on pre-`Zicfilp` cores, `0x00000017 | (lpl << 12)` is backwards-compatible architectural NOP space on baseline `RV64GC` while checking `elp == LP_EXPECTED` and matching the 20-bit landing-pad label `lpl` against `x7[31:12]` (`t2`) when `lpl != 0` under `Zicfilp` (`opencompl/sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f`, `LeanRV64D/ZicfilpInsts.lean:217-225`, raising `SWC_LANDING_PAD_FAULT` on mismatch).

#### 3.3 Win64 PE32+ `.pdata` / `.xdata` Unwind Tables vs. `x86inc.asm`

Under the Microsoft x64 Calling Convention, `rbx, rbp, rdi, rsi, r12..r15` and the low 128-bit halves **`xmm6..xmm15`** are non-volatile (callee-saved), while upper bits `ymm0..ymm15[255:128]` and `zmm0..zmm31[511:128]` are volatile. Any non-leaf function—and **every** function that modifies `rsp` or saves non-volatile registers—must register a 12-byte `RUNTIME_FUNCTION` entry in `.pdata` (`BeginAddress`, `EndAddress`, `UnwindInfoAddress`, each carrying an `IMAGE_REL_AMD64_ADDR32NB` RVA relocation) pointing to an `UNWIND_INFO` structure in `.xdata`.

Executing `rustc --target x86_64-pc-windows-msvc -C opt-level=3 --emit=obj` on `mc_8tap_probe` (which uses 9 YMM registers `ymm0..ymm8`, forcing `xmm6, xmm7, xmm8` saves) produced the exact `.pdata` (12 bytes) and `.xdata` (20 bytes) payloads (`Basis: execution`):

```text
.pdata: 00000000 c5000000 00000000
  0x00: BeginAddress = 0x00000000 (+ IMAGE_REL_AMD64_ADDR32NB .text)
  0x04: EndAddress   = 0x000000c5 (+ IMAGE_REL_AMD64_ADDR32NB .text, 197-byte body)
  0x08: UnwindData   = 0x00000000 (+ IMAGE_REL_AMD64_ADDR32NB .xdata)

.xdata: 01 15 07 00  15 68 00 00  10 78 01 00  0a 88 02 00  04 62 00 00
  Header: Version=1, Flags=0 (0x01), SizeOfProlog=0x15 (21 bytes),
          CountOfCodes=0x07 (7 uint16 slots), FrameRegister=0 (0x00)
  Codes (reverse prolog order):
    [0..1] Offset 0x15: Op=8 (UWOP_SAVE_XMM128), Info=6 (xmm6), ScaledOffset=0x0000 -> [rsp + 0*16]
    [2..3] Offset 0x10: Op=8 (UWOP_SAVE_XMM128), Info=7 (xmm7), ScaledOffset=0x0001 -> [rsp + 1*16]
    [4..5] Offset 0x0a: Op=8 (UWOP_SAVE_XMM128), Info=8 (xmm8), ScaledOffset=0x0002 -> [rsp + 2*16]
    [6]    Offset 0x04: Op=2 (UWOP_ALLOC_SMALL), Info=6 -> alloc (6*8 + 8) = 56 bytes (sub rsp, 56)
    [7]    0x0000 (4-byte alignment tail padding)
```

Compare this against `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (`libavutil/x86/x86inc.asm:500-621`):
- `WIN64_PUSH_XMM` (`lines 536-542`) saves `xmm6` at `[rstk + stack_offset + 8]` and `xmm7` at `[rstk + stack_offset + 24]` inside the caller's 32-byte home/shadow space (note `[rsp + 8]` before `sub rsp` is **16-byte aligned** because `call` pushed an 8-byte return address onto a 16-byte-aligned `rsp`, so `(rsp_entry + 8) % 16 == 0`—a subtle alignment invariant an object lifter must track to avoid spuriously flagging `movaps [rsp + 8], xmm6` as unaligned UB!).
- However, `x86inc.asm` contains **zero** `.xdata`/`.pdata` directives. On Windows x64, `RtlVirtualUnwind` treats any IP lacking a `.pdata` `RUNTIME_FUNCTION` entry as a pure leaf function (`[rsp]` = return address), causing ETW stack-sampling profilers, Vectored Exception Handlers (VEH), and crash-dump walkers interrupted inside an FFmpeg AVX2 kernel after `sub rsp, stack_size_padded` to dereference SIMD spill data as the caller return address. An object-level verifier targeting Win64 should therefore check **unwind-table correspondence**: every prolog instruction (`push reg`, `sub rsp, imm`, `vmovaps [rsp+k], xmmN`) up to `SizeOfProlog` must match the inverse state transition encoded by `UNWIND_INFO.UnwindCode[]`, and epilogs must follow the canonical Windows x64 epilog grammar (`add rsp, imm` / `lea rsp, [fp+disp]`, zero or more `pop reg`, `ret` — note `vzeroupper` appears *after* `.seh_endepilogue` and *before* `retq` in LLVM 22.1.6 `coff_win64.s:463-467`, which is a slight deviation from strict `RtlVirtualUnwind` mid-epilog detection unless `vzeroupper` precedes `addq $56, %rsp`!).

---

### 4. Sandboxed Pass-2 Per-Opcode ISA Correspondence Architecture

`Basis: source + derived`

In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/audit/TrustedBoundary.lean` (`lines 13-122, 229-314`) and `trusted/audit/src/lib.rs` (`lines 61-89, 123-157`) establish a rigorous two-pass TCB separation for large external reference specifications:
- **Pass 1 (`RepoOrigin`):** Compiles `trusted/lean/` (`vetted` and `candidate:<feature>`) and untrusted `theory/` proofs against a locked 3-axiom Lean `v4.34.1` foundation (`propext`, `Quot.sound`, `Classical.choice`), forbidding `axiom`, `unsafe`, `partial`, `sorry`, `native_decide`, `bv_decide`, and `grind` (`allowedTheoryTacticKinds`, `TrustedBoundary.lean:529-558`), and replaying every declaration at `trustLevel := 0`, `loadExts := false`.
- **Pass 2 (`CorrOrigin`):** Isolates `vetted` constants completely from external code (`CorrOrigin.edgeViolation?`, `lines 263-270`), stages SHA-256-pinned vendor files plus an explicit `LOCKED_PATCHED_*` consumer-patch list inside a networkless `bwrap --unshare-all` sandbox (`lib.rs:68-73`), replays every non-`isPartial` vendor declaration from scratch onto the authenticated `{Init,Std,Lean}*` sysroot (`LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`, `lib.rs:141-142`), rejects any `axiom`, `unsafe`, `sorryAx`, `partial`, `opaque`, or compiler-reflection primitive in the reachable cone, and checks bidirectional correspondence between Anneal's compact evaluator and the vendor reference model.

Applying this exact Pass-2 architecture to ISA machine semantics solves the classic tension between **symbolic execution speed** and **ISA specification fidelity**:
- Pass 1 uses a compact, total, pure `BitVec` evaluator $M_{\text{isa}}$ (`candidate:isa_x86_64`, `candidate:isa_aarch64`, `candidate:isa_riscv64`) tailored for media user-space kernels (~60–90 SIMD/GPR/branch/load/store opcodes per ISA, flat byte-addressed memory + read-only `.rodata` map, zero MMU/page-table/privilege-ring state).
- Pass 2 proves **per-opcode correspondence slices** ($\forall s, \text{AdmittedState}(s) \implies M_{\text{isa}}(\text{bytes}, s) \sqsubseteq M_{\text{vendor}}(\text{bytes}, \alpha(s))$) inside `bwrap --unshare-all`, avoiding monolithic multi-hundred-thousand-line ISA imports during Pass-1 proof checking.

Direct source inspection of the upstream Arm and RISC-V formalizations identifies the exact obstacles that Pass-2 slicing and `UPSTREAM_PIN.json` consumer patches must resolve:

#### 4.1 AArch64: Avoiding `rems-project/sail-arm` `ArmExtras.lean` `sorry`s via `UQ-PAC/ASLp` `rASL`

In `rems-project/sail-arm@5416ef6b43e9527c38dc71fb752259c1d01a47e1`, `arm-v9.4-a/Makefile` (`lines 85-97`) invokes `sail -lean --lean-force-output ... -lean-import-file lean/ArmExtras.lean` over the entire Armv9.4-A monolith (`instrs64.sail`, `instrs64_sve.sail`, `instrs64_sme.sail`, `sysregs_autogen.sail`). Inspecting `arm-v9.4-a/lean/ArmExtras.lean` (`lines 19-23`) reveals:

```lean
macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | grind
  | decide
  | sorry)
```

Every recursive Sail helper in Armv9.4-A whose termination measure (`src/termination_measures.sail`, where several `while`-loop measures are guarded under `$iftarget coq` at `line 134`!) is not discharged by `grind` or `decide` elaborates silently via **`sorry`** (`sorryAx`), which immediately fails `TrustedBoundary.lean`'s Pass-2 cone check (`sorryAx` + `grind` syntax/reflection rejection).

`UQ-PAC/ASLp@92e4fd949402056e16e3747e66922060be57ecc8` (Lam & Coughlin, FMCAD 2023, DOI `10.34727/2023/isbn.978-3-85448-060-0_36`; Coughlin, Michael & Lam, SAS 2024, DOI `10.1007/978-3-031-74776-2_4`) eliminates both the monolith and all recursive termination obligations before Lean translation:
- Given a concrete 32-bit A64 opcode pattern (with register indices `Rd, Rn, Rm` symbolic and opcode/size/lane-count bits concrete), `libASL/dis.ml` (`lines 134-220`) partially evaluates Arm's ASL decode-and-execute specification at fixed `PSTATE.EL = EL0` / A64 state, statically unrolling all bounded lane loops (`for e = 0 to elements - 1`) and constant-folding `DecodeBitMasks` / `AdvSIMDExpandImm`.
- `libASL/rASL_check.ml` (`lines 38-296`) mechanically enforces the closed **Reduced ASL (`rASL`)** grammar (`RASLInvariantFailed`):
  1. **Loop-free, recursion-free control flow (`lines 244-257`):** Only `Stmt_VarDeclsNoInit`, `Stmt_VarDecl`, `Stmt_ConstDecl`, `Stmt_TCall`, `Stmt_Assign`, `Stmt_Assert`, `Stmt_Throw`, and binary `Stmt_If (_, _, [], _, _)` (zero `for`/`while` loops, zero `elseif` chains, zero recursive calls).
  2. **Constant-width bit-slices only (`line 266`):** `Expr_Slices(e, [Slice_LoWd(l, w)])` requires `is_const(l) && is_const(w)` (`Expr_LitInt`), eliminating dependent bitvector width proof obligations (`BitVec (w_expr)`) in Lean 4.
  3. **Closed 33-scalar + 19-vector primitive set (`lines 104-160`):** Restricts pure calls to fixed bitvector/boolean primitives (`add_bits`, `mul_bits`, `asr_bits`, `SignExtend`, `ZeroExtend`, `append_bits`, `replicate_bits`, etc.) plus optional vector ops (`Elem.read`, `Elem.set`, `add_vec`, `mul_vec`, `shuffle_vec`, `reduce_add`), with memory reads isolated to `Stmt_ConstDecl(..., "Mem.read")` (`lines 55-66`).

Translating per-opcode `rASL` outputs into non-recursive Lean 4 definitions (and cross-checking overlap opcodes against `leanprover/LNSym@49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c` `Arm/Insts/DPSFP/*` after patching `Arm/Insts/BR/Hints.lean:18-23` for `BTI`/`PACIASP`) yields a 100% `sorry`-free, `partial`-free Pass-2 AArch64 correspondence target, with the offline OCaml partial evaluator `ASLp` cross-validated by differential hardware/Sail co-simulation (`tests/coverage/aarch64_vector{1,2}`).

#### 4.2 RISC-V (`RV64GCV`): Patching `opencompl/sail-riscv-lean` Soundness Gaps (`AGNOSTIC`, `vsetvli`, `RiscvExtras`)

Direct inspection of `opencompl/sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f` (`173,614` lines across `LeanRV64D/*.lean`) and upstream `riscv/sail-riscv@ec5200bdfe0c10afa6dbb1f7b0980db2d236236e` uncovers **four structural and semantic barriers** that must be patched via Anneal's `UPSTREAM_PIN.json` consumer-patch mechanism:

1. **Unsound Deterministic `AGNOSTIC` (`vta`/`vma`) Tail and Mask Semantics:**
   Under the RISC-V "V" Vector Extension Specification v1.0 (§3.4.3), when `vta = 1` (`AGNOSTIC`) or `vma = 1` (`AGNOSTIC`), each inactive or tail destination element (indeed, each bit in general) may **either retain its prior value `vd[i]` or be overwritten with `1`s**. However, in `riscv/sail-riscv@ec5200bdfe0c10afa6dbb1f7b0980db2d236236e` (`model/extensions/V/vext_utils_insts.sail:427-445, 558-561`, marked `// TODO: configuration support`) and its generated Lean translation `opencompl/sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f` (`LeanRV64D/VextUtilsInsts.lean:498-523, 663-666`, plus eight inlined copies in `LeanRV64D/InstsEnd.lean:64683, 66414, 66517, 68849, 69087, 69138, 69188`), `.AGNOSTIC` is hardcoded to deterministic undisturbed:
   ```lean
   match tail_ag with
   | .UNDISTURBED => (GetElem?.getElem! vd_val i)
   | .AGNOSTIC    => (GetElem?.getElem! vd_val i)
   ```
   Proving a kernel with `ta`/`ma` enabled (such as FFmpeg's `vtype_vli ... ta, ma` kernels in `libavutil/riscv/asm.S:197`) against unpatched `sail-riscv-lean` is **unsound**: a kernel that accidentally reads tail lanes after a `vta=1` instruction passes verification under `sail-riscv-lean` yet computes corrupted pixels on real RVV silicon that writes `0xFF..FF` to tail elements.
   - **Required Pass-2 Consumer Patch:** Replace `.AGNOSTIC => vd_val[i]` in `init_masked_result` and `init_masked_result_cmp` with demonic bit-level nondeterminism `(vd_val[i] ||| (← undefined_bitvector _EEW))` (using `SailM`'s existing nondeterministic `undefined_bitvector` monadic primitive at `VextUtilsInsts.lean:539`!), which encompasses both `0#EEW` (undisturbed `vd_val[i]`) and `allOnes` (`0xFF..FF`) as well as arbitrary per-bit `1`-overwrites permitted by RVV 1.0 §3.4.3.

2. **Unsound Deterministic `vsetvli` AVL Clamping (`VLMAX < AVL < 2 * VLMAX`):**
   Under RVV 1.0 §6.2 ("Constraints on Setting `vl`"), when `0 < AVL <= VLMAX`, `vl = AVL`; when `AVL >= 2 * VLMAX`, `vl = VLMAX`; but when **`VLMAX < AVL < 2 * VLMAX`**, *any* integer satisfying $\lceil \text{AVL} / 2 \rceil \le \text{vl} \le \text{VLMAX}$ is architecturally legal (allowing hardware to balance final strip-mine tails). In `LeanRV64D/VextVsetInsts.lean:328-341` (generated from `vext_vset_insts.sail:80-92`), `vl_use_ceil` is hardcoded to `false`:
   ```lean
   def vl_use_ceil : Bool := false
   def calculate_new_vl (AVL : (BitVec 64)) (VLMAX : Nat) : Nat := ...
     if ((AVL <b (2 *i VLMAX)) : Bool) then
       (if (vl_use_ceil : Bool) then (Int.tdiv (AVL +i 1) 2) else VLMAX)
     else VLMAX
   ```
   Unpatched `sail-riscv-lean` therefore models `vl = min(AVL, VLMAX)`, failing to catch strip-mining bugs when compliant cores return $\lceil \text{AVL}/2 \rceil$ (or any intermediate value).
   - **Required Pass-2 Consumer Patch:** Lift `calculate_new_vl` into `SailM Nat` and, in the `VLMAX < AVL < 2 * VLMAX` branch, draw `vl` demonically via `choose_vl` constrained by `((AVL + 1) / 2 ≤ vl) ∧ (vl ≤ VLMAX)`. Note that FFmpeg's `vtype_vli` macro (`libavutil/riscv/asm.S:197-217`) dynamically computes the smallest `LMUL` via `csrr vlenb; clz` such that `AVL <= VLMAX`, which keeps `AVL <= VLMAX` (`vl = AVL` deterministically!) whenever `AVL` fits in `LMUL=8` (`8 * VLEN / SEW`).

3. **75 Unverified `axiom`s in `LeanRV64D/RiscvExtras.lean` and the 72,377-Line `InstsEnd.lean` Monolith:**
   `LeanRV64D/RiscvExtras.lean` (`lines 31-112`) declares **75 custom `axiom`s** (8 platform/reservation axioms `plat_term_write`..`sys_enable_experimental_extensions` plus 67 floating-point axioms `riscv_f16Add`..`riscv_f64roundToInt`), and `LeanRV64D/InstsEnd.lean` places `72,377` lines of mutually coupled system/privileged/CSR/MMU/FP/vector instruction executors into a single file using `set_option maxHeartbeats 1_000_000_000` (`ZicfilpInsts.lean:5`). Importing `InstsEnd.lean` into Pass 2 would pull `RiscvExtras` axioms into module headers and stall standalone kernel replay. Instead, integer/fixed-point RVV media opcodes reside cleanly in modular files (`LeanRV64D/VextArithInsts.lean` at 1,730 lines, `VextUtilsInsts.lean` at 797 lines, `VextVsetInsts.lean` at 371 lines, `ZbaInsts.lean`, `ZbbInsts.lean`, `ZicfilpInsts.lean` at 225 lines); slicing per-opcode `execute_VVTYPE` / `execute_VXTYPE` / `execute_VMVVTYPE` definitions out of `InstsEnd.lean` without importing `RiscvExtras` floating-point axioms keeps the Pass-2 integer/RVV correspondence cone 100% free of custom `axiom`s.

---

### 5. Empirical `rustc` LLVM 22.1.6 Dissection: H.264/HEVC CABAC and 6/8-Tap `vpmaddubsw` Motion Compensation

`Basis: execution + source`

To replace speculation about Rust vs. hand-written assembly performance with concrete compiler evidence, both H.264/HEVC binary arithmetic decoding (`get_cabac_inline`) and 8-tap HEVC `vpmaddubsw` motion compensation were compiled with `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`) on `x86_64-unknown-linux-gnu` (`-C opt-level=3`) and compared instruction-by-instruction against `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`.

#### 5.1 H.264 / HEVC `get_cabac_inline`: Two LLVM 22 Traps vs. 30-Instruction Safe Branchless Parity

In `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, `libavcodec/x86/cabac.h` (`lines 72-106, 177-209`) overrides the portable C `get_cabac_inline` (`libavcodec/cabac_functions.h:108-130`) with a 29-instruction inline assembly block (`BRANCHLESS_GET_CABAC`). Its historical advantage over C compilers rests on three invariants: (1) pinning `&ff_h264_cabac_tables` in a single GPR via an empty-template `lea` asm block (`lines 184-188`) so the three table lookups (`lps_range`, `norm_shift`, `mlps_state`) use base+index+offset addressing without reloading RIP/GOT addresses; (2) branchless LPS/MPS selection (`cmp` + two `cmovae` + `sbb mask, mask` + `xor mask, state`, using negative signed offsets `mlps_off + 128 + ~state` to index `0..127` on LPS and `128..255` on MPS); and (3) `tzcnt`-based 16-bit refill (`BRANCHLESS_GET_CABAC_REFILL`, `lines 45-53`).

Compiling two Rust formulations in `cabac_probe.rs` (`-C opt-level=3 -C target-cpu=x86-64-v3`) revealed a sharp divergence:

| Implementation Variant | Hot-Path Instrs (no refill) | LPS/MPS Branching | Table Base Loads | Shift Ops | Memory Safety / Panics |
| :--- | :---: | :--- | :--- | :--- | :--- |
| **FFmpeg `get_cabac_inline_x86` (`libavcodec/x86/cabac.h:72-106`)** | **29** | **0 branches** (`cmp` + 2x `cmovae` + `sbb`) | **1 `lea`** (`%[tables]`) | 3x legacy `shl %cl` (clobbers `%rcx`) | `unsafe` inline asm (`"memory"` clobber blocks surrounding LICM) |
| **Rust `get_cabac_unchecked_cmov` (naive `if is_lps` + `extern static`)** | **31** (split path) | **1 unpredictable `jle` + `jmp`!** (`0x2e: jle 3a`) | **3x `R_X86_64_GOTPCREL`!** (`0x14, 0x3d, 0x54`) | 2x BMI2 `shlx` | `unsafe` raw pointers, ~14–20 cycle mispredict penalty on high-entropy bins |
| **Rust `get_cabac_safe_idiomatic` (`&CabacTables` arg + `>> 31` mask + `& 0x1FF`/`& 0xFF`)** | **30** (inlined; 32 standalone) | **0 branches** (`sub` + `sar r10d, 0x1f` + `and`/`xor`) | **0 loads** (`rdx` arg reused across `+0x200`, `+0x400`, `+0`) | **2x BMI2 `shlx`** (`shlx ecx, ecx, edx`; `shlx eax, eax, edx`) | **100% safe, zero `unsafe`, zero panic paths** |

Why did `get_cabac_unchecked_cmov` degrade while `get_cabac_safe_idiomatic` matched hand-written assembly?
1. **`X86CmovConversion` profitability heuristic trap:** When written with `if is_lps { c.low -= r_mps << 17; ... }`, LLVM 22's `X86CmovConversion` pass observed that the LPS arm performs an extra memory load (`*tables.add(range_lps)`) and shift-subtract (`shl ecx, 0x11; sub eax, ecx`), estimated `cmov` critical-path latency as higher than predicted branch cost under default 50/50 static heuristics without PGO, and **lowered `select` into `cmp ecx, edx; jle 3a`**. Because CABAC context modeling adapts `pStateIdx` specifically to drive bin entropy toward 50/50 on residual syntax elements, converting `cmov`/masking into a conditional branch incurs severe branch mispredictions. Writing the arithmetic shift mask explicitly (`let lps_mask = (scaled_range.wrapping_sub(c.low)) >> 31;`) keeps the dataflow purely algebraic (`sub r10d, eax; sar r10d, 0x1f; and; sub; sub; and; add; xor`), preventing `X86CmovConversion` from introducing a branch.
2. **Eliminating GOT reloads and bounds checks simultaneously in safe Rust:** Passing `tables: &CabacTables` (`#[repr(C)]` struct packing `norm_shift: [u8; 512]`, `lps_range: [u8; 512]`, `mlps_state: [u8; 256]`) as a function parameter pins its base address in `rdx` across the entire CABAC bin loop (unlike FFmpeg's `"memory"` clobber in `__asm__ volatile`, LLVM can also keep `c.low` and `c.range` in registers across consecutive inlined `get_cabac_safe_idiomatic` calls!). Masking indices by power-of-two array lengths (`(q_range + s) & 0x1FF`, `(128 + s_masked) as usize & 0xFF`, `(c.range as usize) & 0x1FF`) allows LLVM 22 to discharge all three slice bounds checks statically with zero panic blocks while costing only two `and` instructions (`and ebx, 0x7f`; `and esi, 0x1ff`), and `-C target-cpu=x86-64-v3` replaces legacy `shl %cl` with single-cycle register-flexible BMI2 `shlx` (`c4 e2 69 f7 c9`).

#### 5.2 Register-Fused 6/8-Tap `vpmaddubsw` Motion Compensation (`core::arch` vs. `hevc/mc.asm`)

Dissecting `hevc_put_v8_row_avx2` (`mc_core_arch.rs`, 32-pixel-wide 8-tap vertical filter row in `core::arch::x86_64`) against `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (`libavcodec/x86/hevc/mc.asm:537-658`) establishes the exact boundary where `core::arch` achieves parity and where NASM retains an edge:
- **What LLVM 22.1.6 gets right (`mc_core_arch.o` offsets `0x0d..0x107`):**
  1. Emits four `vpbroadcastw ymm{2,3,0,1}, WORD PTR [rax+rcx*1 + {0,2,4,6}]` loads (`4` YMM registers holding the four adjacent tap pairs `[c0,c1]..[c6,c7]`, matching `hevc/mc.asm:642-653` `m12..m15`!).
  2. Emits eight `vmovdqu` row loads (`ymm4..ymm11`) with `lea rax, [rdx + rdx*2]` (`3 * stride`) and scaled SIB addressing `[rsi + rdx*1]`, `[rsi + rdx*2]`, `[rsi + rax*1]`, `[rsi + rdx*4]`, **zero stack spills** (using `ymm0..ymm12` = 13 of 16 YMM registers!), eight `vpunpcklbw`/`vpunpckhbw` interleaves, eight register-register `vpmaddubsw`, six tree-reduced `vpaddw` instructions (`vpaddw` depth 2 instead of serial depth 3!), rounding `vpaddw` + `vpsraw 6`, and `vpackuswb` store + `vzeroupper`.
- **Two subtle codegen differences vs. `hevc/mc.asm`:**
  1. **Redundant pre-clamping before `_mm256_packus_epi16` (`mc_core_arch.o` offsets `0xdf..0xfc`):**
     ```text
     df: vpxor        xmm1, xmm1, xmm1
     e3: vpmaxsw      ymm2, ymm2, ymm1
     e7: vpbroadcastw ymm3, WORD PTR [rip+0x0]  # .rodata constant 0x00ff
     f0: vpminsw      ymm2, ymm2, ymm3
     f4: vpmaxsw      ymm0, ymm0, ymm1
     f8: vpminsw      ymm0, ymm0, ymm3
     fc: vpackuswb    ymm0, ymm2, ymm0
     ```
     Although hardware `vpackuswb` (`PACKUSWB`) already saturates signed 16-bit integers to unsigned `[0x00, 0xFF]` natively, `stdarch`'s `const fn`-compatible lowering of `_mm256_packus_epi16` expands through portable `simd_clamp(0, 255)` + narrowing cast, and **LLVM `22.1.6` failed to fold `vpmaxsw(0) + vpminsw(255) + vpackuswb` into a bare `vpackuswb`**, emitting **6 redundant SIMD instructions and an extra `.rodata` broadcast (`0x00ff`) per 32 output pixels**. Calling `llvm.x86.avx2.packuswb` directly (or an inline `asm!` wrapper) recovers the single-instruction pack immediately.
  2. **128-bit lane ordering of `vpunpcklbw`/`vpunpckhbw` + `vpackuswb` and sliding-window row reuse:** Because AVX2 `vpunpcklbw`, `vpunpckhbw`, and `vpackuswb` operate *in-lane* on two independent 128-bit halves (`[0..7, 16..23]` and `[8..15, 24..31]`), `lo01` + `hi01` followed by `vpackuswb(out_lo, out_hi)` fortuitously cancels the lane permutation and writes `[0..31]` in exact sequential byte order! However, in a multi-row vertical filter loop (`height = 8, 16, 32, 64`), FFmpeg's `hevc/mc.asm` keeps 7 previously loaded pixel rows (`r1..r7`) live in `ymm` registers across loop iterations (loading only **1 new row** per output row instead of 8!) by fusing `[rfilterq + offset]` directly as the memory source operand of `pmaddubsw m0, [rfilterq + %3q*8]` (`hevc/mc.asm:586-589`), freeing 4 YMM registers (`m12..m15`) on 16-register x86-64. In `core::arch`, `_mm256_maddubs_epi16` takes two by-value `__m256i` registers; when 7 sliding rows + interleaved temporaries exceed 16 YMM registers (or 10 non-clobbered XMM registers before Win64 stack spills), LLVM either hoists the 4 filter vectors and spills pixel rows to `[rsp + disp]` or reloads rows from L1D.

## Boundaries

- **Not examined — AVX-512 EVEX mask-register (`k0..k7`) and Arm SVE/SME scalable-predication Pass-2 slices:** Only fixed-width x86-64 SSE2–AVX2 (`128`/`256`-bit), AArch64 NEON (`128`-bit), and RISC-V RVV 1.0 (`VLEN`-parametric integer vector) lifting and correspondence paths were examined. AVX-512 opmask registers and Arm SVE/SME variable-length ASL loops (where `ASLp` cannot unroll `VL`-parametric loops to loop-free `rASL` without fixing `VL`) were not examined.
- **Not examined — Mach-O `compact_unwind` (`__LD,__compact_unwind`) binary encoding:** While Mach-O `__TEXT,__text` and `__TEXT,__literal8` constant-pool relocations were verified via `rustc --target x86_64-apple-darwin`, binary equivalence of Mach-O compact unwind descriptors was not examined.
- **Unknown — Exact LLVM 22 pattern gap preventing `vpmaxsw`+`vpminsw`+`vpackuswb` folding:** Execution of `mc_core_arch.rs` established that `rustc 1.98.0-nightly` (LLVM `22.1.6`) emits redundant `vpmaxsw(0)` and `vpminsw(255)` instructions immediately before `vpackuswb` for `_mm256_packus_epi16`, whereas whether an upstream `stdarch` intrinsic call vs. an LLVM `X86ISelLowering` DAG combine rule is slated to fold that sequence in a subsequent LLVM 22 point update was not resolved from source alone (calling `llvm.x86.avx2.packuswb` directly or `core::arch::asm!` bypasses the 6-instruction penalty immediately).
- **Known not to apply — Unpatched `opencompl/sail-riscv-lean` and unpatched `leanprover/LNSym` as drop-in Pass-2 oracles:** Direct source inspection proves that unpatched `sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f` does **not** soundly over-approximate RVV 1.0 `vta`/`vma` `AGNOSTIC` lanes or `VLMAX < AVL < 2 * VLMAX` `vsetvli` strip-mining, and unpatched `LNSym@49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c` does **not** execute AArch64 `BTI`/`PACIASP` hints (`StateError.Unimplemented`).
- **Unsupported — `.o`-level lifting of RISC-V objects containing active `R_RISCV_RELAX` relocations:** Pre-link relocatable `.o` verification is unsupported when `R_RISCV_RELAX` is present because linker relaxation mutates instruction lengths and branch displacements after `.o` emission; verified RISC-V assembly/codegen units must disable relaxation (`.option norelax` / `-C target-feature=-relax`) or verify post-link DSO code segments.

## Evidence

### Primary Repository Revisions and Specifications
- **`FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`):**
  - `libavutil/x86/x86inc.asm`: Win64 register/XMM prolog/epilog (`lines 482-621`), `cglobal_internal` (`lines 826-861`), `const` hidden data (`lines 890-900`), and `.note.gnu.property` `SHSTK`-only `0x2` note (`lines 906-921`).
  - `libavutil/aarch64/asm.S`: `BTI c`/`BTI jc`/`paciasp` macros and `GNU_PROPERTY_AARCH64_FEATURE_1_AND` (`lines 213-262`), `movrel` PC-relative addressing (`line 313`).
  - `libavutil/riscv/asm.S`: `func`/`const` macros (`lines 46-76`), `Zicfilp` `lpad` macro (`lines 78-82`), and dynamic-LMUL `vtype_ivli`/`vtype_vli` (`lines 155-217`).
  - `libavcodec/cabac_functions.h` (`lines 85-130`) and `libavcodec/x86/cabac.h` (`lines 45-209`): C vs. x86-64 branchless `get_cabac_inline`.
  - `libavcodec/x86/hevc/mc.asm` (`lines 537-658`): 8-tap `pmaddubsw` memory-operand (`[rfilterq + ...]`) and register (`m12..m15`) motion-compensation macros.
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
  - `trusted/audit/TrustedBoundary.lean` (`lines 13-314, 439-596`): Pass-1 `RepoOrigin` vs. Pass-2 `CorrOrigin` authority lattices, tactic/syntax allowlists, and `trustLevel := 0` standalone kernel replay.
  - `trusted/audit/src/lib.rs` (`lines 18-89, 123-157`): `bwrap --unshare-all` sandboxed Pass-2 compilation, `LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`, and `LOCKED_PATCHED_MIRI_FILES`.
  - `trusted/correspondence/Trusted/Correspondence.lean` (`lines 31-126, 578-580`) and `trusted/rustc-capture/src/driver.rs` (`lines 25-85`).
- **`rust-lang/rust` (`ec65cd52bba13d491ff65c9d218b39753755c84a`) & `rust-lang/stdarch` (`ca26a96d57b295dcd927622877242940a0f3c02e`):**
  - `compiler/rustc_codegen_ssa/src/mir/block.rs` (`lines 1051-1066`), `compiler/rustc_codegen_llvm/src/intrinsic.rs` (`lines 911-999`), `compiler/rustc_codegen_llvm/src/attributes.rs` (`lines 453-465`), `compiler/rustc_codegen_ssa/src/target_features.rs` (`lines 174-187`).
  - `crates/core_arch/src/x86/avx2.rs` (`lines 1854-1875, 3740-3755`) and `crates/core_arch/src/x86/ssse3.rs` (`lines 288-303`).
- **`intelxed/xed` (`0bcb6237345c5066726dcc08b3d87928df3b5b26`):** `datafiles/cet/cet-isa.xed.txt` (`lines 45-69`, `ENDBR64`), `datafiles/hswavx/hsw-int256-isa.txt` (`line 525`), `datafiles/avx512-skx/skx-isa.xed.txt` (`lines 15511-15598`).
- **`rems-project/sail-arm` (`5416ef6b43e9527c38dc71fb752259c1d01a47e1`):** `arm-v9.4-a/lean/ArmExtras.lean` (`lines 19-23`, `decreasing_trivial => grind | decide | sorry`), `arm-v9.4-a/Makefile` (`lines 85-97`), `arm-v9.4-a/src/termination_measures.sail` (`lines 132-141`), `arm-v9.4-a/src/v8_base.sail` (`lines 10585-10595, 22591-22638`).
- **`UQ-PAC/ASLp` (`92e4fd949402056e16e3747e66922060be57ecc8`):** `libASL/rASL_check.ml` (`lines 15-296`), `libASL/dis.ml` (`lines 106-220`), `README.md` (`lines 320-331`, DOIs `10.34727/2023/isbn.978-3-85448-060-0_36` and `10.1007/978-3-031-74776-2_4`).
- **`leanprover/LNSym` (`49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`):** `Arm/Insts/BR/Hints.lean` (`lines 18-23`, `NOP`-only `exec_hints`).
- **`opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`) & `riscv/sail-riscv` (`ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`):**
  - `LeanRV64D/VextUtilsInsts.lean` (`lines 498-523, 663-666`) and `model/extensions/V/vext_utils_insts.sail` (`lines 427-445, 558-561`): deterministic `.AGNOSTIC => vd_val[i]`.
  - `LeanRV64D/VextVsetInsts.lean` (`lines 328-341`) and `model/extensions/V/vext_vset_insts.sail` (`lines 80-92`): `vl_use_ceil := false`.
  - `LeanRV64D/RiscvExtras.lean` (`lines 31-112`): 75 custom `axiom` declarations; `LeanRV64D/ZicfilpInsts.lean` (`lines 217-225`): `LPAD`.
- **Normative ISA Specification:** RISC-V "V" Vector Extension Specification, Version 1.0, §3.4.3 ("Vector Tail Agnostic and Vector Mask Agnostic `vta` and `vma`") and §6.2 ("Constraints on Setting `vl`").

### Executed Toolchain Probes (Observed `2026-11-20` on Linux x86-64)
Environment: `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `LLVM version: 22.1.6`), GNU Binutils `as`/`ld`/`objdump`/`readelf`.
1. **Cross-target `#![no_core]` object/relocation/unwind probe (`simd_obj.rs`):** Compiled with `rustc --edition 2024 --crate-type=lib -C panic=abort -C opt-level=3` across `x86_64-unknown-linux-gnu` (`-Z cf-protection=full`), `x86_64-pc-windows-msvc`, `x86_64-apple-darwin`, `aarch64-unknown-linux-gnu` (`-Z branch-protection=bti,pac-ret`), and `riscv64gc-unknown-linux-gnu` (`-C target-feature=+v`), inspected via `objdump -drw -M intel`, `objdump -h -r -s -j .pdata -j .xdata`, and `readelf -r -n`.
2. **CET-IBT `.note.gnu.property` downgrade probe:** Assembled an `x86inc.asm`-equivalent `.note.gnu.property` (`0xc0000002`, data `0x2` `SHSTK`-only) with `as`, linked against `elf_x86.o` (`0x3` `IBT, SHSTK`) using `ld -shared`, and verified via `readelf -n` that `IBT` disappeared from the linked DSO.
3. **CABAC & 8-tap HEVC `vpmaddubsw` codegen probes (`cabac_probe.rs`, `mc_core_arch.rs`):** Compiled with `rustc --edition 2024 --crate-type=lib -C opt-level=3 -C target-cpu=x86-64-v3 --emit=obj` (and `#[target_feature(enable = "avx2")]` on default target CPU for `mc_core_arch.rs`) and disassembled with `objdump -drw -M intel`.

## Revalidation

1. **Check `stdarch` `_mm256_packus_epi16` redundant clamp elimination on newer `rustc`/LLVM:**
   Compile a 6-line function `#[target_feature(enable = "avx2")] pub unsafe fn p(a: __m256i, b: __m256i) -> __m256i { _mm256_packus_epi16(a, b) }` with `rustc -C opt-level=3 --emit=asm -` and check whether `vpmaxsw`/`vpminsw` still precede `vpackuswb`. If absent, the 6-instruction `stdarch` `const fn` lowering overhead documented in Finding 5.2 has been folded upstream.
2. **Check FFmpeg `x86inc.asm` CET-IBT and Win64 SEH support:**
   Inspect `libavutil/x86/x86inc.asm` in any newer `FFmpeg/FFmpeg` revision with `grep -En "endbr64|0x00000003|seh_proc|xdata"` around `cglobal_internal` and `.note.gnu.property`. Until `cglobal` emits `endbr64` and `pr_data` includes bit `0x1`, linking unpatched FFmpeg NASM objects into CET-IBT DSOs strips `IBT`.
3. **Check `sail-arm` and `sail-riscv-lean` soundness status:**
   - In `rems-project/sail-arm`, inspect `arm-v9.4-a/lean/ArmExtras.lean` for `sorry` in `decreasing_trivial`.
   - In `opencompl/sail-riscv-lean`, grep `LeanRV64D/VextUtilsInsts.lean` for `| .AGNOSTIC =>` and `LeanRV64D/VextVsetInsts.lean` for `def vl_use_ceil` and `LeanRV64D/RiscvExtras.lean` for `^axiom `. If `.AGNOSTIC` still returns `vd_val[i]` or `vl_use_ceil` remains a boolean constant, the Pass-2 `UPSTREAM_PIN.json` consumer patches in Finding 4.2 remain mandatory.
4. **Check `LNSym` `BTI`/`PACIASP` hint execution:**
   Inspect `Arm/Insts/BR/Hints.lean` in `leanprover/LNSym` (`exec_hints`); if `inst.CRm != 0b0000#4` still branches to `StateError.Unimplemented`, BTI/PAC-enabled AArch64 objects still require patching `exec_hints` before symbolic simulation.
