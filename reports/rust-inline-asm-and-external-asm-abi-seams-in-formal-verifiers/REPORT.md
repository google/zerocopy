# Rust Inline Assembly and External Assembly ABI Seams in Formal Verifiers

## Summary

Soundly connecting Rust MIR program verification (`MiniRust`, `Miri`, `Anneal`) to ISA-level machine proofs across `core::arch::asm!`, `naked_asm!`, `global_asm!`, `#[target_feature]`, `core::arch` SIMD intrinsics, and external `.S`/NASM object symbols requires discharging **five hidden semantic seams** where abstract-machine memory, compiler backend assumptions, and hardware status/vector registers diverge:

1. **Formal Operational Gap Across `MiniRust`, `Miri`, and `Anneal` (`Basis: source`):** Neither `MiniRust` (`minirust/minirust` at `063d784186d3252bee242217f218223205c0b568`, `spec/lang/step/terminators.md:1-489`), `Miri` (`rust-lang/rust` `compiler/rustc_const_eval/src/interpret/step.rs:713-714`, throwing `"inline assembly is not supported"`), nor `Anneal`'s current baseline MIR semantics (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, mapping `InlineAsm` to `TerminatorKind.unsupported` in `trusted/lean/Trusted/MirAst.lean:782-796` and failing closed to `FaultKind.unsupported` in `trusted/lean/Trusted/MirSemantics.lean:51-52, 103-107`) assigns operational step semantics to inline or external assembly. Bridging a MIR verifier to an ISA model (`Sail`, `HOL Light`/`s2n-bignum`, `Jasmin`, `L3`) requires a **bi-directional state-refinement relation** lowering `AllocId`-provenance `AbstractByte` heaps (`Init(u8, Option<Provenance>) | Uninit`) into flat virtual-address bitvectors on entry and re-lifting post-state bytes while enforcing `Tree Borrows` aliasing permissions.
2. **Compiler-to-Hardware `vzeroupper` Blind Spot on Discarded `YMM`/`ZMM` Clobbers (`Basis: source + execution`):** In `rustc` (`rust-lang/rust` at `4b5350e87e487aed08ab2f9f0160a4b2616438bc`, `compiler/rustc_codegen_llvm/src/asm.rs:100-109, 762-773, 1126-1128`), discarded vector outputs (`out("ymm0") _`, `out("zmm0") _`) and `clobber_abi("C")` have `layout = None` and lower to `f32`-typed **`={xmm0}`** constraints in LLVM IR rather than `={ymm0}`. Consequently, LLVM's `X86InsertVZeroUpper` pass (`llvm/llvm-project` at `f61dfd8c0d8cfa6ed8a1ea3a16174d9673184825`, `llvm/lib/Target/X86/X86InsertVZeroUpper.cpp:117-154, 217-250`) sees only `X86::XMM0`, leaves the block in `PASS_THROUGH` rather than `EXITS_DIRTY`, and **omits `vzeroupper` before `retq` and subsequent calls**—verified empirically with `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`). By contrast, binding a typed 32-byte variable (`let _tmp: __m256i; out("ymm0") _tmp`) emits `=&{ymm0}` and triggers automatic `vzeroupper` insertion.
3. **Architecture-Specific Control/Status Register Hazards Under `options(preserves_flags)` (`Basis: normative + source`):** Under the Rust Reference (`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/inline-assembly.md:1368-1404`), `options(preserves_flags)` extends far beyond integer `NZCV`/`EFLAGS`:
   - On **AArch64**, `preserves_flags` requires preserving **`FPSR`** (`line 1383`), which holds the **cumulative NEON saturation bit `QC` (bit 27)** (`aapcs64.rst:898`). Any inline NEON DSP block executing saturating instructions (`uqadd`, `sqdmulh`, `sqrdmulh`, `uqxtn`) with `options(preserves_flags)` commits immediate Rust Undefined Behavior whenever saturation occurs.
   - On **RISC-V**, `preserves_flags` requires preserving **`vtype`, `vl`, `vxsat`, and `vxrm`** (`src/inline-assembly.md:1386`; `rustc_codegen_llvm/src/asm.rs:273-280`), making `vsetvli` illegal inside `preserves_flags` blocks; meanwhile, the RISC-V psABI (`riscv-cc.adoc:122-127`) mandates **`vstart == 0` on both entry and exit** of every procedure/ABI boundary regardless of `preserves_flags`.
   - On **x86/x86_64**, `EFLAGS.DF = 0` (`src/inline-assembly.md:1398-1399`) and `MXCSR` control bits (`RC`, `FTZ`, `DAZ`, exception masks `bits 6..15`) are unconditional entry/exit invariants even without `preserves_flags`.
4. **Partial-Vector Preservation Asymmetries Across Five Calling Conventions (`Basis: normative + source`):** Cross-platform external `.S`/NASM kernels (`FFmpeg` `x86inc.asm`, `rav1d`) confront asymmetric partial-register preservation laws: SysV AMD64 makes all `xmm0..31`/`ymm`/`zmm` volatile (with a `128`-byte red zone below `rsp`), Win64 makes **only the bottom `128` bits (`xmm6..15`)** of `zmm6..15` callee-saved (plus `32`-byte caller shadow space and zero red zone), AAPCS64 makes **only the bottom `64` bits (`d8..15`)** of `v8..15` callee-saved while reserving platform register `x18` (`aapcs64.rst:849, 867-872, 896`), RV64 LP64D makes all `v0..31` volatile in standard calls (`v1..7, v24..31` callee-saved under `riscv_vector_cc`) while fixing `gp`/`tp`, and OpenPOWER ELFv2 PPC64LE splits `vs14..31` (low `64`-bit FP callee-saved, upper `64`-bit volatile) while keeping `vr20..31` (`vs52..63`) `128`-bit callee-saved and anchoring TOC pointer `r2` at `24(r1)`.
5. **Provenance, `MaybeUninit` SIMD Over-Reads, Tree Borrows, and `#[target_feature]` Capability Tokens (`Basis: normative + source + execution`):** Passing pointers across `asm!` or `extern "C"` assembly requires (a) deriving mutable pointers from an `Active`/`Reserved` root without live `Frozen` (`&[T]`) or conflicting `Protected` (`&mut [T]`) borrows (`minirust` `spec/mem/tree_borrows/state_machine_protected.md`), (b) proving a **de-poisoning / `Uninit`-erasure refinement lemma** whenever wide SIMD loads over-read `MaybeUninit<u8>` tail padding, and (c) guarding `#[target_feature]` entry (which Miri diagnoses as immediate UB on missing features in `src/machine.rs:1212-1239`) with zero-sized proof-carrying CPU capability tokens (`CpuToken<Avx2>`) backed by `CPUID` + **`XGETBV(0)` OS `XCR0` state-save verification**.

## Applicability

This report applies to formal verifiers, verified compilers, and low-level systems/multimedia libraries in Rust that invoke `core::arch::asm!`, `core::arch::naked_asm!`, `core::arch::global_asm!`, `#[target_feature]`, `core::arch` vendor SIMD intrinsics, or external C-ABI assembly objects (`.S`, GAS, NASM, Yasm).

- **Relationship to Existing Corpus Coverage:**
  This package complements and cites—without duplicating—existing corpus reports:
  - `rust-inline-assembly-contracts-relocations-and-simd-correspondence` establishes `out` vs. `lateout` register-allocation quantifier order, Charon ULLBC `InlineAsm` erasure, ELF/Mach-O relocation adjacency, and Kraken `aarch64`/`x86_64` execution pilots.
  - `rustc-inline-assembly-specification-llvm-lowering-and-assembler-syntax` specifies `rustc_builtin_macros::asm` operand parsing, register classes, modifiers, LLVM constraint string syntax, and LLVM integrated assembler directives.
  - `machine-code-verification-frameworks-and-assembly-contracts`, `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`, `target-features-implications-detection-and-abi-effects`, `vendor-intrinsic-specifications-stdarch-verification-and-lean-generation`, `rvv-lmul-vtype-hazards-arm-sme-streaming-za-tiles-and-ffload-speculation`, and `minirust-tree-borrows-protectors-and-program-logic-correspondence` cover general machine-code verification taxonomies, `PassMode`/`FnAbi` C-unwind metadata, Rust/LLVM target-feature implication tables, `stdarch` XML/JSON generation, RVV `LMUL`/Arm SME `ZA` tile mechanics, and pure-Rust Tree Borrows logics respectively.
  - The present report focuses specifically on the **semantic verification contract at the MIR-to-ISA seam**: how `MiniRust`/`Miri`/`Anneal` abstract-machine states relate to concrete ISA states across `asm!` options, hidden vector/CSR clobbers (`vzeroupper`, `MXCSR`, `FPCR`/`FPSR.QC`, `vstart`), the five-architecture ABI preservation matrix (SysV AMD64, Win64, AAPCS64, RV64 LP64D, PPC64LE ELFv2), `Tree Borrows` + `AbstractByte::Uninit` over-read soundness, and capability-typed `#[target_feature]` runtime dispatch.

## Findings

### 1. Anatomy of the Rust MIR-to-ISA Semantic Seam in `MiniRust`, `Miri`, and `Anneal`

`Basis: source`

Across all five mechanisms by which Rust executes target-specific SIMD or machine instructions, the Rust Abstract Machine (`AM`) and the hardware Instruction Set Architecture (`ISA`) speak incompatible state ontologies:

| Surface Mechanism | Representation in `rustc` Runtime MIR (`rustc_middle::mir`) | `MiniRust` (`063d784186`) & `Miri` (`5b99fdad63`) Status | `Anneal` (`c131b320ee`) Status | Residual Soundness Seam Requiring Formal Contract |
| :--- | :--- | :--- | :--- | :--- |
| `core::arch::asm!` | `TerminatorKind::InlineAsm` (`terminator.rs`) | Absent in `MiniRust` (`terminators.md`); rejected in `rustc_const_eval/src/interpret/step.rs:713-714` | Mapped to `TerminatorKind.unsupported` (`MirAst.lean:782-796`) $\to$ `FaultKind.unsupported` (`MirSemantics.lean:103-107`) | Universal register-allocator quantification, `options(...)` effects, hidden CSRs, `vzeroupper`, `Tree Borrows` & `Uninit` refinement |
| `#[unsafe(naked)]` + `naked_asm!` | Custom module ASM emission; callable as `FnDef` / `fn` ptr | Unsupported (no MIR body with Rust locals) | No body in `MirSemantics` (`initState` / `.call` fails closed if unmodeled) | Full calling-convention entry/exit compliance, stack alignment, `.cfi_*` / `.seh_*` unwind metadata |
| `core::arch::global_asm!` | Module-level textual assembly (`rustc_ast::ast`) + `extern "C"` decl | Opaque foreign symbol | External symbol outside `Program.bodies` (`MirSemantics.lean:1700`) | Linker symbol binding (no interposed/mismatched relocation), full target psABI preservation |
| External `.S` / NASM (`cc`, `nasm-rs`) | `extern "C"` / `extern "sysv64"` / `extern "win64"` `TerminatorKind::Call` | Foreign shim missing unless custom-hooked (`foreign_items.rs`) | External callee obligation (`MirAst.lean:876`) | Cross-ABI signature erasure (e.g. Win64 vs. SysV `rav1d` `wrap_fn_ptr!`), `XMM6..15` / `D8..15` spills, `x18` / `r2` reservation |
| `core::arch` SIMD intrinsics | `#[target_feature]` wrapper calling `simd_*` or LLVM intrinsic | Subset emulated in `miri/src/intrinsics/{x86,aarch64}`; `target_feature` checked (`machine.rs:1212`) | Requires intrinsic semantics + `#[target_feature]` precondition | Miri erases `MXCSR` FTZ/DAZ, `vzeroupper`, cache/NT hints, and x86 vs. Arm hardware corner-case differences unless explicitly modeled |

#### 1.1 Exact Four-Component State-Bridge Relation $\mathcal{R}(\sigma_{\text{MIR}}, \sigma_{\text{ISA}})$

`Basis: source + derived`

In `MiniRust` (`spec/mem/interface.md:1-167`, `spec/mem/pointer.md:1-193`), memory is a collection of disjoint allocations indexed by abstract `AllocId`, where each byte is an `AbstractByte<Provenance> ::= Init(u8, Option<Provenance>) | Uninit`, pointers carry `Provenance` (`AllocId` + Tree Borrows `Tag`), and `Stack` frames hold typed MIR locals unmapped to physical addresses unless their address is taken. In an ISA model (`Sail`, `s2n-bignum` HOL Light `x86state`/`armstate`, `Jasmin`), memory is a flat total map $\text{Mem}_{\text{ISA}} : \text{Word64} \to \text{Word8}$ with zero provenance or initialization tags, alongside a physical register file (`GPR`, `SIMD`, `Flags`, `CSR`, `SP`, `PC`).

To verify an `asm!` block or external `.S`/NASM call with precondition $P_{\text{MIR}}$ and postcondition $Q_{\text{MIR}}$ without introducing unsound axioms into `TrustedBoundary.lean` (`joshlf/anneal`, `trusted/audit/TrustedBoundary.lean:25`), the formal bridge must witness a concrete address valuation $\alpha : \text{AllocId} \rightharpoonup \text{Word64}$ satisfying four coupled obligations:

1. **Spatial Realizability and Alignment:** Every live address-taken allocation $a \in \text{dom}(\alpha)$ occupies $[\alpha(a), \alpha(a) + \text{size}(a)) \subset [1, 2^{64})$ disjointly from all other live allocations, the machine code region $[\text{pc}, \text{pc} + |\text{mc}|)$, and the active scratch stack frame $[\text{sp} - S_{\text{scratch}}, \text{sp} + S_{\text{red/shadow}})$, with $\alpha(a) \equiv 0 \pmod{\text{align}(a)}$.
2. **One-Way `AbstractByte` Lowering (`Init` Exactness, `Uninit` Nondeterministic Refinement):**
   - If $\sigma_{\text{MIR}}[a, i] = \text{Init}(b, \pi)$, then $\text{Mem}_{\text{ISA}}[\alpha(a) + i] = b$.
   - If $\sigma_{\text{MIR}}[a, i] = \text{Uninit}$, then $\text{Mem}_{\text{ISA}}[\alpha(a) + i] = v_{a,i}$ for a **universally quantified arbitrary concrete byte** $v_{a,i} \in [0, 255]$ (`r[asm.rules.reg-not-input]` in `rust-lang/reference` `src/inline-assembly.md:1326-1328`: hardware bytes/registers hold deterministic arbitrary bitvectors, *not* multi-valued LLVM `undef`).
   - Crucially, if the assembly kernel writes a byte back to $(\alpha(a) + j)$ that will be read by Rust as an initialized `u8`/`i16` (`Init(b', None)`), the ISA proof must show that **$b'$ is functionally independent of every universally quantified `Uninit` byte $v_{a,i}$** ($\forall v, v'.\; b'(v) = b'(v')$). This single quantifier discipline makes **wide SIMD tail over-reads of `MaybeUninit<u8>` padding completely sound**!
3. **`options(...)` Effect Framing (`src/inline-assembly.md:1078-1238, 1338-1367`):**
   - `options(nomem)`: $\text{Mem}_{\text{ISA}}$ outside assembly-private stack scratch $[\text{sp} - S_{\text{priv}}, \text{sp})$ is neither read nor written (frame identity + zero read-footprints in `memaccess_inbounds`).
   - `options(readonly)`: $\text{Mem}_{\text{ISA}}$ outside private stack scratch is read-only ($\forall p \notin \text{Stack}_{\text{priv}}.\; \text{Mem}'_{\text{ISA}}[p] = \text{Mem}_{\text{ISA}}[p]$), and no cross-thread synchronization/fence edge is relied upon.
   - `options(pure)`: Requires `nomem` or `readonly`, **termination** (`must eventually return`, `line 1079`), and determinism of output registers solely as a mathematical function of direct input operands (plus permitted `readonly` memory).
   - `options(nostack)`: Prohibits any write to $[\text{sp} - \infty, \text{sp})$ (including `push` and SysV `128`-byte red zone) and drops the compiler's entry `16`-byte call-alignment guarantee on `sp` (`line 1230`).
4. **Universal Register-Allocator Quantification (`out` vs. `lateout`):** As proved in `rust-inline-assembly-contracts-relocations-and-simd-correspondence`, the ISA proof must quantify over all valid physical register assignments $\rho$ mapping register-class operands (`reg`, `xmm_reg`, `ymm_reg`, `vreg`) such that non-`lateout` outputs are disjoint from all inputs and other outputs, whereas `lateout` outputs may alias `in` registers.

---

### 2. Hidden Vector, Flag, and Control-Register Clobber Seams

#### 2.1 The `rustc` $\to$ LLVM `X86InsertVZeroUpper` Blind Spot on Discarded `YMM`/`ZMM` Clobbers

`Basis: source + execution`

On x86_64 processors implementing AVX/AVX2/AVX-512, executing any 256-bit `YMM0..YMM15` or 512-bit `ZMM0..ZMM15` instruction transitions the microarchitectural upper-vector state machine to `DIRTY`. Calling or returning into legacy 128-bit SSE code while `YMM0..15` upper bits are dirty triggers severe AVX-to-SSE transition penalties (or false register merge dependencies on modern cores). Both `FFmpeg` (`libavutil/x86/x86inc.asm:374, 617-618`) and LLVM (`llvm/lib/Target/X86/X86InsertVZeroUpper.cpp:115-259`) enforce an ABI-boundary invariant that functions exit in the `CLEAN` state unless passing/returning `YMM`/`ZMM` values by register:
- Notice that **EVEX high registers `ZMM16..ZMM31` do not alias legacy `XMM` registers and never trigger dirty-upper state**: `FFmpeg`'s `x86inc.asm:374, 1073` encodes `%define vzeroupper_required (mmsize > 16 && (ARCH_X86_64 == 0 || xmm_regs_used > 16 || notcpuflag(avx512)))`, and LLVM's `isYmmOrZmmReg` (`X86InsertVZeroUpper.cpp:115-120`) explicitly checks `(Reg >= X86::YMM0 && Reg <= X86::YMM15) || (Reg >= X86::ZMM0 && Reg <= X86::ZMM15)`, ignoring `ZMM16..ZMM31`!

However, combining `rustc`'s inline-assembly lowering (`compiler/rustc_codegen_llvm/src/asm.rs`) with LLVM's `X86InsertVZeroUpper.cpp` exposes a subtle **compiler seam**:
1. In `rustc_codegen_llvm/src/asm.rs:100-109`, when an `asm!` output is discarded (`out("ymm0") _`), `place` is `None`, so `layout` is `None` and `dummy_output_type` (`lines 1126-1128`) chooses `cx.type_f32()`.
2. In `reg_to_llvm` (`asm.rs:762-773`), when `layout` is `None`, `rustc` unconditionally selects register prefix `'x'` (`// We use f32 as the type for discarded outputs`), lowering `out("ymm0") _` and `out("zmm0") _`—as well as `clobber_abi("C")` (`src/inline-assembly.md:1058`)—to **`=&{xmm0}` / `={xmm0}`** in LLVM IR!
3. When `X86InsertVZeroUpper.cpp` scans the basic block (`lines 217-222`), `hasYmmOrZmmReg(MI)` (`lines 142-154`) sees `X86::XMM0` rather than `X86::YMM0`, leaves `CurState = PASS_THROUGH`, and **emits zero `vzeroupper` instructions**!

Executing `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `-O --emit=llvm-ir,asm` on `x86_64-unknown-linux-gnu`; full reproducer in Section `## Evidence`) confirms all three cases:
- `asm!("vpcmpeqb ymm0, ymm0, ymm0", out("ymm0") _)` $\longrightarrow$ LLVM IR `call float asm ... "=&{xmm0},..."` $\longrightarrow$ assembly exits with `popq %rax; retq` (**no `vzeroupper`**).
- `asm!("vpcmpeqb ymm0, ymm0, ymm0", clobber_abi("C"))` $\longrightarrow$ LLVM IR `={xmm0}..={xmm15},~{xmm16}..~{xmm31}` $\longrightarrow$ assembly exits with `popq %rax; retq` (**no `vzeroupper`**).
- `let _tmp: __m256i; asm!("vpcmpeqb ymm0, ymm0, ymm0", out("ymm0") _tmp)` $\longrightarrow$ LLVM IR `call <4 x i64> asm ... "=&{ymm0},..."` $\longrightarrow$ assembly emits **`vzeroupper` before `retq`**.

**Rule for Rust Verifiers and Authors:** Any x86/x86_64 `asm!` block touching `ymm0..15` or `zmm0..15` without returning/binding a 32/64-byte typed Rust variable **must either execute `vzeroupper` inside the `asm!` template before exit or bind dummy outputs to typed `__m256i`/`__m512i` locals**.

#### 2.2 Control and Status Register Traps: `FPSR.QC`, `MXCSR`, `FPCR`, `EFLAGS.DF`, and `vstart`

`Basis: normative + source`

Formal verifiers frequently model `options(preserves_flags)` as "does not clobber integer condition codes (`ZF/CF/SF/OF` or `NZCV`)." Inspection of `rust-lang/reference` (`src/inline-assembly.md:1368-1404`), `rustc_codegen_llvm/src/asm.rs:259-280`, `ARM-software/abi-aa` (`aapcs64/aapcs64.rst:881-915`), and `riscv-non-isa/riscv-elf-psabi-doc` (`riscv-cc.adoc:96-128`) proves that model **unsound**:

1. **AArch64 `FPSR.QC` Cumulative Saturation Trap (`src/inline-assembly.md:1381-1383`, `aapcs64.rst:898`):**
   Normative rule `r[asm.rules.preserved-registers]` requires an AArch64 `asm!` block with `options(preserves_flags)` to preserve **both `NZCV` and `FPSR`**. Under AAPCS64 (`aapcs64.rst:898`), `FPSR` contains floating-point cumulative exception flags (`IDC, IXC, UFC, OFC, DZC, IOC`) **and bit 27 `QC` (sticky SIMD saturation)**. Every AArch64 NEON saturating arithmetic or narrowing instruction (`UQADD`, `SQADD`, `UQSUB`, `SQSUB`, `SQDMULH`, `SQRDMULH`, `SQXTN`, `UQXTN`, `SQXTUN`) sets `FPSR.QC := 1` upon saturation! Marking such an `asm!` block `options(preserves_flags)` violates the Rust AM contract. Meanwhile, `FPCR` (`aapcs64.rst:900-906`: rounding mode `bits 22:23`, flush-to-zero `FZ bit 24`, `NEP bit 2 == 0` on entry/exit) must **always** be preserved across both `asm!` and `extern "C"` boundaries, even when `preserves_flags` is omitted.
2. **RISC-V `vtype`/`vl`/`vxrm`/`vxsat` vs. Unconditional `vstart == 0` (`src/inline-assembly.md:1384-1386`, `riscv-cc.adoc:108-128`):**
   When `preserves_flags` is omitted on RISC-V, `rustc` appends `~{fflags},~{vtype},~{vl},~{vxsat},~{vxrm}` (`asm.rs:273-279`). Consequently, **executing `vsetvli` or any fixed-point RVV instruction writing `vxsat` inside `options(preserves_flags)` is instant UB**. Conversely, `vstart` is *not* in the clobber list because `riscv-cc.adoc:122-127` mandates an **unconditional ABI invariant**: *"Procedures may assume that `vstart` is zero upon entry. Procedures may assume that `vstart` is zero upon return... Any procedure that does explicitly write `vstart` to a nonzero value must zero `vstart` before either returning or calling another procedure."* Leaving `vstart != 0` on exit from `asm!` or external `.S` silently corrupts subsequent compiler-generated RVV instructions by skipping elements `0 .. vstart - 1`.
3. **x86_64 `MXCSR` Split and `EFLAGS.DF = 0` (`src/inline-assembly.md:1370-1373, 1397-1400`):**
   On x86/x86_64, `MXCSR` is split across two contracts: sticky exception flags (`PE, UE, OE, ZE, DE, IE`, bits `0..5`) are volatile across calls and `asm!` unless `preserves_flags` is set (`line 1373`), whereas control bits (`DAZ` bit 6, exception masks bits `7..12`, rounding control `RC` bits `13..14`, `FTZ` bit 15; standard default `0x1F80`) are **non-volatile ABI state** that an external DSP kernel or `asm!` block must restore before returning (toggling `FTZ`/`DAZ` for audio denormal flushing without restoring `MXCSR` breaks downstream IEEE-754 Rust semantics). Similarly, `EFLAGS.DF` must be `0` on entry and exit (`line 1398`); leaving `DF = 1` (`std` without `cld`) causes compiler-emitted `rep movsb` (`memcpy`) to copy backward in memory.

---

### 3. Five-Architecture Calling-Convention Seam Matrix for External `.S`/NASM Kernels

`Basis: normative + source`

When multimedia codecs (`FFmpeg`, `dav1d`, `rav1d`) link hand-written NASM or GAS assembly via `extern "C"` (or explicit `extern "sysv64"` / `extern "win64"`), formal verification must check exact ABI compliance at symbol boundaries:

| Architectural Dimension | SysV AMD64 (`x86_64` Unix) | Microsoft Win64 (`x86_64` Windows) | Arm AAPCS64 (`aarch64`) | RISC-V RV64 LP64D + RVV | OpenPOWER ELFv2 (`ppc64le`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Int Arg Registers** | `rdi, rsi, rdx, rcx, r8, r9` | `rcx, rdx, r8, r9` (`4` regs; 5th+ on stack) | `x0..x7` (`x8` indirect sret) | `a0..a7` (`x10..x17`) | `r3..r10` (`8` regs) |
| **FP / Vector Arg Regs** | `xmm0..xmm7` | `xmm0..xmm3` (positional with int!) | `v0..v7` (`z0..z7, p0..p3` SVE CC) | `fa0..fa7`; `v0, v8..v23` (`riscv_vector_cc` only) | `f1..f13`, `v2..v13` |
| **Callee-Saved GPRs** | `rbx, rbp, r12..r15` | `rbx, rbp, rdi, rsi, r12..r15` | `x19..x28, x29(fp), x30(lr)` | `s0..s11` (`x8..9, x18..27`) | `r14..r31`, `cr2..cr4` |
| **Reserved / Anchor GPRs** | `rsp` | `rsp` | **`x18` platform reg** (`aapcs64.rst:849, 867`: TLS/macOS/Android SCS — never touch!) | **`gp` (`x3`), `tp` (`x4`)** (`riscv-cc.adoc:19-29`: signal handlers rely on them!) | **`r2` TOC pointer**, `r13` TLS (`r12` global entry addr; save `r2` at `24(r1)`) |
| **Callee-Saved Vector Bits (Partial-Width Asymmetry!)** | **None** (`xmm0..31`, `ymm`, `zmm` all caller-saved) | **`xmm6..xmm15` bits `[127:0]` ONLY** (`ymm6..15[255:128]` & `zmm16..31` volatile!) | **`v8..v15` bits `[63:0]` (`d8..d15`) ONLY** (`v8..15[127:64]` volatile; SVE CC saves full `z8..z23, p4..p15`) | **None** in standard CC (`riscv-cc.adoc:108`); `v1..v7, v24..v31` full-width in `riscv_vector_cc` (`:145-147`) | **`f14..f31` (`vs14..31` low `64`b)** + **`vr20..vr31` (`vs52..63` full `128`b)** (`vs0..13, vr0..19` & upper `64`b of `vs14..31` volatile) |
| **Red Zone / Caller Frame Scratch** | **`128` B below `rsp`** (forbids `push` under `options(nostack)`) | **`0` B red zone**; mandatory **`32` B shadow space** `[rsp+8..rsp+40)` above retaddr | **`0` B** mandated by AAPCS64 (OS-dependent; treat below `sp` as volatile to signals) | **`0` B red zone** | **`288` B** below `r1` (`16` B `lr` save at `16(r1)` + `24(r1)` TOC in **caller** frame!) |
| **Entry `SP` Alignment** | `16` B before `call` (`rsp % 16 == 8` at entry) | `16` B before `call` (`rsp % 16 == 8` at entry) | **`sp % 16 == 0` hardware-enforced** on any `sp` mem access! | `sp % 16 == 0` at call boundary | `r1 % 16 == 0` (`32` B min frame if allocating) |

- **Machine-Checked Partial-Vector Lens Proof Pattern (`s2n-bignum` `x86/proofs/mlkem_ntt.ml:1345-1427` & `FFmpeg` `x86inc.asm:560-605`):**
  In `FFmpeg` (`x86inc.asm:560-605`), `WIN64_SPILL_XMM` allocates `16 * N + 32` stack bytes whenever `xmm_regs_used > 6 + high_mm_regs` and spills `movaps [rsp + ...], xmm6..xmm15`. In `awslabs/s2n-bignum` (`280a220986a0bc6249248187717a771153d073db`), `MLKEM_NTT_NOIBT_WINDOWS_SUBROUTINE_CORRECT` (`x86/proofs/mlkem_ntt.ml:1347-1356, 1425-1426`) formalizes this exact asymmetry via sub-register lens composition `ENSURES_PRESERVED_TAC "init_xmm6" (ZMM6 :> bottomhalf :> bottomhalf)` paired with `MAYCHANGE_ZMM_QUARTER`, proving that `vmovdqa` of `128`-bit `xmm6..15` plus `vzeroupper` satisfies the Win64 contract even after `ymm6..15` were clobbered during the kernel. Similarly, `arm/proofs/mlkem_ntt.ml:552-554` discharges AAPCS64 `[D8; D9; D10; D11; D12; D13; D14; D15]` (`64` bytes) preservation while mutating full 128-bit `Q8..Q15`.
- **Cross-ABI Wrapper Hazard in Hybrid Rust+ASM Codecs (`rav1d` `src/wrap_fn_ptr.rs:41-99`):**
  `rav1d` declares assembly kernels as `unsafe extern "C" fn(...)` (`wrap_fn_ptr.rs:42, 49, 86`). On `x86_64-pc-windows-msvc`, `extern "C"` resolves to `win64`, so the NASM assemble-time configuration (`ARCH_X86_64` + `WIN64` in `x86inc.asm`) **must** match the exact target triple's `"C"` ABI; compiling NASM objects with `-DARCH_X86_64=1 -DWIN64=0` and calling them via `extern "sysv64"` on Windows works for leaf kernels *only* if Structured Exception Handling (`.seh_proc`/`.seh_savereg` in `src/inline-assembly.md:1697-1704`) is never triggered by a page fault or debugger walk inside the assembly frame.

---

### 4. Pointer Provenance, `Tree Borrows`, and `MaybeUninit` Across ASM Seams

`Basis: normative + source + execution`

Under `rust-lang/reference` `r[asm.rules.mem-same-as-ffi]` (`src/inline-assembly.md:1338-1343`), *"The set of memory locations that assembly code is allowed to read and write are the same as those allowed for an FFI function."* Evaluating this rule against `MiniRust`'s `Tree Borrows` state machine (`minirust/minirust` `spec/mem/tree_borrows/state_machine_protected.md` & `state_machine_unprotected.md`) and `Miri` establishes four concrete obligations for verified Rust wrappers around SIMD assembly (verified by the executable state-machine probe in `## Evidence`):

1. **Never Derive Mutable ASM Pointers From Shared References (`&T` / `slice.as_ptr()`):**
   Casting `&[u8]` $\to$ `*const u8` $\to$ `in(reg) ptr` creates a `Frozen` (read-only) tag in Tree Borrows (`SharedReadOnly` in Stacked Borrows). Any write through that address inside `asm!` or external `.S`—even writing back the *exact same byte value* (`vmovdqu` read-modify-write masking on tail lanes!)—is **immediate Undefined Behavior** (`Frozen` + child write $\to$ `UB`; `Frozen` + foreign write under protector $\to$ `UB`). In-place or masked-store kernels (`loopfilter`, `cdef`, `itx_add`) must derive `*mut u8` from `&mut [u8]` (`slice.as_mut_ptr()`, `Reserved`/`Active`) or `&UnsafeCell<[u8]>`.
2. **Release Conflicting Reference Protectors Before Entering ASM on Overlapping Planes:**
   In video motion compensation and loop restoration, intra-block copy (`Intrabc`) or overlapping ring-buffer windows may read and write within the **same backing allocation**. Holding a Rust `&mut [u8]` (`dst`) and `&[u8]` (`src`) as function parameters attaches **function-lifetime `Protector`s** (`state_machine_protected.md`): any foreign read against a `Protected Active` byte or foreign write against a `Protected Frozen`/`Reserved` byte is **immediate UB** (even if the assembly executes sequentially!). Sound Rust wrappers must slice disjoint rows via `split_at_mut`, or pass a single raw `*mut Pixel` + signed `stride: isize` derived from one `&mut FramePlane` allocation root with a pure spatial-separation precondition over accessed index sets.
3. **Pointer-to-Integer Provenance Exposure Across `in(reg)`:**
   Passing `p: *mut u8` into `in(reg) p` passes an address in a machine GPR; if the `asm!` block computes a pointer into a *different* Rust allocation by integer arithmetic (`ptr_a + (addr_b - addr_a)`), the resulting memory access violates `MiniRust` allocation-bounded provenance (`spec/mem/pointer.md`) unless `addr_b`'s provenance was previously exposed (`p_b.expose_provenance()`, `spec/mem/intptrcast.md:1-43`). Within a single allocation $a$, pointer arithmetic `p.wrapping_offset(y * stride + x)` preserves $a$'s provenance cleanly without exposing global provenance.
4. **Sound `MaybeUninit<u8>` Tail Over-Read Discipline:**
   When a Rust caller holds `&[u8]` of length `w = 4`, reading `16` bytes via `core::ptr::read_unaligned::<u128>(ptr.cast())` in pure Rust MIR is **double UB**: out-of-bounds of the `4`-byte slice *and* typed load of potentially `Uninit` padding bytes (`MirSemantics.lean:83-87`). By contrast, if the backing buffer is allocated as `&[MaybeUninit<u8>]` of length $\ge w + 12$ and passed via `buf.as_ptr()` into `asm!` (or a `core::arch` vector load intrinsic whose target contract loads register lanes without asserting scalar `Init` on unused lanes) that masks out lanes `4..15` before storing `4` bytes (`movd [dst], xmm0`), the state-bridge relation $\mathcal{R}$ (Section 1.1) proves the boundary **100% UB-free**.

---

### 5. Sound Runtime CPU-Feature Dispatch (`#[target_feature]` + `XGETBV` Capability Witnesses)

`Basis: normative + source`

In Rust (`rust-lang/reference` `src/attributes/codegen.md`; `rust-lang/miri` `src/machine.rs:1212-1239` & `src/helpers.rs:893-905`), calling an `unsafe fn` annotated with `#[target_feature(enable = "avx2")]` on a host CPU lacking `avx2` is **language-level Undefined Behavior at the call site itself**, even if the function dynamically branches around AVX2 intrinsics—because LLVM attaches `"target-features"="+avx2,..."` to the entire function (`vzu_probe.ll` `attributes #0`) and may hoist AVX2 instructions (`vpxor`, `vmovdqu` prologue spills) above user branches!

Furthermore, raw `CPUID` leaf `7` (`EBX` bit 5 = `AVX2`) is **insufficient** to guarantee that executing `vpaddd ymm0, ...` will not trap with `#UD` (Invalid Opcode):
1. **Mandatory Two-Gate OS State-Save Check (`CPUID` + `XGETBV(0)`):** A hypervisor or OS kernel booted with `noxsave` leaves `CR4.OSXSAVE = 0` or clears `XCR0[2:1]` (`YMM`/`XMM` save enable), causing any VEX-encoded AVX/AVX2 instruction to fault with `#UD` despite `CPUID.(EAX=7,ECX=0):EBX.AVX2 == 1`! Sound x86_64 detection (`std_detect` and `FFmpeg` `libavutil/x86/cpu.c` / `rav1d` `src/cpu.rs`) must verify:
   - For **AVX/AVX2**: `CPUID.01H:ECX.OSXSAVE[bit 27] == 1` $\land$ `(XGETBV(0) & 0x6) == 0x6` (`XCR0.SSE[1]` and `XCR0.AVX[2]` enabled) $\land$ `CPUID.07H:EBX.AVX2[bit 5] == 1`.
   - For **AVX-512**: Additionally `(XGETBV(0) & 0xE6) == 0xE6` (`XCR0.opmask[5]`, `ZMM_Hi256[6]`, `Hi16_ZMM[7]` all enabled by OS—note macOS Darwin leaves `XCR0[7:5] = 0` at process entry and lazily enables or rejects AVX-512 differently from Linux!).
   - For **AArch64 / RISC-V Linux**: User-space cannot read `ID_AA64ISAR0_EL1` or `misa` directly without kernel trap/emulation; sound dispatch reads `getauxval(AT_HWCAP)` / `AT_HWCAP2` (or Linux `riscv_hwprobe` syscall for fast misaligned vector access `RISCV_HWPROBE_KEY_CPUPERF_0` + `Zve64x`/`V`, matching `FFmpeg` `checkasm.c:362-369`).
2. **Zero-Cost Verified Dispatch Pattern (`CpuToken<Feat>`):**
   Instead of scattering `unsafe` `is_x86_feature_detected!("avx2")` checks at every hot inner loop—or storing raw untyped `extern "C" fn` tables initialized via `OnceLock`/`AtomicUsize` (`rav1d` `src/cpu.rs`)—a clean-rewrite verifier encapsulates the `CPUID + XGETBV` / `HWCAP` proof inside a single trusted constructor `Avx2Token::try_new() -> Option<Avx2Token>` (a zero-sized `Copy` struct whose private field witnesses the Ghost proposition `HostSupports("avx2")`). Safe wrapper functions `pub fn filter_8tap_avx2(_tok: Avx2Token, dst: &mut [u8], ...)` then discharge the `#[target_feature(enable = "avx2")]` call precondition statically in `Anneal`/`Verus` with **zero runtime branch overhead** inside frame/tile loops and **`0` bytes** of struct/register footprint.

## Boundaries

- **Not Examined — Self-Modifying / JIT-Patched Assembly:** Although `rust-lang/reference` `r[asm.rules.black-box]` (`src/inline-assembly.md:1347, 1490`) permits target-specific runtime code patching inside `asm!` and `naked_asm!`, instruction-cache coherence (`ISB` on AArch64, `FENCE.I` on RISC-V, serializing `CPUID` on x86) for JIT/self-modifying media code is **not examined** (see sibling report `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement`).
- **Not Examined — Hardware Performance Counter / Speculative Side-Channel Leakage Across Media ASM:** Unlike cryptographic assembly (`DOIT` in `Jasmin`, `consttime.ml` in `s2n-bignum`), multimedia codecs intentionally use data-dependent branches (e.g., all-zero transform block skip, `msac`/`cabac` early exit) and variable-latency gathers; constant-time side-channel preservation across media `asm!` seams is **not examined**.
- **Unsupported — Operational Execution of `InlineAsm` in Current `Miri` (`5b99fdad63`), `MiniRust` (`063d784186`), and `Anneal` (`c131b320ee`):** Direct execution or verification of `TerminatorKind::InlineAsm` without external/compositional contract discharge is **unsupported** in all three tools today (`MirAst.lean:782-796` maps `InlineAsm` to `.unsupported`).
- **Known Not to Apply — Assuming `out("ymm0") _` or `clobber_abi("C")` Emits `vzeroupper` in `rustc` (`14210df0e2` / `4b5350e87e`):** As proved by source inspection and execution in Section 2.1, assuming `rustc` + LLVM automatically clean upper `YMM`/`ZMM` state after discarded-output `asm!` clobbers **is known not to apply**.

## Evidence

### Primary Git Repositories and Specifications

- **`rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, observed 2026-11-20):**
  - `src/inline-assembly.md:1051-1071` (`clobber_abi` register sets), `1072-1318` (`options(...)` validation rules), `1319-1463` (`r[asm.rules.*]` undefined-value vs. LLVM `undef`, `preserves_flags` per-ISA status registers including AArch64 `FPSR` and RISC-V `vtype`/`vl`/`vxsat`/`vxrm`, x86 `DF = 0`, x87 stack, PPC64 caller-frame stack write), and `1464-1728` (`naked_asm!` and directive support).
  - `src/attributes/codegen.md:1-1144` (`#[target_feature]` safety rules) and `src/behavior-considered-undefined.md:1-225`.
- **`rust-lang/rust` (`4b5350e87e487aed08ab2f9f0160a4b2616438bc` source & `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` executed `rustc 1.98.0-nightly`, observed 2026-11-20):**
  - `compiler/rustc_middle/src/mir/terminator.rs:1-822` (`TerminatorKind::InlineAsm`).
  - `compiler/rustc_const_eval/src/interpret/step.rs:713-714` (`InlineAsm => throw_unsup_format!("inline assembly is not supported")`).
  - `compiler/rustc_codegen_llvm/src/asm.rs:67-125, 258-280, 677-774, 1126-1128` (`dummy_output_type` `f32` fallback, `reg_to_llvm` `'x'` selection when `layout.is_none()`, and RISC-V/x86/AArch64 flag clobbers) and `compiler/rustc_target/src/asm/x86.rs:275-320, 491-506` (`xmm`/`ymm`/`zmm` overlapping register definitions).
- **`llvm/llvm-project` (`f61dfd8c0d8cfa6ed8a1ea3a16174d9673184825`, observed 2026-11-20):**
  - `llvm/lib/Target/X86/X86InsertVZeroUpper.cpp:63-155, 185-270` (`EXITS_CLEAN`/`EXITS_DIRTY` automaton, `isYmmOrZmmReg` `YMM0..15`/`ZMM0..15` restriction, `hasYmmOrZmmReg` operand scan).
- **`rust-lang/miri` (`5b99fdad636668442f94e15054a6b9fb3a80f613`, observed 2026-11-20):**
  - `src/machine.rs:1212-1240` (`check_fn_target_features` UB check on unavailable target features) and `src/helpers.rs:889-905` (`expect_target_feature_for_intrinsic`).
- **`minirust/minirust` (`063d784186d3252bee242217f218223205c0b568`, observed 2026-11-20):**
  - `spec/lang/step/terminators.md:1-489`, `spec/mem/interface.md:1-167`, `spec/mem/pointer.md:1-193`, `spec/mem/intptrcast.md:1-43`, and `spec/mem/tree_borrows/state_machine_protected.md:1-146`.
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, observed 2026-11-20):**
  - `trusted/lean/Trusted/MirAst.lean:742-796` (`TerminatorKind.unsupported` covering `InlineAsm`), `trusted/lean/Trusted/MirSemantics.lean:51-52, 82-107, 799-829, 1700` (`FaultKind.undefined` vs. `FaultKind.unsupported` fail-closed semantics), and `trusted/audit/TrustedBoundary.lean:1-40`.
- **ABI Specifications and Production Assembly Consumers (observed 2026-11-20):**
  - `ARM-software/abi-aa` (`9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7`): `aapcs64/aapcs64.rst:836-950` (`r18` platform register, `v8-v15` low 64-bit preservation, `FPSR.QC`, `FPCR.NEP == 0`, SVE `z8-z23` conditional preservation).
  - `riscv-non-isa/riscv-elf-psabi-doc` (`56561cb3e7330fe99a98fd27457229707b2786ae`): `riscv-cc.adoc:19-38, 100-170` (`gp`/`tp` invariance, `v0-v31`/`vl`/`vtype`/`vxrm`/`vxsat` volatility, `vstart == 0` entry/exit rule, `riscv_vector_cc`).
  - `FFmpeg/FFmpeg` (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, `libavutil/x86/x86inc.asm:374, 560-622, 1073`), `memorysafety/rav1d` (`2e7216c20ac2a75de204d6c8d7268b75a45959b4`, `src/wrap_fn_ptr.rs:41-101`, `src/cpu.rs:1-261`), `awslabs/s2n-bignum` (`280a220986a0bc6249248187717a771153d073db`, `x86/proofs/mlkem_ntt.ml:1345-1427`, `arm/proofs/mlkem_ntt.ml:552-554`), *System V AMD64 psABI* (`v1.0`), *Microsoft x64 Calling Convention*, and *OpenPOWER 64-Bit ELF V2 ABI Specification* (`Version 2.1.5`).

### Reproducible Execution Probes (Observed 2026-11-20 on Linux x86_64)

1. **`rustc` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) YMM Clobber vs. `vzeroupper` Emission Probe:**
   ```bash
   cat > /tmp/vzu_probe.rs <<'RS'
   #![no_std]
   use core::arch::x86_64::__m256i;
   #[no_mangle] #[target_feature(enable = "avx2")]
   pub unsafe fn discarded_ymm_clobber() {
       core::arch::asm!("vpcmpeqb ymm0, ymm0, ymm0", out("ymm0") _);
   }
   #[no_mangle] #[target_feature(enable = "avx2")]
   pub unsafe fn clobber_abi_only() {
       core::arch::asm!("vpcmpeqb ymm0, ymm0, ymm0", clobber_abi("C"));
   }
   #[no_mangle] #[target_feature(enable = "avx2")]
   pub unsafe fn typed_ymm_discarded_binding() {
       let _tmp: __m256i;
       core::arch::asm!("vpcmpeqb ymm0, ymm0, ymm0", out("ymm0") _tmp);
   }
   RS
   rustc --crate-type=lib -O --emit=asm,llvm-ir /tmp/vzu_probe.rs --out-dir /tmp
   grep -E "discarded_ymm_clobber:|clobber_abi_only:|typed_ymm_discarded_binding:|vzeroupper|retq" /tmp/vzu_probe.s
   ```
   Observed output confirms `vzeroupper` appears **solely** in `typed_ymm_discarded_binding` (immediately preceding `retq`), while both `clobber_abi_only` and `discarded_ymm_clobber` return directly with dirty `ymm0[255:128]`.

2. **Tree Borrows + `AbstractByte::Uninit` SIMD Seam Finite-State Probe (`Python 3.13`):**
   ```bash
   python3 - <<'PY'
   def tb_step(state: str, protected: bool, is_foreign: bool, is_write: bool) -> str:
       if not is_foreign:
           if not is_write: return state
           return "Active" if state in ("Reserved", "Active") else "UB"
       if not is_write:
           return ("UB" if protected else "Frozen") if state == "Active" else state
       if state in ("Reserved", "Active", "Frozen"):
           return "UB" if protected else "Disabled"
       return "Disabled"

   assert tb_step("Frozen", True, False, True) == "UB"      # in-place ASM write via &[u8] ptr
   assert tb_step("Active", True, True, False) == "UB"      # ASM foreign read vs live &mut [u8]
   assert tb_step("Active", False, False, True) == "Active" # raw *mut derived from unique root

   # Uninit tail-overread independence check: 16B load over 4 Init bytes + 12 Uninit bytes
   init_prefix = [10, 20, 30, 40]
   asm_masked_out = lambda tail12: [(b + 1) & 0xFF for b in (init_prefix + tail12)[:4]]
   assert asm_masked_out([0]*12) == asm_masked_out([0xFF]*12) == [11, 21, 31, 41]
   print("SEAM PROBE OK")
   PY
   ```

## Revalidation

1. **Check whether `rustc` fixes discarded `YMM`/`ZMM` clobber lowering (`< 0.2 s`):** Run the 18-line `rustc --crate-type=lib -O --emit=asm /tmp/vzu_probe.rs` probe in `## Evidence` or inspect `reg_to_llvm` in `compiler/rustc_codegen_llvm/src/asm.rs` (`layout == None` arm) on any newer `rustc` revision. If `discarded_ymm_clobber` begins emitting `=&{ymm0}` and `vzeroupper`, update Section 2.1 to record the version transition.
2. **Check `Anneal`, `MiniRust`, and `Miri` `InlineAsm` / foreign-call support:** Inspect `TerminatorKind` in `trusted/lean/Trusted/MirAst.lean` (`joshlf/anneal`), `spec/lang/step/terminators.md` (`minirust/minirust`), and `compiler/rustc_const_eval/src/interpret/step.rs` (`rust-lang/rust`).
3. **Check `preserves_flags` and ABI specifications on new targets:** Diff `r[asm.abi-clobbers.supported-abis]` and `r[asm.rules.preserved-registers]` in `rust-lang/reference` `src/inline-assembly.md`, `aapcs64/aapcs64.rst` (`ARM-software/abi-aa`), and `riscv-cc.adoc` (`riscv-non-isa/riscv-elf-psabi-doc`).
