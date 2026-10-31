<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Historical Verification Failures and Postmortems Across Backend Codegen, Register Allocation, Binary/Linker Tooling, Lifters, and Sandboxes

## Summary

Across both formally verified compilation pipelines (`CompCert`, `CakeML`,
`seL4` binary translation validation) and production industrial backends,
linkers, lifters, and JIT sandboxes (`Cranelift`/`Wasmtime`, `rustc`/`LLVM`,
`ld.lld`/`BOLT`, `McSema`/`Remill`, `VeriWasm`, Linux kernel eBPF JITs, and GPU
shader compilers), historical correctness failures and security escapes cluster
around four recurring structural fault lines:

1. **Unverified peripheral boundaries around verified cores:** In `CompCert`
   1.6–1.8, `Csmith` random differential testing (Yang et al., PLDI 2011) found
   zero miscompilations inside the Coq-verified middle-end passes, but exposed
   wrong-code bugs in the unverified `C2C` front-end elaborator (bitfield sign
   and width lowering, unaligned volatile/struct handling), the unverified
   OCaml assembly printer (`PrintAsm.ml`), ABI marshaling (`va_arg`), and 80-bit
   x87 extended-precision spill/reload double-rounding prior to CompCert 2.0's
   verified IEEE-754 `Floats.v` and Menhir `val_automaton` parser. Similarly,
   standard `CompCert` modeled stack frames as unbounded abstract blocks in
   `CompCert` memory until `Stack-Aware CompCert` (Wang et al., POPL 2019),
   permitting verified programs to silently overflow finite hardware stacks into
   adjacent heap segments. In `seL4`'s ARM binary translation validator
   (`GraphRefine`, Sewell et al., PLDI 2013), inline assembly, kernel entry/exit
   context-switch stubs, and GCC `-O2` loop unrolling/vectorization fell outside
   automated equivalence checking, requiring either manual HOL4/Isabelle machine
   proofs or compiler flag restrictions (`-fno-unroll-loops`,
   `-fno-tree-vectorize`).
2. **Instruction-selection bitwidth extensions, condition-flag clobbers, and
   register-allocator reload/aliasing bugs:** In `Cranelift` and `Wasmtime`,
   severity-critical sandbox escapes stemmed from 32-bit sign-extension versus
   zero-extension mismatches during spill reloads (`CVE-2021-32629` /
   `GHSA-hpqh-2wqx-7qp5`), 35-bit instead of 33-bit effective-address
   calculation in `x86_64` addressing-mode ISLE rules (`CVE-2023-26489` /
   `GHSA-ff4p-7xrq-q5r8`), input-register overwrite and upper-lane corruption in
   SIMD `i8x16.swizzle` and `select` lowering (`CVE-2022-31104` /
   `GHSA-jqwc-c49r-4w2x`), and Spectre-guard `cmov` flag clobbering when zero
   materialization (`xor reg, reg`) overwrote `rflags` before the conditional
   move executed. Formal verification of ISLE rules via `Crocus` (ASPLOS 2024)
   and `VeriISLE` (PLDI 2024) reproduced three known bugs (including
   `CVE-2023-26489`) and uncovered two new wrong-code bugs plus underspecified
   lowering invariants (`SDIV` overflow on `INT_MIN / -1` in AArch64 and
   subregister zero-extension assumptions).
3. **Cross-language ABI skew, lifetime-marker stack-slot aliasing, and
   underspecified inline assembly contracts:** Differential testing with
   `abi-cafe` exposed a multi-year `i128`/`u128` ABI mismatch between `rustc`
   (8-byte alignment in LLVM `< 18`) and C/C++ `__int128` (16-byte alignment in
   System V AMD64 and AAPCS64, tracked in `rust-lang/rust#54341` and fixed in
   Rust 1.77–1.78), alongside `#[repr(C)]` zero-sized type (ZST) and SIMD vector
   passing discrepancies. Inside `rustc` + LLVM, mis-ordered or escaped
   `StorageLive`/`StorageDead` markers (`llvm.lifetime.start`/`end`) caused
   LLVM's `StackColoring` pass (`StackColoring.cpp`) to merge simultaneously
   live stack slots (`rust-lang/rust#46606`, `rust-lang/rust#91899`). At the
   inline-assembly boundary, `TInA` (ASE 2019) and `RUSTInA` (ICSE 2021) showed
   that handwritten `asm!` blocks across Debian, GMP, FFmpeg, and kernel trees
   routinely omit `earlyclobber` (`out(reg)` vs. `lateout(reg)`), clobber
   `rflags` while claiming flag preservation, or write into the 128-byte System
   V red zone `[rsp - 128 .. rsp)` despite `nostack`.
4. **Unsound binary-lifter assumptions, post-codegen linker/BOLT relaxation
   drift, and multi-pass JIT/SIMT divergence bugs:** Binary lifters (`McSema`,
   `Remill`, `RetDec`) evaluated by Dasgupta et al. (PLDI 2020) contained 29
   single-instruction semantic bugs (`lifting-bits/remill#376`) and relied on
   unverified frame-separation and return-address preservation assumptions later
   formalized by `FoxDec` (OOPSLA 2022). Post-compilation linkers (`ld.lld`
   `R_RISCV_RELAX` / `R_RISCV_ALIGN`) and binary optimizers (`LLVM BOLT`) have
   corrupted PC-relative displacements, jump tables, and `.eh_frame` unwind
   tables after compiler verification completes. In kernel and GPU JITs,
   `CVE-2021-29154` allowed root privilege escalation in the Linux `x86` eBPF
   JIT (`arch/x86/net/bpf_jit_comp.c`) when mixed-pass `addrs[]` state caused
   backward-branch displacements to oscillate and emit wrong jump offsets;
   `Jitterbug` (OSDI 2020) discovered 16+ new bugs across Linux `x86`, `ARM32`,
   `ARM64`, and `RISC-V` eBPF JITs (`ALU64_ARSH` shift-by-zero, subregister
   zero-extension); and `GraphicsFuzz` (OOPSLA 2017) uncovered 60+ shader
   compiler bugs across 7 GPU vendors, including SIMT reconvergence mask
   corruption and divergent barrier hangs (`CVE-2017-2424`, `CVE-2017-6259`).

Every one of these historical failure classes maps directly onto design
requirements for Anneal's four `trusted/` primitives—(1) `Language SemObs` +
partial `BehaviorCodec L₁ L₂` (`Compiles` and `Abstracts`), (2) `ProductiveOn` +
`InhabitedPre`, (3) positive per-obligation `VerificationResult`, and (4)
`SmallStepMachine` with `EventualBehaviorOf` + `StepResult.externalCall`—backed
by single-source `.olean`-bound artifact verification in `anneal-audit`.

## Applicability

This report applies to the twelve subjects recorded in `REPORT.json`:

1. **Anneal workspace and trusted core:**
   `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`, the trusted
   refinement core at `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`
   (`trusted/lean/Trusted/Refinement.lean`,
   `trusted/lean/Trusted/StepResult.lean`,
   `trusted/lean/Trusted/MirSemantics.lean`), and the MIR-to-x86-64 compiler
   branch at `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`
   (`trusted/lean/Trusted/X86Semantics.lean`,
   `theory/Anneal/Compiler/NaiveCodegen.lean`,
   `theory/Anneal/Compiler/Peephole.lean`).
2. **Verified compiler and kernel translation-validation postmortems:**
   `Csmith` evaluation of `CompCert` 1.6–1.8 (Yang et al., PLDI 2011, DOI
   `10.1145/1993498.1993532`), `Stack-Aware CompCert` (Wang, Wilke, and Shao,
   POPL 2019, DOI `10.1145/3290380`), and `seL4` ARM binary translation
   validation (Sewell, Myreen, and Klein, PLDI 2013, DOI
   `10.1145/2491956.2462183`).
3. **Industrial backend, ABI, inline-asm, lifter, linker, and JIT defect
   corpora:** `Wasmtime`/`Cranelift` security advisories (`CVE-2021-32629`,
   `CVE-2022-31104`, `CVE-2022-39392`, `CVE-2023-26489`, `CVE-2023-30624`),
   `Crocus` (ASPLOS 2024, DOI `10.1145/3620665.3640369`) and `VeriISLE` (PLDI
   2024, DOI `10.1145/3656427`), `rustc`/`LLVM` ABI and `StackColoring` defect
   records (`rust-lang/rust#54341`, `rust-lang/rust#46606`,
   `rust-lang/rust#91899`, `Gankra/abi-cafe`), `TInA`/`RUSTInA` inline-assembly
   studies (ASE 2019 DOI `10.1109/ASE.2019.00069`, ICSE 2021 DOI
   `10.1109/ICSE43902.2021.00069`), binary lifter and SFI studies (Dasgupta et
   al. PLDI 2020 DOI `10.1145/3385412.3385964`, `VeriWasm` NDSS 2021 DOI
   `10.14722/ndss.2021.24295`, `FoxDec` OOPSLA 2022 DOI `10.1145/3563322`),
   Linux kernel eBPF JIT flaws (`CVE-2021-29154` and `Jitterbug` OSDI 2020), and
   `GraphicsFuzz` GPU shader miscompilations (OOPSLA 2017 DOI
   `10.1145/3133917`).

The relationship among these subjects is diagnostic and architectural: concrete
historical failures in Subjects 4–12 are analyzed to extract exact failure
mechanisms and verify how Anneal's `trusted/` primitives (Subjects 1–3) prevent
or surface each failure class without expanding the trusted computing base.

## Findings

### 1. Verified Compiler Unverified-Boundary Bugs: `CompCert`, `CakeML`, and `seL4` Binary Translation Validation

`Basis: documentation + source + derived`

#### 1.1 `CompCert` 1.6–1.8 Unverified Front-End (`C2C`), Assembly-Printer, ABI, and x87 Spilling Bugs (`Csmith`, PLDI 2011)

In *"Finding and Understanding Bugs in C Compilers"* (PLDI 2011, DOI
`10.1145/1993498.1993532`), Yang, Chen, Eide, and Regehr tested `GCC`, `LLVM`,
and `CompCert` (versions 1.6 through 1.8) using randomly generated, UB-free C99
programs from `Csmith`. While `Csmith` uncovered more than 325 bugs in `GCC` and
`LLVM` across all optimization phases, **it found zero wrong-code bugs in the
Coq-verified middle-end passes of `CompCert`**. However, `Csmith` and subsequent
boundary audits exposed silent wrong-code generation and crashes across every
*unverified* boundary surrounding `CompCert`'s verified core:

- **Unverified `C2C` front-end elaborator and bitfield lowering:** Prior to
  `CompCert` 2.0, parsing and C-to-`CompCertC`/`Clight` elaboration were written
  in unverified OCaml (`cparser/`). `Csmith` triggered miscompilations where
  bitfield widths, signedness promotions on narrow bitfields, and compound
  initializers were mistranslated *before* the Coq-verified AST was ever
  constructed. Because the Coq theorem only proved that the emitted PowerPC/ARM/x86
  assembly refined the elaborated `Clight` AST, any semantic distortion in
  `C2C` produced a valid Coq proof of the wrong program. (This failure directly
  motivated Jourdan, Pottier, and Leroy's verified LR(1) parser in `CompCert`
  2.0 using Menhir's `val_automaton` in ESOP 2012, and moving bitfield
  lowering inside the Coq proof.)
- **80-bit x87 extended-precision register spilling vs. 64-bit IEEE-754 memory
  slots:** Early x86 `CompCert` backends used the legacy x87 floating-point
  stack (`st(0)..st(7)`), which computes intermediate results in 80-bit extended
  precision (`long double`) but rounds to 64-bit `double` (`fstpl`) whenever the
  register allocator spills a live range to the stack frame. Because register
  spilling was invisible to the source C semantics, whether a floating-point
  expression experienced single rounding (80-bit) or double rounding (80-bit
  then 64-bit spill) depended on register pressure—violating deterministic
  IEEE-754 refinement until Boldo, Jourdan, Leroy, and Melquiond (ARITH 2013 /
  `Floats.v` in `CompCert` 2.0+) formalized full Flocq IEEE-754 bit-level
  semantics and switched scalar FP codegen to SSE2 (`xmm0..xmm15`).
- **Unverified assembly pretty-printer (`PrintAsm.ml`) and GNU `as` assembler
  drift:** `CompCert`'s Coq proof ended at an abstract `Asm.program` datatype;
  an unverified OCaml printer formatted `Asm.program` into text strings passed
  to the system assembler (`gas`). Bugs were discovered in `PrintAsm.ml` where
  immediate operands, symbol offsets, or section alignment directives were
  printed with wrong syntax or sign formatting, or where `gas` silently
  interpreted an ambiguous mnemonic differently from `Asm.v`'s operational
  semantics.
- **`va_arg` and composite struct ABI mismatches at the C library boundary:**
  When `CompCert`-compiled translation units called `glibc` or system libraries
  compiled with `GCC`/`Clang`, disagreements over struct-by-value splitting and
  `va_list` state layouts caused silent argument corruption across the FFI
  seam—even though `CompCert`'s internal calling convention was self-consistent.

#### 1.2 Unbounded Abstract Stack Blocks vs. Concrete Finite Hardware Stacks (`Stack-Aware CompCert`, POPL 2019)

In standard `CompCert` (Leroy, CACM 2009), the memory model (`Mem.v`) represents
every function activation's stack frame as a freshly allocated, isolated
abstract memory block `b : block` drawn from an infinite supply, and `Mem.alloc`
never fails. On real hardware (`x86-64`, `AArch64`, `RISC-V`), the stack is a
contiguous, finite downward-growing region `[stack_limit .. stack_base)` sharing
a single flat 64-bit address space with the heap and `.bss`/`.data`.

As Wang, Wilke, and Shao demonstrated in *"An Abstract Stack Based Approach to
Verified Compositional Compilation to Machine Code"* (`Stack-Aware CompCert`,
POPL 2019, DOI `10.1145/3290380`), standard `CompCert`'s infinite-block memory
model creates a critical soundness gap:

- A program proven completely safe and UB-free in `CompCert` can decrement the
  hardware stack pointer `rsp`/`sp` past the stack guard region (via deep
  recursion or large local frames) and overwrite live heap or global variables,
  violating memory isolation in the compiled binary despite a machine-checked
  refinement theorem.
- Furthermore, standard `CompCert`'s `Stacking` pass could not verify
  optimizations that merge or elide frames (such as tail-call elimination or
  inlining) against a concrete finite byte budget without tracking an explicit
  abstract stack height (`Stack-Aware CompCert`'s `stack` ADT with frame push/pop
  history) and discharging a static whole-program or per-entrypoint stack
  headroom precondition (`stack_consumption(p) ≤ MAX_STACK`).

#### 1.3 `CakeML` Foreign Function Interface (FFI), Word-Width, and GC Boundary Assumptions

`CakeML` (Kumar et al., POPL 2014; Tan et al., ICFP 2016) eliminates the
unverified assembly printer and external compiler bootstrap by bootstrapping its
compiler inside the HOL4 logic and emitting verified machine-code byte arrays
directly (`x86-64`, `ARMv7`, `AArch64`, `RISC-V`, `MIPS`). Nevertheless,
historical defects and verification boundaries in `CakeML` deployments have
arisen at three external seams:

1. **FFI byte-array aliasing and GC root invalidation:** `CakeML`'s verified
   runtime communicates with external C/OS routines exclusively via an `ffi`
   oracle transition passing mutable byte arrays (`Word8Array`). If an external
   C FFI function retains a raw pointer into the `CakeML` heap across a return
   boundary or writes past the passed byte-slice length, the copying garbage
   collector relocates live objects and corrupts the heap.
2. **Startup/linker wrapper and OS page-mapping mismatches:** While `CakeML`
   emits verified machine bytes, an unverified C/assembly startup stub (`basis_ffi.c`)
   must allocate the heap and stack regions and pass their exact virtual
   addresses and sizes in architectural registers upon entry; mismatches between
   the stub's `mmap` size and the compiled binary's configured heap/stack bounds
   cause immediate unchecked memory faults.

#### 1.4 `seL4` Binary Translation Validation (`GraphRefine`, PLDI 2013): Inline Assembly, Context Switches, and GCC `-O2` Loop Optimizations

In *"Translation Validation for a Verified OS Kernel"* (PLDI 2013, DOI
`10.1145/2491956.2462183`), Sewell, Myreen, and Klein built `GraphRefine` to
extend `seL4`'s Isabelle/HOL C verification (`Simpl` semantics) down to the
actual ARMv7 ELF binary compiled by `GCC 4.5.1` without trusting `GCC`. By
decompiling the ARM binary into a flat control-flow graph (`GraphLang`, derived
from Cambridge HOL4's verified ARM model) and discharging per-cut-point
equivalence obligations via SMT solvers (`Z3`, `CVC4`, `SONOLAR`), `GraphRefine`
eliminated the compiler from the TCB for the C portion of `seL4`. However, the
postmortem of `GraphRefine` documented three sharp boundaries where automated
translation validation failed or required manual intervention:

1. **Loop-restructuring optimizations at `GCC -O2`:** `GraphRefine` matches
   source and binary executions at loop headers ("split points"). When `GCC -O2`
   performed loop unrolling, peel-and-jam, loop-invariant code motion across
   multiple exit edges, or auto-vectorization, the 1-to-1 iteration
   correspondence between the `Simpl` loop header and the ARM binary CFG broke
   down, causing SMT timeouts or structural refutations. Validating the `seL4`
   binary at `-O2` required explicitly disabling loop-restructuring flags in
   `GCC` (such as `-fno-unroll-loops`) or supplying manual cut-point alignment
   hints.
2. **Inline assembly (`asm volatile`) and privileged coprocessor instructions:**
   Hardware control operations in `seL4` (TLB invalidation `MCR p15`, cache
   flushes, IRQ masking, and page-table base updates) are written as C inline
   assembly blocks. Because `Simpl` treats inline assembly as opaque external
   calls or axioms while the binary contains concrete ARMv7 `MCR`/`MRC`/`MSR`
   instructions, `GraphRefine` could not automatically validate functions
   containing non-trivial inline assembly without bespoke instruction-to-hook
   specifications.
3. **Context-switch, trap-entry, and boot assembly routines:** Pure assembly
   files (`traps.S`, `head.S`) that manipulate the kernel stack pointer `sp` and
   saved-register context blocks directly violate the standard C ABI frame
   discipline assumed by `GraphRefine`'s stack-frame separation invariant,
   requiring manual exclusion from the automated binary validator.

#### 1.5 Architectural Lessons for Anneal's 4 `trusted/` Primitives

- **Eliminating unverified printer and assembler drift via `.olean`-bound
  emission (`anneal-audit`):** To prevent `CompCert`'s `PrintAsm.ml` failure
  mode, Anneal's verified backend defines the emitted assembly text
  (`Trusted.emitX86CrateAsm : String`) or linked ELF byte array
  (`Trusted.emitCrateElfBytes : ByteArray`) as a pure constant inside the
  Lean 4 kernel environment (`Trusted/X86Semantics.lean`), and `anneal-audit`
  verifies that the on-disk `.s` or `.o`/ELF file matches the kernel-reduced
  constant byte-for-byte.
- **Preventing silent stack overflow via `ProductiveOn` + `InhabitedPre`:** To
  close the gap exposed by `Stack-Aware CompCert`, Anneal pairs downward
  compilation (`Compiles SpillSlotMachLang StackFrameMachLang`) with a target
  productivity obligation `StackFrameMachLang.ProductiveOn (StackHeadroomPre
  frameBound) t` (and an `InhabitedPre` witness ensuring the headroom
  precondition is non-vacuous), surfacing `StackBound::<fn_name>` in
  `VerificationResult`.
- **Handling `GCC`/`LLVM -O3` loop optimizations and inline assembly via
  per-obligation `VerificationResult`:** Rather than failing monolithically when
  a single `-O3` loop or `asm!` block resists automated SMT/symbolic checking
  (as in `GraphRefine`), Anneal's positive per-obligation `VerificationResult`
  isolates each cut-point VC (`LlvmO3CutPoint::<fn>::<bb>`) and inline-asm
  contract (`InlineAsmOptionsValid::<loc>`) as an individually named obligation
  that can be discharged by a custom Lean proof, compiled via `NaiveCodegen`, or
  explicitly audited under a development policy.

### 2. `Cranelift`, `Wasmtime`, `regalloc2`, and Instruction-Selection Bugs & CVEs

`Basis: documentation + source + derived`

#### 2.1 `CVE-2021-32629` (`GHSA-hpqh-2wqx-7qp5`): 32-Bit Sign-Extension Instead of Zero-Extension on Spill Reloads

In May 2021, Fastly and the Bytecode Alliance disclosed `CVE-2021-32629`
(`GHSA-hpqh-2wqx-7qp5`, affecting `cranelift-codegen` `< 0.73.1` in `Wasmtime`
and `Lucet`). WebAssembly 32-bit linear-memory addresses are unsigned 32-bit
integers $a \in [0, 2^{32})$. On 64-bit targets (`x86_64`, `aarch64`), SFI
sandboxing relies on zero-extending every 32-bit Wasm address to a 64-bit
register ($0 \le \text{zext}_{64}(a) < 2^{32}$) before adding the 64-bit linear
memory base register (`r15` / `heaps_base`) and an unmapped 4 GiB–8 GiB guard
region above the heap.

- **Technical root cause:** Under high register pressure when a 32-bit address
  virtual register was spilled to the stack frame and subsequently reloaded via
  an addressing-mode or narrow-reload folding pattern in Cranelift's backend,
  the reload instruction emitted a **32-to-64-bit sign-extending load** (`movslq`
  on `x86_64` / `ldrsw` on `aarch64`) instead of a zero-extending load (`movl` /
  `ldr w`).
- **Exploit mechanism:** Any Wasm guest address $a \in [2^{31}, 2^{32})$ (with
  bit 31 set) was sign-extended to a negative 64-bit offset in $[-2^{31}, -1]$,
  allowing a malicious Wasm module to read and write host virtual memory up to
  **2 GiB below** the start of the sandbox's linear memory (`heaps_base - 2 GiB`),
  completely bypassing forward guard pages.

#### 2.2 `CVE-2023-26489` (`GHSA-ff4p-7xrq-q5r8`): 35-Bit vs. 33-Bit Effective-Address Calculation in `x86_64` ISLE Lowering

In March 2023, the Bytecode Alliance disclosed `CVE-2023-26489`
(`GHSA-ff4p-7xrq-q5r8`, CVSS 9.9, affecting `Wasmtime` `< 4.0.1`, `< 5.0.1`,
`< 6.0.1` on `x86_64`).

- **Technical root cause:** In WebAssembly, a memory instruction computes its
  effective address as $\text{EA} = \text{zext}_{64}(\text{base}_{32}) +
  \text{zext}_{64}(\text{offset}_{32})$, which is at most $2^{33} - 2$ (a 33-bit
  unsigned range $[0, 8\text{ GiB})$). Wasmtime's default static virtual-memory
  reservation on 64-bit hosts maps 4 GiB of accessible linear memory followed by
  a 2 GiB guard region (6 GiB total) plus explicit bounds checks when
  $\text{offset}_{32} > 2\text{ GiB}$. During migration of `x86_64` instruction
  selection to ISLE (`cranelift/codegen/src/isa/x64/inst.isle`), an addressing
  mode optimization folded a left-shift by 1, 2, or 3 bits (`shl` scale factor
  $\times 2, \times 4, \times 8$ in `x86_64` SIB addressing `[base + index*scale + disp]`)
  into the effective-address calculation *after* zero-extension, without
  accounting for the 32-bit wraparound semantics of Wasm's `i32.shl` prior to
  address addition.
- **Exploit mechanism:** Because `index` was zero-extended to 64 bits and then
  multiplied by $\text{scale} = 8$ ($2^3$) in 64-bit arithmetic, $\text{EA}$
  could reach $2^{32} \times 8 = 2^{35}$ bytes (**34.3 GiB** past the linear
  memory base), jumping straight over Wasmtime's 6 GiB virtual-memory guard zone
  into arbitrary adjacent host heap mappings or other tenant sandboxes.

#### 2.3 `CVE-2022-31104` (`GHSA-jqwc-c49r-4w2x`): Input-Register Aliasing in `i8x16.swizzle` and Sub-Register Truncation in `v128` `select`

Disclosed in July 2022 (`Wasmtime` `< 0.38.1`, `cranelift-codegen` `< 0.85.1`),
`CVE-2022-31104` bundled two distinct SIMD instruction-lowering miscompilations
on `x86_64`:

1. **`i8x16.swizzle` constant-pool/input register corruption:** WebAssembly's
   `i8x16.swizzle(v, idx)` zeroes any output lane whose index byte in `idx` is outside
   `0..15`, whereas Intel's `pshufb xmm1, xmm2` only zeroes the lane if bit 7 of
   the index byte (`0x80`) is set, and otherwise masks the index by `0x0F`. To
   bridge this semantic gap on pre-AVX512 `x86_64`, Cranelift's lowering added
   `0x70` (`paddb`) to `idx` in-place so that any value $\ge 16$ (`0x10..0x7F`)
   overflowed into `0x80..0xEF` (setting bit 7). However, the lowering rule
   mutated the **input register holding `idx` directly** without allocating a
   fresh scratch register or marking the operand as read-write (`inout`). When
   `idx` held a loop-invariant constant or a value reused by subsequent
   instructions, `i8x16.swizzle` permanently corrupted `idx` for the rest of the
   function.
2. **`select` on `v128` 32-bit partial register move:** When lowering `select(c,
   v_true, v_false)` for 128-bit SIMD vectors (`I8X16`, `I32X4`, etc.) on
   `x86_64`, the false-branch copy path emitted a 32-bit scalar/float move
   (`movss` / 32-bit register copy) instead of a full 128-bit vector move
   (`movdqa` / `movaps`), copying only bits `0..31` and leaving bits `32..127`
   containing uninitialized or stale register contents.

#### 2.4 `CVE-2022-39392`, `CVE-2023-30624`, and Spectre-Guard Condition-Flag Clobbers

- **`CVE-2022-39392` (`GHSA-44mr-8vmm-wjhg`, Wasmtime `< 2.0.2`):** When
  Wasmtime's pooling allocator was configured with `memory_pages: 0`, virtual
  memory guard protections were omitted under the assumption that no memory
  existed, yet Cranelift's static-bound elision still assumed a 2 GiB guard page
  region was mapped—allowing a guest module to read/write host memory near the
  unmapped base.
- **Spectre-guard `cmov` flag clobbering (`x86_64` / `aarch64`):** To prevent
  speculative out-of-bounds reads (Spectre v1), Cranelift lowers heap bounds
  checks using branchless conditional-move guards (`cmp idx, bound; cmovae ptr,
  zero_reg`). In a recurring class of flag-dataflow bugs (and related to
  `CVE-2026-34971` / `GHSA-jhxm-h53p-jm7w` on `aarch64`), the instruction
  selector or register-allocator reload pass inserted an instruction between the
  `cmp` and the `cmov` that materialized zero via `xor r_zero, r_zero` (on
  `x86_64`) or modified `NZCV` flags, **clobbering the flags set by `cmp`** (`xor`
  always sets `CF = 0, ZF = 1, OF = 0`) right before `cmovae` tested `CF == 0`!
- **`CVE-2023-30624` (`GHSA-c87w-297f-6568`, Wasmtime `< 6.0.2 / 7.0.1 /
  8.0.1`):** Wasmtime's runtime `VMContext` management cast a shared reference
  `&VMContext` to `*mut VMContext` to mutate instance tables and memories across
  JIT entries. Under Rust 1.70 / LLVM 16's stricter `noalias` (`readonly`)
  exploitation, LLVM proved that fields reachable through `&VMContext` could not
  change across a Wasm call and optimized away critical bounds/table checks.

#### 2.5 `VeriISLE` (PLDI 2024), `Crocus` (ASPLOS 2024), and `regalloc2` Symbolic Checker Postmortems

To systematically eliminate instruction-lowering bugs in Cranelift's ISLE DSL,
VanHattum, Pardeshi, et al. developed `Crocus` (ASPLOS 2024, DOI
`10.1145/3620665.3640369`) and `VeriISLE` (PLDI 2024, DOI `10.1145/3656427`),
which verify ISLE rewrite rules against formal ARMv8-A ASL and x86-64 semantics
using SMT solvers. Across Cranelift's `aarch64` and `x86_64` backends,
`VeriISLE` reproduced 3 historical bugs (including `CVE-2023-26489`) and
discovered **2 previously unknown wrong-code bugs plus underspecified subregister
invariants**:

- **`AArch64` `SDIV` / `srem` signed overflow edge case (`INT_MIN / -1`):**
  Unlike `x86_64` `idiv` (which traps with `#DE` on both division by zero and
  `INT_MIN / -1`), ARM64's `SDIV` instruction never traps in hardware: it
  returns `0` on division by zero and wraps `INT_MIN / -1` to `INT_MIN`.
  Cranelift's `aarch64` ISLE rules for remainder (`srem`) and division (`sdiv`)
  omitted or misordered explicit overflow checks on 8-bit/16-bit/32-bit widths
  when upper bits of a 64-bit `X` register were assumed sign-extended vs.
  zero-extended.
- **Implicit upper-bit cleanliness invariant across ISLE rules:** `VeriISLE`
  exposed that some ISLE extractors/constructors assumed 8-bit (`I8`) and 16-bit
  (`I16`) virtual registers had zeroed bits `8..63` in their hosting 32/64-bit
  physical register, while other rules left arbitrary high-bit garbage (`undef`
  upper bits) that leaked when consumed by a 32-bit compare or shift instruction.
- **`regalloc2` parallel-move and reload bugs caught by `regalloc2`'s symbolic
  checker:** Chris Fallin's `regalloc2` includes a built-in symbolic dataflow
  checker (`checker.rs`) that tracks abstract virtual-register values through
  physical registers and spill slots. During `regalloc2` development and fuzzing
  (`cargo-fuzz`), the symbolic checker caught critical allocator bugs in:
  1. **Parallel-move cycle resolution:** When resolving a cycle of simultaneous
     register moves ($r_1 \leftarrow r_2, r_2 \leftarrow r_3, r_3 \leftarrow
     r_1$) combined with a tree of non-cyclic fan-out moves ($r_4 \leftarrow
     r_2$) at a CFG split edge, emitting the cycle's `xchg`/scratch swap
     *before* the fan-out move read the already-overwritten $r_2$.
  2. **Eviction vs. rematerialization ordering:** When a virtual register was
     simultaneously marked rematerializable and dirty in a physical register
     whose spill slot was shared with an evicted live range.

#### 2.6 Architectural Lessons for Anneal's 4 `trusted/` Primitives

- **Preventing `CVE-2021-32629` and `CVE-2023-26489` via target-level
  `ProductiveOn` in SFI sandboxes:** `Compiles` alone only guarantees target
  correctness when the source program is UB-free. For WebAssembly/SFI sandboxes
  (`WasmSfiSandbox`), Anneal requires the target-machine theorem
  `X86SandboxedLang.ProductiveOn (HostSandboxPre bounds) (compileWasmSfi u)`
  where any memory access outside `[r15 .. r15 + 4GiB + guard)` steps to
  `.failed .ub`. Had a reload used sign-extension (`movslq`, reaching
  `r15 - 2GiB`) or a scaled index reached `r15 + 34GiB`, the `ProductiveOn`
  obligation fails in `bv_decide` with an explicit 64-bit counterexample
  address.
- **Preventing `VeriISLE` subregister dirtiness and `v128` partial moves via
  partial `BehaviorCodec.decodeOut`:** In Anneal's `BehaviorCodec`, narrow types
  (`I8`, `I16`, `bool`) and SIMD vectors stored in wider architectural registers
  must satisfy an explicit representation invariant enforced by partial
  `decodeOut : L₂.Out → Option L₁.Out`. Any rule that leaves dirty upper bits in
  a register claimed to be zero-extended yields `decodeOut o₂ = none`, refuting
  `Compiles`.
- **Catching `i8x16.swizzle` input-aliasing and `cmov` flag clobbers via
  `SmallStepMachine` register/flag semantics:** Because `X86Machine` models
  `rflags` explicitly on every instruction (`xor` unconditionally overwrites
  `CF`/`ZF`/`OF`) and `checkRegAlloc` in `theory/` verifies `regalloc2` outputs
  against `VRegMachLang`, both flag clobbering before `cmov` and in-place
  mutation of a live input register fail symbolic simulation.

### 3. ABI Marshaling, Inline Assembly, and `StackColoring` Bugs in `rustc` and `LLVM`

`Basis: documentation + source + derived`

#### 3.1 Cross-Language FFI ABI Mismatches Exposed by `abi-cafe` (`rust-lang/rust#54341`, ZSTs, and Struct Splitting)

Alyssa Rosenzweig's `abi-cafe` differential harness (`Gankra/abi-cafe`, integrated
into `rustc` CI) pairs caller and callee implementations compiled by different
compilers (`rustc` LLVM backend, `rustc_codegen_cranelift`, `rustc_codegen_gcc`,
`clang`, `gcc`, `msvc`) across `extern "C"`, `extern "sysv64"`, and `extern
"win64"` signatures. `abi-cafe` and related FFI bug reports exposed systematic
cross-compiler ABI divergences:

- **`i128` / `u128` alignment and stack-slot split bug (`rust-lang/rust#54341`):**
  The System V AMD64 psABI and ARM64 AAPCS64 specify that 128-bit integers
  (`__int128`) have **16-byte alignment** (`alignof(__int128) == 16`), so a
  `struct { char a; __int128 b; }` has 15 bytes of padding before `b` (`sizeof ==
  32`), and an `__int128` passed in registers (`rdx:rax` or `x0:x1`) or on the
  stack must be aligned to an even register pair or 16-byte stack boundary. For
  nearly a decade (prior to LLVM 18 and Rust 1.77/1.78), LLVM's default x86-64
  data layout hardcoded `i128:64` (8-byte alignment); `clang` worked around this
  in its C frontend by manually attaching `align 16` attributes, whereas `rustc`
  relied on LLVM's data layout and gave `i128`/`u128` 8-byte alignment on
  `x86_64` and `aarch64` (`sizeof == 24` for `#[repr(C)] struct(u8, u128)`!).
  Passing a struct containing `u128` or passing more than three `u128` arguments
  across `extern "C"` between Rust and C silently shifted every subsequent stack
  argument by 8 bytes.
- **Zero-Sized Types (ZSTs) and empty `#[repr(C)]` structs across C vs. C++ vs.
  Rust:** In GNU C (`gcc`), an empty struct `struct Empty {}` has size `0` and
  consumes zero argument registers or stack bytes; in C++ (Itanium ABI and MSVC
  ABI), an empty struct has `sizeof == 1` and consumes a register or stack slot!
  When `#[repr(C)]` Rust structs containing ZST fields or single-field wrappers
  (`#[repr(transparent)]`) crossed FFI boundaries without matching the target C
  vs. C++ empty-aggregate rule, eightbyte classification in System V AMD64
  shifted `INTEGER` vs. `SSE` register assignments (`rdi` vs. `xmm0`).
- **System V vs. Win64 struct-passing and `sret` confusion:** When Rust code on
  Windows (`x86_64-pc-windows-msvc`) called an `extern "sysv64"` function (or
  vice versa under Wine/UEFI `efiapi`), composite types of size 12 or 16 bytes
  (which SysV passes split across two registers `rdi` + `rsi` or `xmm0` + `xmm1`,
  whereas Win64 passes by hidden pointer unless size $\in \{1, 2, 4, 8\}$) were
  mismarshaled when `rustc` applied the host target's ABI lowering rules instead
  of the explicit calling convention's rules.

#### 3.2 `LLVM StackColoring` Miscompilations from Mis-Ordered `StorageLive`/`StorageDead` Markers (`rust-lang/rust#46606`, `rust-lang/rust#91899`)

In Rust MIR, local variable storage lifetimes are bracketed by
`StatementKind::StorageLive(_x)` and `StatementKind::StorageDead(_x)`. During
LLVM IR emission (`rustc_codegen_llvm`), these translate to
`llvm.lifetime.start.p0(size, ptr)` and `llvm.lifetime.end.p0(size, ptr)`
intrinsics consumed by LLVM's `StackColoring` pass (`llvm/lib/CodeGen/StackColoring.cpp`)
to merge non-overlapping `alloca` stack slots into shared `[rsp + offset]` frame
locations.

Repeatedly in `rustc` history (`rust-lang/rust#46606`, `rust-lang/rust#91899`,
and upstream `llvm/llvm-project#32906`), the interaction between MIR passes and
`StackColoring` produced catastrophic silent stack corruption at `-C opt-level >= 2`:

1. **Raw pointer escaping across `StorageDead` + `StorageLive` in loops:** When a
   raw pointer `*const T` or reference to a local `_x` was created inside a block,
   or when an inlined MIR function's cleanup/drop path executed `StorageDead(_x)`
   along one CFG edge while leaving `_x` live or re-entering `StorageLive(_x)`
   without dominating the pointer use, `StackColoring` concluded `_x`'s live
   interval had ended and assigned a newly allocated local `_y` to the **exact
   same physical stack offset `[rsp + off]`**. Subsequent writes to `_y`
   silently overwrote the live contents of `_x`.
2. **Degenerate or inverted lifetime intervals in `StackColoring.cpp`:** LLVM's
   dataflow analysis in `StackColoring` treated any memory access outside the
   computed `[start, end]` interval as `undef`/poison, causing the backend
   scheduler and dead-store eliminator to delete stores to `_x` altogether before
   reading from `[rsp + off]`.

#### 3.3 Inline Assembly (`asm!`) Interface Violations Discovered by `TInA` (ASE 2019) and `RUSTInA` (ICSE 2021)

Compilers treat inline assembly blocks (`core::arch::asm!` in Rust, `asm(...)` in
GCC/Clang) as black-box instructions whose register, flag, and memory effects
are trusted entirely to the programmer's constraint annotations. In *"Get Out of
the Valley: Lifting Inline Assembly to IR"* (`TInA`, ASE 2019, DOI
`10.1109/ASE.2019.00069`) and *"Assess and Heal: Automated Inline Assembly
Compliance"* (`RUSTInA`, ICSE 2021, DOI `10.1109/ICSE43902.2021.00069`),
Recoules, Bardin, Bonichon, Mounier, and Potet lifted and verified thousands of
real-world inline assembly blocks across the Linux kernel, GMP, FFmpeg, ALSA,
and Debian packages, uncovering widespread latent miscompilation hazards:

1. **Missing `earlyclobber` (`=&r` in C / using `lateout(reg)` instead of
   `out(reg)` in Rust):** In multi-instruction assembly templates, an output
   operand `out` is frequently written in instruction 1 before an input operand
   `in` is read in instruction 2. Unless the output is constrained as an early
   clobber (which Rust `asm!` makes the default for `out(reg)` *unless* the
   programmer writes `lateout(reg)`), the register allocator is permitted to
   assign the **same physical register** to both `out` and `in` whenever `in` is
   dead after the `asm!` block. When surrounding code changes or inlining makes
   `in` die at the `asm!` boundary, `regalloc` aliases `out` and `in`, silently
   clobbering `in` at instruction 1! `RUSTInA` found dozens of missing
   early-clobbers in production cryptographic and multimedia libraries that only
   manifested under specific inlining contexts.
2. **Undeclared condition-flag (`rflags` / `NZCV`) and subregister clobbers:**
   In Rust `asm!`, specifying `options(preserves_flags)` promises the compiler
   that status flags (`CF, PF, AF, ZF, SF, OF` on `x86-64`, `NZCV` on `AArch64`)
   are unchanged across the assembly block. If an instruction inside the block
   (such as `add`, `xor`, `and`, or `bsf`) modifies flags while
   `options(preserves_flags)` is set, the compiler hoists or reuses a prior
   `cmp` across the `asm!` block and branches on corrupted flags.
3. **System V AMD64 128-byte Red-Zone corruption under `options(nostack)`:** On
   `x86_64` System V targets (Linux, macOS, BSD), leaf functions store local
   variables and spill slots in the 128-byte red zone `[rsp - 128 .. rsp)`
   *below* the current stack pointer without decrementing `rsp`. If an `asm!`
   block is annotated with `options(nostack)` (claiming it does not touch the
   stack) yet executes `pushfq`/`popfq` or an internal `call` instruction inside
   the assembly string, the hardware decrements `rsp` by 8 bytes and **overwrites
   `[rsp - 8 .. rsp)` inside the caller's live red zone**!

#### 3.4 Architectural Lessons for Anneal's 4 `trusted/` Primitives

- **Verifying FFI boundaries and red-zone invariants via
  `StepResult.externalCall`:** In Anneal (`AbiMarshal`), every foreign call steps
  via `StepResult.externalCall (checkAbiPrecondition abiSig state)
  (postAbiBranches abiSig state)`. `checkAbiPrecondition` checks exact alignment
  (including 16-byte alignment for `i128` on SysV64/AAPCS64 and `rsp % 16 == 0`),
  while `postAbiBranches` demonically scrambles all caller-saved registers *and*
  the 128-byte red zone `[rsp - 128 .. rsp)`. Any compiler pass that leaves a
  live variable in the red zone across a call fails `Compiles` immediately.
- **Validating stack-slot sharing in `StackingPacker` against
  `MirSemantics.lean`:** Because `MirLang` in `trusted/lean/Trusted/MirSemantics.lean`
  steps to `.failed .ub` on any use of a local or dangling pointer after
  `StorageDead`, `StackingPacker` only merges two stack slots `[rsp + off]` when
  a machine-checked proof establishes that their `StorageLive`..`StorageDead`
  intervals are disjoint along all defined MIR executions.
- **Catching `lateout(reg)` / `earlyclobber` and `options(nostack)` bugs via
  demonic choice in `SmallStepMachine` (`InlineAsmSimdLifter`):** Anneal models
  `asm!` register allocation for `in(reg)` and `lateout(reg)` using
  `.choice .demonic` over all physical register assignments allowed by the
  declared constraints (including assigning the *same* register to `in(reg)` and
  `lateout(reg)`!). If the assembly writes the `lateout` register before reading
  the `in` register, the colliding demonic branch corrupts the computation and
  refutes the `InlineAsmNoUndefClobber` obligation in `VerificationResult`.

---

### 4. Binary Lifter, Linker Relaxation, SFI Sandbox, and eBPF/GPU JIT Failures

`Basis: documentation + source + derived`

#### 4.1 Unsound Binary-Lifter Semantics and Frame Assumptions (`McSema`/`Remill` PLDI 2020, `FoxDec` OOPSLA 2022)

Binary lifters (`McSema`, `Remill`, `RetDec`, `REVNG`) translate stripped or
compiled `x86-64`/`AArch64` binaries into LLVM IR for security auditing,
rewriting, or formal verification. Two landmark studies exposed deep soundness
flaws in standard binary lifters:

1. **29 single-instruction lifting bugs in `McSema`/`Remill` (Dasgupta et al.,
   PLDI 2020, DOI `10.1145/3385412.3385964`):** By validating `Remill`'s C++
   instruction-lifting templates against their formal K-framework `x86-64`
   specification (`Single-Instruction Validation`), Dasgupta et al. discovered
   **29 previously unknown wrong-code bugs** (`lifting-bits/remill#376`),
   including:
   - Failure to zero bits `32..63` of destination 64-bit general-purpose
     registers on 32-bit `cmpxchg`, `xadd`, and `movd` operations when the
     conditional comparison failed or took the false branch;
   - Incorrect `AF` (Auxiliary Carry), `OF` (Overflow), and `CF` flag updates on
     rotate/shift instructions (`rol`, `ror`, `shld`, `shrd`) when the masked
     shift count was `0` or `1`;
   - Miscomputed `RIP`-relative displacement offsets on instructions with
     multiple legacy prefixes (`66`, `F2`, `F3`, `REX`) where instruction length
     Changed between decoding and semantic evaluation.
2. **Unsound stack-frame separation and CFG recovery assumptions (`FoxDec`,
   Verbeek, Bockenek, Fu, and Ravindran, OOPSLA 2022, DOI `10.1145/3563322`):**
   Heuristic lifters like `McSema` and `RetDec` promote `[rsp + offset]` accesses
   into disjoint LLVM `alloca` variables and convert `ret` instructions into
   structured LLVM `ret` terminators *without proving* that computed heap/array
   pointers do not alias the stack frame or overwrite the saved return address
   `[rsp]`! On binaries with variable-length stack allocations (`alloca`),
   overlapping variable-length `x86` instructions, or indirect jump tables,
   heuristic lifters silently emit unsound LLVM IR that hides exploitable memory
   corruption.

#### 4.2 Post-Compilation Linker Relaxation (`R_RISCV_RELAX`, `R_X86_64_GOTPCRELX`) and `LLVM BOLT` Binary Rewriting Bugs

Even when a compiler backend emits correct relocatable object code (`.o`), the
system linker (`ld.lld`, `GNU ld`, `mold`) and post-link binary optimizers
(`LLVM BOLT`) mutate machine instructions inside `.text` *after* compilation:

- **RISC-V linker relaxation (`R_RISCV_RELAX` and `R_RISCV_ALIGN`) corrupting
  PC-relative offsets and `.eh_frame` tables:** On `RISC-V`, the compiler emits
  2-instruction sequences (`auipc ra, %pcrel_hi(sym); jalr ra, %pcrel_lo(label)(ra)`,
  8 bytes) tagged with `R_RISCV_RELAX`. When `sym` resolves within $\pm 1\text{ MiB}$,
  the linker **deletes** the 4-byte `auipc` instruction and rewrites `jalr` into
  a single 4-byte `jal` (or 2-byte compressed `c.jal` on RV32C), physically
  shrinking the `.text` section and shifting all subsequent instruction
  addresses! Multiple bugs in `ld.lld` and `GNU binutils` occurred when:
  1. Paired `R_RISCV_PCREL_LO12_I` relocations (which point to the address of
     the `auipc` instruction rather than the target symbol!) were misadjusted
     when an intervening instruction was relaxed;
  2. `.eh_frame` DWARF unwind tables, jump-table `.rodata` difference
     relocations (`R_RISCV_ADD32` / `R_RISCV_SUB32`), or section alignment pads
     (`R_RISCV_ALIGN`) were evaluated *before* relaxation finished, leaving
     off-by-2 or off-by-4 byte landing-pad and branch offsets.
- **Post-link optimizer (`LLVM BOLT`) fallthrough and jump-table corruption:**
  When `BOLT` splits hot and cold basic blocks into `.text` and `.text.cold`,
  implicit fallthrough edges must be materialized as explicit `jmp rel32`
  instructions, and indirect jump tables must be rewritten. Bugs in `BOLT` have
  repeatedly arisen when functions use inline assembly with local numeric labels,
  hand-coded jump tables, or tail calls that `BOLT` misclassifies as intra-function
  branches.

#### 4.3 `VeriWasm` (NDSS 2021) and `NaCl` SFI Sandbox Verification Edge Cases

In *"VeriWasm: Automatically Verifying Compiled WebAssembly Binaries for
Software Fault Isolation"* (NDSS 2021, DOI `10.14722/ndss.2021.24295`), Johnson,
narayanan, McMullen, Cano, Stelter, Savage, Voelker, Wahby, and Stefan built an
offline binary SFI verifier deployed in Fastly's `Lucet`/`Cranelift` edge
pipeline. Earlier SFI systems (`Google Native Client` / `NaCl` on `x86-32`,
`x86-64`, and `ARMv7`) enforced instruction-bundle alignment (`32-byte` bundles)
so that no indirect jump could land in the middle of a multi-byte `x86`
instruction to execute an unintended opcode suffix. `VeriWasm`'s deployment and
evaluation highlighted three subtle SFI verification challenges:

1. **Spilled linear-memory pointers and 32-bit zero-extension tracking across
   basic-block joins:** When Cranelift spilled a 32-bit zero-extended guest
   offset (`mov eax, eax`) to a stack slot and reloaded it in a join block, an SFI
   verifier must prove that the stack slot itself was not overwritten by an
   unmasked 64-bit value along any incoming CFG edge (precisely the pattern where
   `CVE-2021-32629` sign-extended the reload instead of zero-extending it!).
2. **Indirect call table (`call_indirect`) index masking vs. function-signature
   check ordering:** If a compiled Wasm binary loads a function pointer from the
   indirect table before checking or masking the table index, an out-of-bounds
   table index can read an attacker-controlled value from adjacent memory and
   jump to an arbitrary host gadget.
3. **Stack-pointer (`rsp`) vs. linear-memory base (`r15`/`rdi`) separation:**
   Because Wasm's execution stack lives in host virtual memory outside the 4 GiB
   linear memory, every `[rsp + disp]` access in the compiled native code must
   be statically proven to stay within the guard page below the Wasm execution
   stack (`stack_limit`).

#### 4.4 Linux Kernel eBPF JIT Miscompilations (`CVE-2021-29154` and `Jitterbug` OSDI 2020)

The Linux kernel executes untrusted or semi-trusted eBPF programs inside ring 0
by first running a static abstract-interpretation verifier (`kernel/bpf/verifier.c`)
and then compiling the verified eBPF bytecode to native machine code via
per-architecture JIT compilers (`arch/*/net/bpf_jit_comp*.c`). Even when the
eBPF bytecode verifier is completely sound, a bug in the native JIT compiler
translates safe eBPF instructions into arbitrary ring-0 machine code:

- **`CVE-2021-29154` (`arch/x86/net/bpf_jit_comp.c` branch displacement
  convergence flaw):** On `x86_64` and `i386`, `do_jit()` runs multiple
  iterative passes to shrink 32-bit relative jumps (`jmp rel32`, 5 bytes; `jcc
  rel32`, 6 bytes) into 8-bit short jumps (`jmp rel8`, 2 bytes) whenever the
  target displacement fits in $[-128, +127]$, recording cumulative instruction
  end offsets in an array `addrs[i]`. However, when emitting a **backward
  branch** from instruction `i` to an earlier instruction `t < i` during pass $p$,
  `do_jit()` computed the branch displacement using `addrs[t]` (which had
  *already* been overwritten with pass $p$'s shrunk offset) subtracted from
  `addrs[i]` (which still held pass $p - 1$'s unshrunk offset!). An attacker
  could construct a sequence of eBPF jumps where the pass size appeared to
  converge (`proglen == oldproglen`), causing `do_jit()` to emit the final binary
  image with a corrupted relative jump offset that landed **in the middle of a
  multi-byte `x86-64` immediate operand**, executing arbitrary attacker-chosen
  bytes in kernel mode.
- **`Jitterbug` (Nelson, Van Geffen, Torlak, and Wang, OSDI 2020):** Using
  symbolic verification in Rosette/Serval against the Linux kernel's production
  eBPF JITs (`x86-64`, `x86-32`, `ARM64`, `ARM32`, `RV64G`, `RV32G`), `Jitterbug`
  discovered and fixed **16+ previously unknown wrong-code bugs** in mainline
  Linux:
  1. **`ALU64_ARSH` / `RSH` / `LSH` shift-by-zero corruption on `ARM32` and
     `x86-32`:** When lowering a 64-bit shift (`BPF_ALU64 | BPF_ARSH | BPF_X`)
     onto a pair of 32-bit registers `(hi, lo)`, a runtime shift amount of `0`
     executed a shift by `32 - 0 = 32` on the complementary word, corrupting the
     upper/lower 32 bits!
  2. **`JMP32` (`BPF_JSET | BPF_X`) missing upper-32-bit masking on `x86-32`
     (`ia32`):** The 32-bit bitwise-test jump tested the high 32 bits instead of
     ignoring them, branching in the opposite direction from the eBPF verifier's
     abstract prediction!
  3. **`ARM32` `BPF_MEM | BPF_DW` offset overflow:** When loading a 64-bit word
     at stack offset `off` near the 8-bit/12-bit immediate boundary (`off = 252`),
     loading the high 32-bit word at `off + 4 = 256` overflowed the instruction's
     immediate field and read from offset `0` instead.
  4. **`RV32G` tail-call stack-pointer corruption:** Miscomputed prologue/epilogue
     stack adjustments during `bpf_tail_call` transitions corrupted callee-saved
     registers.

#### 4.5 GPU Shader Compiler Miscompilations and SIMT Divergence Bugs (`GraphicsFuzz`, OOPSLA 2017)

In *"Automated Testing of Graphics Shader Compilers"* (OOPSLA 2017, DOI
`10.1145/3133917`), Donaldson, Evrard, Lascu, and Thomson applied metamorphic
semantics-preserving transformations (`GLFuzz` / `GraphicsFuzz`) across **17 GPU
driver stacks spanning all 7 major GPU architectures** (AMD, Apple, ARM Mali,
Imagination PowerVR, Intel, NVIDIA, Qualcomm Adreno), discovering **more than 60
distinct bugs across every tested vendor** (`CVE-2017-2424`, `CVE-2017-6259`):

- **SIMT execution-mask (`exec`) reconvergence corruption across nested loops and
  `switch`/`continue`/`break`:** On SIMT GPUs (such as AMD GCN/RDNA and NVIDIA
  PTX), 32 or 64 threads in a wavefront execute in lockstep under a bitmask of
  active lanes (`exec`). When threads diverge at an `if` or `loop` exit, the
  compiler lowers structured SPIR-V/GLSL control flow (`OpSelectionMerge`,
  `OpLoopMerge`) into explicit scalar mask-save and mask-restore instructions
  (`s_and_saveexec_b64`). `GraphicsFuzz` repeatedly triggered wrong-code bugs
  where dead-code or jump-threading optimizations bypassed the mask-restoration
  block on a `continue` or early `return`, leaving surviving threads permanently
  masked off (`exec == 0`) or executing subsequent instructions with the wrong
  lane mask.
- **Divergent workgroup barrier hangs and cross-origin VRAM leaks:** When loop
  unswitching or branch hoisting moved a `barrier()` / `OpControlBarrier` into a
  path where only a subset of wavefront lanes were active, the GPU hardware
  deadlocked (triggering OS kernel panics / Windows BSODs), while out-of-bounds
  register/spill indexing leaked uninitialized VRAM contents from other browser
  tabs (`CVE-2017-2424`).

#### 4.6 Cross-Cutting Architectural Synthesis: How Historical Failures Map to Anneal's 4 `trusted/` Primitives

| Historical Failure Case & Primary Source | Root-Cause Mechanism | Anneal `trusted/` Primitive & Prevention Mechanism |
| :--- | :--- | :--- |
| **`CompCert` 1.6–1.8 `PrintAsm.ml` & `C2C` Bugs** (Yang et al., PLDI 2011) | Unverified front-end elaborator and unverified OCaml assembly printer outside the Coq proof | **Single-Source `.olean` Emission (`anneal-audit`):** `anneal-rustc-capture` extracts post-elaboration `Runtime(PostCleanup)` MIR directly, and `Trusted.emitX86CrateAsm` / `Trusted.emitCrateElfBytes` are kernel-evaluated constants verified byte-for-byte against on-disk outputs. |
| **Standard `CompCert` Stack Overflow** (`Stack-Aware CompCert`, POPL 2019) | Infinite abstract stack blocks in `Mem.v` ignore finite hardware stack limits | **`ProductiveOn` + `InhabitedPre` + `VerificationResult`:** `StackingPacker` pairs `Compiles` with `StackFrameMachLang.ProductiveOn (StackHeadroomPre bound) t` and emits `StackBound::<fn>` obligations. |
| **`seL4` `GraphRefine` `-O2` Loop & Inline-Asm Exclusions** (Sewell et al., PLDI 2013) | Monolithic SMT translation validation fails on unrolled loops and opaque `asm volatile` | **Positive Per-Obligation `VerificationResult` + `Abstracts`:** `LlvmO3Validator` and `InlineAsmSimdLifter` emit per-cut-point and per-`asm!` obligations; `asm!` blocks are decoded via `BijectiveCodecIsa` and lifted via `Abstracts`. |
| **`Cranelift` `CVE-2021-32629` & `CVE-2023-26489`** (`Wasmtime` SFI Escapes) | 32-bit sign-extension (`movslq`) on spill reload ($-2\text{ GiB}$ escape) and 35-bit scaled EA ($+34\text{ GiB}$ escape) | **Target-Level `ProductiveOn` (`WasmSfiSandbox`):** Requires `X86SandboxedLang.ProductiveOn HostSandboxPre (compileWasmSfi u)` directly on the target machine, where any access outside `[r15 .. r15 + 4GiB + guard)` is `.failed .ub`. |
| **`Cranelift` `CVE-2022-31104` & `VeriISLE` Bugs** (PLDI 2024, ASPLOS 2024) | `i8x16.swizzle` input-register overwrite, `v128` `select` 32-bit truncation, dirty upper bits, `cmov` flag clobbers | **Partial `BehaviorCodec.decodeOut` + `SmallStepMachine`:** `decodeOut : L₂.Out → Option L₁.Out` rejects dirty upper bits (`none`); `X86Machine` models explicit `rflags` clobbers (`xor`) and register aliasing (`checkRegAlloc`). |
| **`rustc`/`LLVM` `i128` ABI (`#54341`) & Red-Zone Bugs** (`abi-cafe`, `TInA` ASE 2019) | 8-byte vs. 16-byte `i128` alignment skew; live data in `[rsp - 128 .. rsp)` red zone clobbered by call/`pushfq` | **`StepResult.externalCall (boundaryInv) (branches)`:** Checks 16-byte alignment in `boundaryInv` (or steps to `.failed .ub`) and demonically scrambles caller-saved registers and the 128-byte red zone in `branches`. |
| **`rustc`/`LLVM` `StackColoring` Bugs (`#46606`, `#91899`)** | Merging stack slots whose `StorageLive`..`StorageDead` ranges overlap or escape via raw pointers | **`MirSemantics.lean` + `StackingPacker` `Compiles`:** Any dereference after `StorageDead` is `.failed .ub` in `MirLang`; `StackingPacker` must prove slot disjointness across all defined MIR executions to establish `Compiles`. |
| **`RUSTInA` Missing `earlyclobber` in `asm!`** (Recoules et al., ICSE 2021) | Output written before input read when `lateout(reg)` aliases `in(reg)` | **Demonic Choice (`.choice .demonic`) in `SmallStepMachine`:** `InlineAsmSimdLifter` branches demonically over all valid physical register assignments (including `lateout == in`), refuting missing `earlyclobber` deterministically. |
| **`McSema`/`Remill` 29 Lifter Bugs & `FoxDec`** (PLDI 2020, OOPSLA 2022) | Unverified single-instruction templates and unproved stack/return-address separation assumptions | **Upward `Abstracts` + `Partial` Top ($\top$) + `VerificationResult`:** Lifters prove `Abstracts L_v ElfBinaryLang` against a shared `BijectiveCodecIsa` semantics and surface `ReturnAddrUnmodified`/`StackFrameSeparation` as explicit obligations. |
| **`R_RISCV_RELAX` Linker & `CVE-2021-29154` eBPF JIT Bugs** (`Jitterbug`, OSDI 2020) | Post-codegen instruction deletion/shrinking and mixed-pass `addrs[]` branch displacement corruption | **`EventualBehaviorOf` + Post-Relaxation `MachineBytesLang` Verification:** `BijectiveCodecIsa` and `AnnealLinkELF` prove `Compiles` on the *final relaxed byte array* fetched by `rip`, while `EbpfJitterbug` chains `Abstracts` + `ProductiveOn` + `Compiles`. |
| **`GraphicsFuzz` SIMT Shader Bugs** (Donaldson et al., OOPSLA 2017) | Divergent workgroup barrier deadlocks and corrupted `exec` lane masks across loop exits | **Wavefront `SmallStepMachine` (`GpuShaderGuardian`):** Models lockstep 64-lane state + `exec` mask; non-uniform barrier (`exec != fullMask`) steps to `.failed .ub`, caught by `ProductiveOn` and `Compiles`. |

## Boundaries

1. **Microarchitectural transient execution and hardware side channels (`not examined`):**
   While Section 2.4 documents architectural condition-flag clobbering in
   Cranelift's branchless Spectre-guard lowering (`cmov` preceded by `xor`),
   neither Anneal's current `SmallStepMachine` in
   `trusted/lean/Trusted/StepResult.lean` nor the historical correctness proofs
   in `CompCert`/`CakeML`/`Jitterbug` model speculative out-of-order cache-timing
   channels without an explicit leakage-trace `Obs` instantiation.
2. **Asynchronous hardware interrupts and kernel page-table self-modification
   (`not examined`):** Section 1.4 and Section 3.3 analyze red-zone corruption
   under synchronous `call`/`pushfq` instructions and `seL4`'s context-switch
   exclusions, but full preemptive interrupt delivery on an unadjusted kernel
   stack pointer requires an interrupt-aware `SmallStepMachine` interleaving not
   evaluated in the current `Trusted/X86Semantics.lean` sequential model.
3. **Closed-source vendor GPU backend internals (`unknown`):** For the
   `GraphicsFuzz` shader compiler bugs in Section 4.5 (`CVE-2017-2424`,
   `CVE-2017-6259`), the input GLSL/SPIR-V reproducers and observable
   wrong-image/hang outcomes are established in the published OOPSLA 2017
   artifact, whereas the proprietary internal IR pass names inside closed-source
   NVIDIA and Apple shader drivers remain uninspected (`unknown`).

## Evidence

- **Anneal workspace and trusted core (`source`):**
  - `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`:
    `PRINCIPLES.md` (lines 18–55), `AGENTS.md` (lines 67–98),
    `trusted/lean/Trusted.lean` (lines 1–11),
    `trusted/audit/src/main.rs`, and `trusted/rustc-capture/src/main.rs`.
  - `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`:
    `trusted/lean/Trusted/Refinement.lean` (`Partial`, `Behavior`, `Language`,
    `BehaviorCodec`, `Compiles`, `Abstracts`, `Compiler.SoundOn`,
    `Compiler.Verified`, `VerificationResultOn`),
    `trusted/lean/Trusted/StepResult.lean` (`StepResult`, `SmallStepMachine`,
    `BehaviorOf`), and `trusted/lean/Trusted/MirSemantics.lean`.
  - `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`:
    `trusted/lean/Trusted/X86Semantics.lean`,
    `theory/Anneal/Compiler/NaiveCodegen.lean`, and
    `theory/Anneal/Compiler/Peephole.lean`.
- **Verified compiler and kernel translation-validation postmortems (`documentation`):**
  - Xuejun Yang, Yang Chen, Eric Eide, and John Regehr, *"Finding and
    Understanding Bugs in C Compilers,"* PLDI 2011, pp. 283–294, DOI
    `10.1145/1993498.1993532` (Section 2 & Section 3.4 on `CompCert` 1.6–1.8
    front-end `C2C` and assembly-generation bugs).
  - Yuting Wang, Pierre Wilke, and Zhong Shao, *"An Abstract Stack Based
    Approach to Verified Compositional Compilation to Machine Code,"* PACMPL
    3(POPL), Article 62, January 2019, DOI `10.1145/3290380` (`Stack-Aware
    CompCert`).
  - Thomas Sewell, Magnus Myreen, and Gerwin Klein, *"Translation Validation for
    a Verified OS Kernel,"* PLDI 2013, pp. 471–482, DOI
    `10.1145/2491956.2462183` (`seL4` ARMv7 binary translation validation with
    `GraphRefine`).
- **`Cranelift` / `Wasmtime` CVEs, `VeriISLE`, and `regalloc2` (`documentation`):**
  - Bytecode Alliance Security Advisories: `CVE-2021-32629`
    (`GHSA-hpqh-2wqx-7qp5`, sign-extension on 32-bit stack reload in
    `cranelift-codegen` `< 0.73.1`), `CVE-2022-31104` (`GHSA-jqwc-c49r-4w2x`,
    `i8x16.swizzle` input overwrite and `v128` `select` 32-bit move in
    `cranelift-codegen` `< 0.85.1`), `CVE-2022-39392` (`GHSA-44mr-8vmm-wjhg`,
    pooling allocator `memory_pages: 0` in `Wasmtime` `< 2.0.2`),
    `CVE-2023-26489` (`GHSA-ff4p-7xrq-q5r8`, 35-bit effective address in
    `x86_64` ISLE rules in `Wasmtime` `< 4.0.1 / 5.0.1 / 6.0.1`), and
    `CVE-2023-30624` (`GHSA-c87w-297f-6568`, `&VMContext` aliasing UB in
    `Wasmtime` `< 6.0.2 / 7.0.1 / 8.0.1`).
  - Alexa VanHattum et al., *"Lightweight, Modular Verification for WebAssembly-to-Native
    Instruction Selection"* (`Crocus`), ASPLOS 2024, DOI
    `10.1145/3620665.3640369`; and *"Verifying Instruction Selection Rules in
    Cranelift"* (`VeriISLE`), PLDI 2024, DOI `10.1145/3656427`.
- **ABI marshaling, `StackColoring`, and inline assembly (`documentation`):**
  - `rust-lang/rust` issues `#54341` (`i128`/`u128` alignment on System V AMD64
    and AAPCS64, resolved in Rust 1.77–1.78 with LLVM 18), `#46606` and `#91899`
    (`StorageLive`/`StorageDead` + LLVM `StackColoring.cpp` slot-sharing
    miscompilations), and `Gankra/abi-cafe`.
  - Frédéric Recoules, Sébastien Bardin, Richard Bonichon, Laurent Mounier, and
    Marie-Laure Potet, *"Get Out of the Valley: Lifting Inline Assembly to IR"*
    (`TInA`), ASE 2019, DOI `10.1109/ASE.2019.00069`; and *"Assess and Heal:
    Automated Inline Assembly Compliance"* (`RUSTInA`), ICSE 2021, DOI
    `10.1109/ICSE43902.2021.00069`.
- **Binary lifters, linkers, SFI, eBPF JITs, and GPU shaders (`documentation`):**
  - Sandeep Dasgupta, Sushant Dinesh, Deepan Venkatesh, Vikram S. Adve, and
    Christopher W. Fletcher, *"Scalable Validation of Binary Lifters,"* PLDI
    2020, pp. 655–671, DOI `10.1145/3385412.3385964` (`McSema`/`Remill` 29 bugs
    in `lifting-bits/remill#376`).
  - Freek Verbeek, Joshua Bockenek, Zhoulai Fu, and Binoy Ravindran, *"Formally
    Verified Lifting of C-Compiled x86-64 Binaries"* (`FoxDec`), OOPSLA 2022,
    DOI `10.1145/3563322`.
  - Evan Johnson et al., *"VeriWasm: Automatically Verifying Compiled
    WebAssembly Binaries for Software Fault Isolation,"* NDSS 2021, DOI
    `10.14722/ndss.2021.24295`.
  - Linux kernel `CVE-2021-29154` (`arch/x86/net/bpf_jit_comp.c` backward-branch
    displacement oscillation); Luke Nelson, Jacob Van Geffen, Emina Torlak, and
    Xi Wang, *"Specification and Verification in the Field: Applying Formal
    Methods to BPF Just-in-Time Compilers in the Linux Kernel"* (`Jitterbug`),
    OSDI 2020, ISBN `978-1-939133-19-9`, pp. 41–61.
  - Alastair F. Donaldson, Hugues Evrard, Andrei Lascu, and Paul Thomson,
    *"Automated Testing of Graphics Shader Compilers"* (`GraphicsFuzz`), PACMPL
    1(OOPSLA), Article 93, October 2017, DOI `10.1145/3133917`.

## Revalidation

To revalidate the architectural alignment between these historical failure modes
and a newer revision of Anneal's `trusted/lean/` and `theory/` layers:

1. **Check single-source emission and boundary audit:** Inspect
   `trusted/audit/src/main.rs` and `trusted/lean/Trusted/X86Semantics.lean` (or
   the current backend target semantics) to confirm that emitted assembly/ELF
   bytes remain defined as kernel-checked constants inside `.olean` and are
   byte-compared against on-disk artifacts without an unverified pretty-printer
   (Section 1.1, Section 4.2).
2. **Check `BehaviorCodec`, `EventualBehaviorOf`, and `StepResult.externalCall`
   definitions:** Diff `trusted/lean/Trusted/Refinement.lean` and
   `trusted/lean/Trusted/StepResult.lean` against
   `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` and the mechanized
   probes in
   `reports/anneal-behavior-codec-and-progress-refinement-2026/support/BehaviorCodecExpressiveness.lean`
   to verify that:
   - Partial `decodeOut : L₂.Out → Option L₁.Out` rejects invalid subregister
     and narrow-type bit patterns (Section 2.3, Section 2.5);
   - `ProductiveOn` + `InhabitedPre` can be stated directly on target sandboxed
     machines (`X86SandboxedLang` / `KernelIsaLang`) to block `CVE-2021-32629`
     and `CVE-2023-26489` even on untrusted/UB guest inputs (Section 2.1,
     Section 2.2, Section 4.3, Section 4.4);
   - `StepResult.externalCall` and `.choice .demonic` enforce caller ABI
     alignment preconditions (`i128` 16-byte alignment, `rsp % 16 == 0`),
     scramble caller-saved registers and the 128-byte System V red zone, and
     branch over all legal physical-register assignments for `asm!` constraints
     (Section 3.1, Section 3.3).
