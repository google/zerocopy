<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Real-World Tool Deep-Dive and `trusted/` Architecture Mapping for Backend Codegen, Register Allocation, Binary/Linker Tooling, Lifters, and Sandboxes

## Summary

Across compiler backends, register allocators, instruction schedulers,
machine-code assemblers and linkers, post-link binary optimizers, translation
validators for industrial compilers (`rustc + LLVM -O3`, `Cranelift`, `GCC`),
binary and inline-assembly lifters, and native sandboxing/JIT engines
(`Wasm/SFI`, `eBPF`, `SPIR-V/WGSL`), **22 concrete verification workflows** and
**over 50 real-world formal and industrial systems** reduce to Anneal's four
orthogonal `trusted/lean/` primitives—plus single-source `.olean`-bound artifact
emission—without introducing new trusted axioms or expanding the `trusted/`
boundary:

1. **`Language (SemObs : Type)` and `BehaviorCodec L₁ L₂`
   (`trusted/lean/Trusted/Refinement.lean`):** Parameterizing `Language SemObs`
   by an external observation classifier `obs : Out → SemObs` over
   `Behavior Query Out := Query → Partial (Out → Prop)` allows source, IR,
   relocatable object, and flat-memory machine languages (`MirLang`,
   `ClightLang`, `VRegIsaLang`, `X86AsmLang`, `LinkedElfLang`) with distinct
   internal state representations to compose horizontally and vertically over a
   shared `SemObs := EventualOut IoObs Unit` spine. Generalizing `decodeOut` to
   a partial map `L₂.Out → Option L₁.Out` obeying left-inversion
   (`decodeOut (encodeOut o₁) = some o₁`), partial-injectivity
   (`decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`), and observation preservation
   (`obs_decodeOut`) cleanly handles target representations of strictly larger
   cardinality (such as 8-bit/64-bit registers holding 2-valued Rust `bool`,
   `VEX`-zeroed upper AVX lanes `bits 128..511`, and preserved callee-saved
   registers) while requiring unobservable caller-saved scratch registers
   (`r10`, `r11`, dead `rflags`) and popped stack bytes below `rsp` to be
   quotiented in `L₂.Out`.
2. **Dual Polarities of `Compiles` and `Abstracts` over `Partial`:** Downward
   compilation (`Compiles L₁ L₂ codec s t := L₂.sem t ≤ codec.toMorphism (L₁.sem s)`)
   and upward binary lifting or decompilation
   (`Abstracts L_v L_src codec v s := L_src.sem s ≤ codec.toMorphism (L_v.sem v)`)
   are dual instances of the single refinement inequality over `Partial`. In
   downward compilation (`LlvmO3Validator`, `SouperCert`, `AnnealLinkELF`),
   source undefined behavior (`(L₁.sem s q).defined = False`, top element $\top$
   of `Partial`) licenses aggressive compiler optimizations and flat-memory
   global adjacency without hardware guard pages between globals. Conversely, in
   upward binary lifting (`GraphLangBinaryLifter`, `VerifiedDecompiler`,
   `InlineAsmSimdLifter`), emitting an assertion failure `.failed .ub` ($\top$)
   in the lifted IR on unresolved dynamic jump targets (`jmp rax`) makes
   `Abstracts` hold immediately during lifting and defers the bounds proof
   (`rax < N`) cleanly to the high-level `ProductiveOn` proof.
3. **Target-Level `ProductiveOn` and `InhabitedPre` for Untrusted Sandboxes:**
   Because `Compiles SrcLang TgtLang` is conditional on the source program being
   free of undefined behavior, `Compiles` alone vacates its safety promise when
   an adversary supplies a malicious input module `u` with source-level UB.
   Stating isolation directly at the target machine via
   `X86SandboxedLang.ProductiveOn (HostSandboxPre bounds) (compileWasmSfi u)`
   (paired with `InhabitedPre`) certifies unconditional Software Fault Isolation
   (SFI) containment and bounded stack headroom (`StackingPacker`) even on
   adversarial inputs, while combining `Abstracts` + `ProductiveOn` + `Compiles`
   forms the verification triangle required by in-kernel bytecode JITs
   (`EbpfJitterbug`).
4. **`SmallStepMachine` with `EventualBehaviorOf` and
   `StepResult.externalCall` (`trusted/lean/Trusted/StepResult.lean`):**
   `EventualBehaviorOf` internalizes silent step counts inside
   `Out := EventualOut Obs Val`, absorbing $1 \to k$ template expansion
   (`NaiveCodegen`), $k \to 1$ addressing-mode contraction (`VeriISLE`),
   $0 \leftrightarrow k$ parallel-move cycle breaking and coalescing
   (`CertRegAlloc2`), $0 \leftrightarrow 1$ fallthrough-to-`jmp` inversions in
   post-link binary layout (`BoltPropellerTV`), cross-iteration loop pipelining
   (`ModuloPipelines`), and lockstep 64-lane SIMT wavefront execution
   (`GpuShaderGuardian`). Meanwhile,
   `StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop)`
   captures the exact two-sided contract of multi-target calling conventions
   (`AbiMarshal`, `DimSumLink`): callers must establish `boundaryInv = true`
   (16-byte `rsp` alignment, valid register/stack arguments, and no live data in
   the 128-byte System V red zone across `call`) or step to `.failed .ub`, and
   must survive every demonic post-call state in `branches` (clobbered
   caller-saved registers and red zone, preserved callee-saved registers).
5. **Positive Per-Obligation `VerificationResult` and Single-Source `.olean`
   Artifact Binding:** Decomposing custom ISLE rule side conditions, stack-frame
   watermarks, ELF relocation range checks, translation-validator cut-point VCs,
   `core::arch::asm!` clobber/option contracts, and decompiler frame-separation
   assumptions into positive disjunctive clauses (`ob.id ∈ waived ∨ ob.prop`) in
   `VerificationResult` prevents a waived or unverified obligation from
   contaminating verified passes via Principle of Explosion. Binding final
   emitted assembly (`Trusted.emitX86CrateAsm : String`) or linked ELF bytes
   (`Trusted.emitCrateElfBytes : ByteArray`) inside the kernel-checked `.olean`
   environment and verifying byte-for-byte identity in `anneal-audit` eliminates
   dual-emitter drift between the verified Lean model and the binary executed by
   hardware.

## Applicability

The findings in this report apply to Anneal's verification architecture across
`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` (trusted core
refinement and `SmallStepMachine` primitives),
`joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14` (MIR-to-x86-64 codegen
and `.olean` boundary audit), and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`
(`v4.34.1`), evaluated in comparative relationship with the 11 external compiler,
binary, lifter, and sandbox subject clusters recorded in `REPORT.json`:

- **Target architectures and ABIs:** `x86-64` (System V AMD64 LP64 and Windows
  x64), `AArch64` (AAPCS64), `RISC-V RV64GC` (LP64D with compressed `RVC`
  quadrants `00/01/10` and `Zba`/`Zbb`), plus virtual/accelerator ISAs (`Wasm`,
  Linux `eBPF`, `SPIR-V`/`WGSL` over `AMDGPU GCN/RDNA` and `NVIDIA PTX`).
- **Scope separation:** Statements regarding Anneal's `trusted/lean/` definitions
  (`Language`, `BehaviorCodec`, `Compiles`, `Abstracts`, `ProductiveOn`,
  `InhabitedPre`, `VerificationResult`, `SmallStepMachine`,
  `EventualBehaviorOf`, `StepResult.externalCall`) and `NaiveCodegen` /
  `Peephole` implementations are grounded directly in the inspected
  `joshlf/anneal` revisions. Designs for the 22 backend, binary, lifter, and
  sandbox tools (`Use Case 1` through `Use Case 22`) represent derived
  architectural mappings demonstrating how `theory/` modules instantiate those
  fixed `trusted/` primitives without modifying `trusted/lean/`.

## Findings

### 1. Category A: Instruction Selection, Peepholes & Superoptimization (Use Cases 1–4)

`Basis: source + normative + documentation + derived`

#### 1.1 Real-World Tool Family Deep-Dive

1. **`CompCert` (`AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`,
   v3.18; `Selection.v`, `RTLgen.v`, `Mach.v`, `Asm.v`):**
   - *Goals & Target Users:* Embedded avionics, automotive, nuclear, and
     systems engineers requiring a mathematically verified C (`Clight`) to
     assembly (`PowerPC`, `ARM`, `x86-64`, `RISC-V`, `AArch64`) compiler (Leroy,
     CACM 2009, DOI `10.1145/1538788.1538814`).
   - *History & Lineage:* Initiated at INRIA by Xavier Leroy (2005–present);
     commercialized by AbsInt for DO-178B/C Level A flight-control software.
   - *Design Philosophy & Tradeoffs:* Uses constructive Coq/Rocq forward/backward
     simulation proofs across ~20 small passes (`Cshmgen` → `Selection` →
     `RTLgen` → `Tailcall` → `Inlining` → `Constprop` → `CSE` → `Allocation` →
     `Tunneling` → `Linearize` → `CleanupLabels` → `Stacking` → `Asmgen`). In
     `backend/Selection.v`, instruction selection uses hand-written non-monadic
     smart constructors wrapped in Coq extraction-time `compilenv` patterns to
     fold addressing modes (`Aindexed`, `Aindexed2`, `Ascaled`) and strength
     reductions.
   - *Ecosystem Comparison:* Unlike `CakeML` (which compiles functional source all
     the way to machine bytes inside HOL4) or `Cranelift` (which uses a
     declarative DSL `ISLE`), `CompCert` stops at symbolic assembly ASTs (`Asm`)
     and relies on an external assembler/linker (or `CompCertELF` / `Valex`)
     unless extended.
   - *Formal Theory & TCB:* Small-step transition systems parameterized by trace
     events (`trace := list event`), memory injections (`Mem.inject`), and
     simulation diagrams (`forward_simulation` flipped to `backward_simulation`
     via target receptiveness and determinism). The TCB includes Coq's kernel,
     OCaml extraction, the C parser (partially verified via `Menhir`/`Verasco`),
     and the unverified GNU assembler/linker.

2. **`CakeML` (`CakeML/cakeml`, `wordLang` → `stackLang` → `labLang`; Tan et al.,
   JFP 2019, DOI `10.1017/S0956796818000229`):**
   - *Goals & Target Users:* High-assurance ML applications and verified hardware
     (`Silver`) requiring an end-to-end verified compiler from source ASTs down
     to raw machine-code byte arrays (`x86-64`, `ARMv7`, `AArch64`, `MIPS`,
     `RISC-V`) with a verified GC and in-logic bootstrapping.
   - *History & Lineage:* Developed in HOL4 by Magnus Myreen, Scott Owens, Ramana
     Kumar, Yong Kiam Tan, Anthony Fox, and collaborators (2014–present).
   - *Design Philosophy & Tradeoffs:* Prioritizes end-to-end machine-byte
     completeness over aggressive mid-end instruction selection. Instruction
     selection flattens `BVI`/`dataLang` into `wordLang` (an imperative SSA-like
     register language with explicit 64-bit word operations and maximal-munch
     instruction selection into `inst` nodes), lowers spills in `stackLang`, and
     resolves labels in `labLang`.
   - *Formal Theory & TCB:* Functional big-step (clocked) semantics (`evaluate`)
     avoiding coinduction; TCB is restricted to the HOL4 kernel and the target
     L3 ISA model (`asmProps`).

3. **`CertiCoq` (`CertiCoq/certicoq`) and `Oeuf` (`uwplse/oeuf`, Mullen et al.,
   CPP 2018, DOI `10.1145/3167089`):**
   - *Goals & Lineage:* `CertiCoq` (Anand, Appel, Morrisett, Paraskevopoulou,
     et al.) compiles Gallina (`Template-Coq`) via ANF/CPS to `Clight` so
     `CompCert` serves as the backend; `Oeuf` (UW PLSE) restricts Coq terms to a
     eliminator-based subset and compiles them directly into `CompCert` `Cminor`,
     eliminating OCaml extraction from the TCB of verified Coq passes (such as
     `Peek`).

4. **`QBE` (`c9x.me/compile/`, Quentin Carbonneaux) and `Cranelift` / `ISLE`
   (`bytecodealliance/wasmtime`, `cranelift/isle`):**
   - *Goals & Lineage:* `QBE` provides a compact C backend aiming for 70% of
     LLVM's performance in 10% of the code; `Cranelift` is the production Rust
     compiler backend for `Wasmtime` and `rustc_codegen_cranelift` (`cg_clif`),
     designed by Chris Fallin, Nick Fitzgerald, and Bytecode Alliance engineers.
   - *Design Philosophy:* Replaced imperative Rust pattern-matching backends with
     **`ISLE`** (Instruction Selection and Lowering Expressions), a strongly
     typed, prioritized term-rewriting DSL with pure constructors and extractors
     that compiles to deterministic decision trees (`cranelift/isle/`).

5. **`VeriISLE` and `Crocus` (`bytecodealliance/wasmtime/tree/main/cranelift/isle/veri`,
   VanHattum, Pardeshi, Fallin, Sampson, Brown, ASPLOS 2024, DOI
   `10.1145/3620665.3640367`; Pardeshi CMU-CS-23-126):**
   - *Goals & Lineage:* Modular SMT-based formal verification of Cranelift's
     `ISLE` lowering rules for `AArch64` and `x86-64`.
   - *Design Philosophy & Tradeoffs:* Annotates `ISLE` terms with width-polymorphic
     bitvector specifications (`cranelift/isle/veri/meta/src/`) and verifies each
     rule compositionally over SMT-LIB (`QF_BV`). Discovered and reproduced real
     Cranelift CVEs (including CVE-2023-26489, CVSS 9.9, an `x86-64` addressing-mode
     sign-extension offset miscalculation).

6. **Peephole Optimizers and Superoptimizers (`Peek`, `Chamois-CompCert postpass`,
   `Hydra`, `Slothy`, `Souper`, `Minotaur`, `STOKE`):**
   - **`Peek` (Mullen, Daryl, Tatlock, Grossman, PLDI 2016, DOI
     `10.1145/2908080.2908109`):** Verified peephole optimizer for `CompCert`
     x86 assembly using a parametric liveness-masked step equivalence relation
     (`peephole_step`) checking condition-flag and scratch-register liveness.
   - **`Chamois-CompCert postpass` (Six, Boulmé, Monniaux, OOPSLA 2020 / CPP
     2022):** Verified post-register-allocation peephole and pairing pass (e.g.,
     fusing adjacent 64-bit loads/stores into AArch64 `ldp`/`stp` load/store
     pair instructions and Kalray KVX 128-bit/256-bit paired loads).
   - **`Hydra` (Mukherjee, Regehr, OOPSLA 2024):** Automatically generalizes
     concrete superoptimizer rewrite discoveries (`Souper`) into width-independent
     symbolic peephole rules with synthesized preconditions verified via
     `Alive2`.
   - **`Slothy` (`slothy-optimizer/slothy`, Abdulrahman, Kannwischer, et al.,
     TCHES 2024):** Constraint-programming (`CP-SAT` OR-Tools) superoptimizer
     that jointly performs instruction scheduling, register renaming, and loop
     software pipelining on handwritten cryptographic assembly (`ARMv8-A NEON`,
     `ARMv8.1-M Helium/MVE`, `RISC-VRV64`), paired with automated equivalence
     checks.
   - **`Souper` (`google/souper`, Sasnauskas et al., arXiv:1711.04422) &
     `Minotaur` (`minotaur-toolkit/minotaur`, Liu, Stefan, Regehr, CGO 2024, DOI
     `10.1109/CGO57630.2024.10444836`):** CEGIS-based synthesizing
     superoptimizers for LLVM IR (`Souper` for scalar integer SSA; `Minotaur`
     for vector/SIMD intrinsics including `x86-64` AVX2/AVX-512 and `AArch64`
     SVE/NEON, using `Alive2` as its SMT TV oracle).
   - **`STOKE` (`StanfordPL/stoke-release`, Schkufza, Sharma, Aiken, ASPLOS
     2013, DOI `10.1145/2451116.2451150`):** Stochastic MCMC superoptimizer
     exploring loop-free `x86-64` assembly sequences via hardware performance
     models and bitvector/FP SMT symbolic equivalence validators (`strata`).

---

#### 1.2 Concrete Tool Specifications & Mapping onto Anneal's `trusted/` Primitives (Use Cases 1–4)

##### Use Case 1: `NaiveCodegen` — Constructive Multi-Target Baseline Code Generator (`x86-64`, `AArch64`, `RISC-V RV64GC`)

- **Role & Problem Solved:** Constructive, total, zero-search baseline backend in
  pure Lean 4 (`theory/Anneal/Compiler/NaiveCodegen.lean` in
  `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`, generalized to
  `X86_64`, `AArch64`, and `RiscV64GC`). Assigns every MIR local `_0 .. _n` a
  dedicated, non-overlapping 8-byte-aligned stack frame slot (`[rbp - offset]`,
  `[x29 - offset]`, or `[s0 - offset]`) and lowers every MIR `Statement` and
  `Terminator` via fixed instruction templates through designated scratch
  registers (`rax`, `rcx`, `rdx`). Provides an immediately auditable,
  compile-time-fast verified path from `Runtime(PostCleanup)` MIR to native
  machine code without trusting LLVM or Cranelift.
- **Mapping onto Anneal's 4 `trusted/` Primitives + Single-Source `.olean`
  Binding:**
  - *Refinement Direction:*
    `Compiles MirLang X86AsmLang mirToX86NaiveCodec m (naiveCodegen m)`.
  - *`Language` & `SmallStepMachine` Instantiation:* Both `MirLang` and
    `X86AsmLang` instantiate `EventualBehaviorOf` over `MirMachine` and
    `X86Machine` (`trusted/lean/Trusted/X86Semantics.lean`), sharing
    `SemObs := EventualOut IoEvent Unit`. `MirLang.Query := MirEntryState`;
    `X86AsmLang.Query := X86State` (GPRs `rax..r15`, `rip`, `rflags`, flat frame
    memory, and `rsp`).
  - *`BehaviorCodec MirLang X86AsmLang` (`mirToX86NaiveCodec`):*
    `encodeQuery` allocates a fresh stack frame at `rsp`, initializes
    callee-saved registers to canonical values, and writes MIR arguments into
    System V argument registers (`rdi`, `rsi`, `rdx`, `rcx`, `r8`, `r9`) or stack
    slots. `decodeQuery` projects `X86State` back to `MirEntryState` by reading
    argument locations and discarding caller-saved registers (`r10`, `r11`,
    `rflags`), satisfying `decodeQuery (encodeQuery q_mir) = q_mir`.
    `decodeOut : X86AsmLang.Out → Option MirLang.Out` checks that callee-saved
    registers (`rbx`, `rbp`, `r12..r15`) and `rsp` match their entry contract
    and that `rax`/`rdx` hold a valid bit representation of the Rust return type
    (returning `none` if `bool` in `al` is outside `{0, 1}`).
  - *Single-Source `.olean` Binding:* `Trusted.emitX86CrateAsm : String := renderX86Asm (naiveCodegen crateMir)`
    is reduced inside the Lean kernel and cross-checked byte-for-byte against
    the emitted `.s` file by `anneal-audit`.
- **Architectural Stress Tests:**
  - *Stuttering & $1 \to k$ Step Expansion:* Each MIR statement expands into
    $4\text{--}12$ `X86Machine` instructions. Because `EventualBehaviorOf`
    abstracts silent internal steps (`Obs = none`), $1 \to k$ expansion requires
    zero step-dilation parameters in `Language` or `BehaviorCodec`.
  - *Quotienting Dead Scratch State in `Out`:* To satisfy partial injectivity
    `decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`, `X86AsmLang.Out` represents
    the architectural post-call observation (return registers, callee-saved
    registers, `rsp`, and observable heap memory), quotienting dead caller-saved
    scratch registers (`rcx`, `r8..r11`, `rflags`) and popped stack-frame bytes
    below `rsp`.

##### Use Case 2: `VeriISLE` — Declarative Term-Rewriting Instruction Selector (`ISLE` / `VeriISLE`)

- **Role & Problem Solved:** Certifying/verified instruction selector modeled on
  Cranelift's `ISLE` DSL and `VeriISLE`/`Crocus` (`cranelift/isle/veri`). Lowers
  width-polymorphic integer, pointer, bitfield, and vector DAGs (`MachIrLang`)
  via prioritized term-rewrite rules (e.g., `(rule (iadd x (ishl y (iconst k))) (if (uimm2 k)) (x86_lea_scaled x y k))`)
  into `VRegIsaLang`, discharging each rule's bitvector side conditions via
  `bv_decide` in `theory/` and eliminating sign/zero-extension bugs in `x86-64`
  addressing modes, `AArch64` `ADD Xd, Xn, Wm, SXTW #2`, and `RISC-V` `Zba`
  `sh1add`/`sh2add`/`sh3add`.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement Direction:*
    `Compiles MachIrLang VRegIsaLang isleCodec irProg vregProg`.
  - *`Language` & `BehaviorCodec`:* `MachIrLang.Query := VRegEnv × MemState`;
    `VRegIsaLang.Query := VRegEnv × ArchFlags × MemState`;
    `isleCodec.encodeQuery (env, mem) := (env, defaultFlags, mem)` and
    `isleCodec.decodeQuery (env, _, mem) := (env, mem)`.
  - *`VerificationResult` Integration:* User-supplied domain-specific ISLE rules
    (e.g., for custom RISC-V crypto/bitmanip extensions) emit named obligations
    `IsleRuleSoundness::<rule_id>` into `VerificationResult`.
- **Architectural Stress Tests:**
  - *Tree-to-DAG $k \to 1$ Contraction & Trap Ordering:* Contracting `zext_i32_to_i64`
    + `shl_imm` + `add_i64` + `load_i64` into a single `mov rax, [rdi + rsi*4 + 16]`
    collapses 4 silent/memory steps into 1 under `EventualBehaviorOf`, while
    `Compiles` over `Partial` automatically forbids rules that hoist a trapping
    division or load above an earlier guard.

##### Use Case 3: `FlagFusePeephole` — Verified Peephole & Condition-Code Fusion Pass

- **Role & Problem Solved:** Verified peephole and condition-flag dataflow pass
  (extending `Peek`, `Chamois-CompCert postpass`, and Anneal's
  `theory/Anneal/Compiler/Peephole.lean`). Fuses `sub rax, rbx; cmp rax, 0; je L`
  into `sub rax, rbx; je L` on `x86-64`, `add x0, x1, x2; cmp x0, #0; b.eq L`
  into `adds x0, x1, x2; b.eq L` and `and + cbnz` into `tbnz` on `AArch64`, and
  eliminates redundant 32-bit zero-extension moves (`mov eax, eax`) after 32-bit
  ALU writes.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement Direction:*
    `Compiles VRegIsaLang VRegIsaLang (flagLivenessCodec liveOutFlags) srcBlock optBlock`.
  - *`BehaviorCodec`:* `flagLivenessCodec` masks out dead architectural condition
    flags in `Out` according to `liveOutFlags : FlagMask` while preserving all
    live-out flags (`CF`, `ZF`, `SF`, `OF`) consumed by downstream branches or
    `adc`/`sbb` carry chains.
- **Architectural Stress Tests:**
  - *Catching `OF`/`CF` Flag Miscompilations:* Attempting to fuse
    `sub rax, rbx; cmp rax, 0; jl L` into `sub rax, rbx; jl L` fails `Compiles`
    immediately in Lean: `jl` tests `SF ≠ OF`, and after `cmp rax, 0`, `OF = 0`
     always, whereas after `sub rax, rbx`, `OF` reflects signed overflow of
    `rax - rbx`. Similarly, replacing `add eax, 1` with `inc eax` is rejected
    whenever `CF` is in `liveOutFlags` because `inc` preserves `CF`.

##### Use Case 4: `SouperCert` / `MinotaurTV` — Synthesis-Based Superoptimizer with Bitvector/SIMD Certificates

- **Role & Problem Solved:** Pairs untrusted synthesis-based superoptimizers
  (`Souper`, `Minotaur`, `STOKE`, `Slothy`, `Hydra`) with an in-Lean translation
  validation checker (`LRAT` / `bv_decide`) in `theory/`, achieving optimal
  branchless bit-manipulation and SIMD (`pshufb`, `vpternlogd`, `popcnt`,
  `clmul`) code generation with zero TCB footprint for the synthesizer or SAT/SMT
  solver.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement Direction:*
    `Compiles SsaBlockLang SsaBlockLang simdSubregCodec s t`.
  - *Poison Refinement via `Partial` & SIMD Lane Codecs:* Over `Partial`, any
    input triggering shift-amount overflow or poison in `s` has
    `(sem s q).defined = False`, permitting `t` to replace poison-producing
    expressions with total hardware instructions (`shlx`). When lowering 128-bit
    SSE (`xmm0`) onto 256-bit/512-bit AVX (`ymm0`/`zmm0`), `simdSubregCodec.decodeOut`
    verifies that bits `128..511` are zero (matching `VEX` upper-lane zeroing in
    `encodeOut`), satisfying `decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`.

---

### 2. Category B: Register Allocation, Spilling & Stack/ABI Layout (Use Cases 5–7)

`Basis: source + normative + documentation + derived`

#### 2.1 Real-World Tool Family Deep-Dive

1. **`CompCert` Iterated Register Coalescing (`IRC`, `backend/Allocproof.v`,
   `backend/Locations.v`, `backend/Movesproof.v`; Rideau, Serpette, Leroy, POPL
   2008):**
   - *Goals & Lineage:* Translation-validated graph-coloring register allocator
     lowering `RTL` (infinite pseudo-registers) to `LTL` (physical `mreg`s +
     abstract `slot` locations `Local`/`Incoming`/`Outgoing`).
   - *Design Philosophy & Tradeoffs:* Because George-Appel Iterated Register
     Coalescing (IRC) with live-range splitting and spilling is complex to verify
     constructively, `CompCert` implements the graph-coloring heuristics in
     untrusted OCaml (`Regalloc.ml`) and verifies a backward dataflow equations
     checker (`Allocproof.v`) in Coq, followed by Rideau-Serpette-Leroy's
     verified parallel-move sequentialization (`Movesproof.v`, which breaks
     register transfer cycles using a single temporary or swap instructions).
   - *Formal Theory & TCB:* Backward dataflow analysis computing sets of
     equations `reg = loc` required at each CFG point; zero trust in the OCaml
     IRC heuristic search.

2. **`regalloc2` and `regalloc2::checker` (`bytecodealliance/regalloc2`,
   `src/checker.rs`; Chris Fallin):**
   - *Goals & Lineage:* Industrial Rust register allocator for `Cranelift`
     (`Wasmtime` and `rustc_codegen_cranelift`), derived from SpiderMonkey's
     IonMonkey backtracking bundle allocator (`ion`) plus a single-pass fast
     allocator (`fastalloc`).
   - *Design Philosophy & Tradeoffs:* Includes an integrated symbolic dataflow
     equivalence checker (`src/checker.rs`) that tracks abstract values (`CheckerValue`)
     flowing through physical registers and spill slots across CFG basic blocks,
     verifying that every edited instruction stream and parallel-move resolver
     preserves SSA virtual-register dataflow.
   - *Ecosystem Comparison:* Unlike `CompCert Allocproof.v` (which checks a Coq
     AST), `regalloc2::checker` executes at compile/fuzz time in Rust; porting
     `regalloc2::checker` into Lean 4 (`CertRegAlloc2`) converts it into a
     kernel-checked translation validator.

3. **`CakeML reg_alloc` (`compiler/backend/reg_alloc/`, Tan et al., JFP 2019):**
   - *Goals & Lineage:* Constructively verified graph-coloring register allocator
     written directly inside HOL4 (rather than translation-validated), compiling
     annotated clash graphs into total coloring functions with verified spill
     insertion in `word_allocProofScript.sml`.

4. **`CompCert Stacking` (`backend/Stackingproof.v`), Stack-Aware `CompCert`
   (Wang, Wilke, Shao, POPL 2019, DOI `10.1145/3290352`), and Verified Stack
   Bounds (Carbonneaux, Hoffmann, Ramananandro, Shao, PLDI 2014, DOI
   `10.1145/2594291.2594301`):**
   - *Goals & Lineage:* `CompCert`'s standard `Stacking` pass packs `LTL`/`Linear`
     slots into a per-function stack frame block, but standard `CompCert` models
     stack frames as unbounded independent memory blocks. Carbonneaux et al.
     (PLDI 2014) added quantitative stack-bound propagation to `CompCert`
     (`Valex`), and Wang et al. (`Stack-Aware CompCert`, POPL 2019) replaced the
     unbounded block stack with a single finite flat byte array (`stack : mem`)
     bounded by `SINGLE_STACK_SIZE`.

5. **LLVM `StackColoring` (`llvm/lib/CodeGen/StackColoring.cpp`) and Rust Stack
   Clash Protection (`__rust_probestack`, `compiler/rustc_codegen_ssa/src/back/`):**
   - *Goals & Tradeoffs:* `StackColoring` merges stack slots whose
     `LIFETIME_START`..`LIFETIME_END` (`StorageLive`..`StorageDead` in MIR)
     intervals do not overlap using conflict-graph coloring, but has historically
     suffered miscompilations when escaping pointers outlive merged slots.
     `__rust_probestack` (and `-fstack-clash-protection`) touches every 4 KiB
     page when allocating frames $> 4096$ bytes so `rsp` cannot jump across the
     OS guard page into the heap.

6. **Calling Convention Specifications (`CompCert backend/Conventions1.v`,
   `abi-cafe` `Gankra/abi-cafe`, and `Sail`/`Islaris` ABI contracts):**
   - *Goals & Lineage:* `Conventions1.v` formalizes caller/callee-saved registers
     and parameter location sequences (`loc_arguments`, `loc_result`) for C
     types; `abi-cafe` differentially fuzzes C/Rust calling conventions across
     `rustc`, `clang`, `gcc`, and `cg_clif` (exposing `i128` alignment and
     composite splitting bugs); `Islaris` (`rems-project/islaris@c978e10f50`)
     encodes arm64/riscv64 AAPCS64/LP64 calling conventions as separation-logic
     preconditions/postconditions over Sail traces.

---

#### 2.2 Concrete Tool Specifications & Mapping onto Anneal's `trusted/` Primitives (Use Cases 5–7)

##### Use Case 5: `CertRegAlloc2` — Certifying Register Allocator (`regalloc2` + Verified Symbolic Dataflow Equivalence Checker)

- **Role & Problem Solved:** Pairs `regalloc2` (executed as an untrusted external
  oracle) with a linear-time per-block symbolic dataflow equivalence checker
  `checkRegAlloc` in Lean 4 (`theory/Backend/RegAlloc/`). Verifies live-range
  splitting across loop backedges, spill/reload insertion, constant
  rematerialization, coalesced `mov` elimination, and parallel-move cycle
  breaking (`xchg`), discharging:
  `theorem checkRegAlloc_sound : checkRegAlloc vprog pprog cert = true → Compiles VRegMachLang PhysRegMachLang regAllocCodec vprog pprog`.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement Direction:*
    `Compiles VRegMachLang PhysRegMachLang regAllocCodec vprog pprog`.
  - *`BehaviorCodec` (`regAllocCodec`):* `VRegMachLang.Query := VRegInitArgs × AbstractMem`;
    `PhysRegMachLang.Query := PhysRegFile × SpillSlotArray × AbstractMem`.
    `encodeQuery` places entry arguments into physical registers/stack slots per
    `cert.entryMap` and zeros spill slots; `decodeQuery` extracts initial
    virtual-register values from `cert.entryMap`; `decodeOut` reads return
    registers (`rax`, `rdx`, `xmm0`) and verifies that callee-saved registers
    (`rbx`, `rbp`, `r12..r15`) equal their entry values.
- **Architectural Stress Tests:**
  - *Simultaneous $0 \to k$ and $1 \to 0$ Step Elasticity:* At split CFG edges,
    a 0-step edge transition in `VRegMachLang` expands into $k$ physical moves,
    spills, and `xchg` swaps in `PhysRegMachLang` ($0 \to k$), while coalesced
    virtual moves (`mov v2, v1`) collapse into 0 physical instructions ($1 \to 0$).
    `EventualBehaviorOf` absorbs both ratios without stuttering-step padding.
  - *One-to-Many Live-Range Replication:* When a virtual register `v` resides
    simultaneously in physical register `r` and spill slot `s` (avoiding re-spill
    stores), the internal block invariant tracks a location set per `vreg` that
    projects canonically at function boundaries via `regAllocCodec`.

##### Use Case 6: `StackingPacker` — Stack-Frame Packing, Live-Range Slot Sharing & Guard-Page Probing

- **Role & Problem Solved:** Combines `CompCert Stacking`, `LLVM StackColoring`
  over non-overlapping `StorageLive`..`StorageDead` lifetimes, and 4 KiB
  guard-page probing (`__rust_probestack`). Assigns concrete `[rsp + off]` frame
  offsets respecting alignment ($1..64$ bytes), merges disjoint-lifetime locals
  into shared physical byte ranges, and emits page-probing loops for frames
  $> 4096$ bytes.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement & Progress:*
    `Compiles SpillSlotMachLang StackFrameMachLang stackingCodec s t` paired with
    `StackFrameMachLang.ProductiveOn (StackHeadroomPre frameBound) t` and
    `VerificationResult` obligation `StackBound::<fn_name> (maxBytes ≤ budget)`.
- **Architectural Stress Tests:**
  - *Temporal Aliasing of Shared Stack Bytes:* When `_1 : [u8; 64]` and
    `_2 : [u64; 8]` have disjoint `StorageLive`..`StorageDead` intervals and
    share `[rsp + 32 .. rsp + 96]`, any dangling dereference of `&raw _1` after
    `StorageDead(_1)` already triggers UB in `SpillSlotMachLang`
    (`(sem s q).defined = False`), allowing the simulation relation to re-bind
    `[rsp + 32 .. rsp + 96]` to `_2` soundly.

##### Use Case 7: `AbiMarshal` — Multi-Target Foreign Calling-Convention Marshaler (`SysV AMD64`, `AAPCS64`, `RISC-V LP64D`, `Win64`)

- **Role & Problem Solved:** Verified calling-convention lowering pass and FFI
  boundary verifier for `extern "C"`, `extern "system"`, `extern "efiapi"`,
  `extern "win64"`, and `extern "sysv64"` over `#[repr(C)]`, `#[repr(transparent)]`,
  `#[repr(simd)]`, and `i128`/`u128`:
  - *System V AMD64:* Recursive eightbyte classification (`INTEGER`, `SSE`,
    `SSEUP`, `X87`, `MEMORY`) with post-merger rules, hidden `sret` in `rdi`
    returned in `rax`, `al` vector count for variadics, 16-byte `rsp` alignment
    before `call`, and 128-byte leaf red zone `[rsp - 128 .. rsp)`.
  - *AAPCS64:* Homogeneous Floating-Point/Short-Vector Aggregates (`HFA`/`HVA`
    up to 4 elements in `v0..v3`), composites $> 16$ bytes passed by reference,
    indirect result pointer in `x8` (distinct from `x0..x7`!), and 16-byte `sp`
    alignment at all public memory accesses.
  - *RISC-V LP64D:* Hardware FP struct flattening (`{ f32, i32 }` in `fa0` +
    `a0`), $2 \times \text{XLEN}$ register pairs, and composites $> 16$ bytes by
    reference.
  - *Win64:* 4 register slots (`rcx/xmm0..r9/xmm3`), mandatory 32-byte caller
    shadow space, and register passing only for structs of exact size $1, 2, 4,$
    or $8$ bytes.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement & `StepResult.externalCall`:*
    `Compiles RustCallLang PlatformAbiLang abiCodec s t`. At every
    `call extern_symbol` in `PlatformAbiLang`, the machine steps via:
    `StepResult.externalCall (checkAbiPrecondition abiSig state) (postAbiBranches abiSig state)`.
- **Architectural Stress Tests:**
  - *Two-Sided Validation of `StepResult.externalCall`:* Callers must establish
    `checkAbiPrecondition = true` (16-byte `rsp` alignment, initialized ABI
    register/stack slots, disjoint `sret`, and zero live data in the 128-byte
    System V red zone across `call`) or transition to `.failed .ub`, and must
    survive every demonic post-state in `postAbiBranches` (clobbered caller-saved
    registers and red zone, preserved callee-saved registers). Exported Rust
    callees (`#[no_mangle] pub extern "C" fn`) are verified by encoding arbitrary
    valid C caller states via `encodeQuery` and checking `postAbiBranches` in
    `decodeOut`.

---

### 3. Category C: Instruction Scheduling & Pipeline Hazards (Use Cases 8–10)

`Basis: source + documentation + derived`

#### 3.1 Real-World Tool Family Deep-Dive

1. **`Chamois-CompCert BTL` (`gricad-gitlab.univ-grenoble-alpes.fr/certicompil/Chamois-CompCert`,
   Six, Gourdin, Boulmé, Monniaux, Fasse, Nardino, OOPSLA 2020 DOI
   `10.1145/3428208` & CPP 2022 DOI `10.1145/3497775.3503679`):**
   - *Goals & Lineage:* Block Transfer Language (`BTL`) IR and verified symbolic
     execution engine in Coq for defensive translation validation of superblock
     instruction scheduling, load hoisting, if-conversion, and lazy code motion.
   - *Design Philosophy & Tradeoffs:* Rather than proving list-scheduling
     heuristics (critical-path latencies, register-pressure heuristics) directly,
     `BTL` normalizes source and scheduled superblocks into hash-consed symbolic
     execution trees equipped with `Ok` (non-trapping) predicates, checking tree
     inclusion by Coq reflection (`vm_compute`).

2. **`Tristan & Leroy` Scheduler and Modulo Software Pipelining Validators
   (Tristan & Leroy, POPL 2008, DOI `10.1145/1328438.1328460`; Tristan & Leroy,
   PLDI 2010, DOI `10.1145/1806596.1806609`):**
   - *Goals & Lineage:* Pioneered verified translation validation in `CompCert`
     for trace scheduling (POPL 2008) and Swing Modulo Software Pipelining (PLDI
     2010), decomposing a pipelined loop (Prolog + steady-state Kernel + Epilog)
     against an unrolled symbolic execution of the original loop body.

3. **`LLVM MachinePipeliner` (`llvm/lib/CodeGen/MachinePipeliner.cpp`, Swing
   Modulo Scheduling):**
   - *Goals & Tradeoffs:* Production Swing Modulo Scheduler (`SMS`) used on
     Hexagon, PowerPC, RISC-V, and AArch64; overlaps $k$ loop iterations with
     Initiation Interval $II$ and modulo variable expansion, but unverified
     corner cases in epilog drain predicates and short-trip-count ($N < k$)
     peeling are a recurring source of backend miscompilations.

4. **`CompCert-KVX` VLIW Bundle Packer (Six, Boulmé, Monniaux, OOPSLA 2020),
   `CakeML` MIPS Delay-Slot Filler (`compiler/backend/mips/`), and `CerCo`
   (Amadio et al., FMSD 2014, DOI `10.1007/s10703-014-0207-x`):**
   - *Goals & Tradeoffs:* `CompCert-KVX` packs sequential `Mach` instructions
     into parallel VLIW bundles for the Kalray KV3-1 core (up to 8 instructions
     per bundle with simultaneous read-before-write semantics), checking absence
     of intra-bundle resource and WAW/RAW conflicts; `CakeML` verifies branch
     delay-slot filling for MIPS; `CerCo` instruments C code with exact
     cycle-accurate cost annotations verified against a pipelined 8051/ARM
     back-end.

---

#### 3.2 Concrete Tool Specifications & Mapping onto Anneal's `trusted/` Primitives (Use Cases 8–10)

##### Use Case 8: `ChamoisBTL` — Certifying Superblock & Basic-Block List Scheduler (`BTL` Symbolic Simulation)

- **Role & Problem Solved:** Certifying instruction scheduler modeled on
  Chamois-CompCert's `BTL` symbolic simulator. Validates latency-hiding load
  hoisting, store-to-load forwarding, and speculative instruction motion across
  extended basic blocks (superblocks) produced by an untrusted critical-path
  scheduler.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement Direction:*
    `Compiles BtlBlockLang BtlBlockLang btlCodec s t`.
  - *Catching Illegal Speculation via `Partial`:* Executing a `BtlBlock` returns
    a `Partial (BtlExitState → Prop)`. If the scheduler hoists a pure `add` or
    in-bounds stack load `[rsp + 16]` above a branch, both `s` and `t` are
    defined on the same inputs. If it hoists a potentially trapping `udiv r1, r2`
    above `cbz r2, L_exit`, `(sem s q).defined` is `True` when `r2 == 0` whereas
    `(sem t q).defined` is `False` (divide-by-zero trap), refuting
    `t.sem ≤ s.sem` automatically.
- **Architectural Stress Tests:**
  - *Commuting Internal Steps under `EventualBehaviorOf`:* Reordering independent
    ALU and local memory operations changes intermediate register states at every
    cycle while preserving the terminal state and `List Obs` trace at block exit.

##### Use Case 9: `ModuloPipelines` — Modulo Software Pipelining Validator for Inner Loops

- **Role & Problem Solved:** Translation validator for Swing Modulo Scheduled
  inner loops (`Prolog` filling $k$ stages, steady-state `Kernel` executing stage
  $s$ of iteration $i - s$ at Initiation Interval $II$, and `Epilog` draining the
  pipeline), checking inductive schedule mappings
  $\sigma(i, \text{instr}) = i \cdot II + \text{cycle}(\text{instr})$ and short
  trip-count ($N < k$) guards.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement Direction:*
    `Compiles LoopIsaLang LoopIsaLang idCodec loopSrc loopOpt`.
- **Architectural Stress Tests:**
  - *Cross-Iteration Commutation in `EventualBehaviorOf`:* In `loopOpt`, a
    non-aliasing local load of iteration $i + 1$ executes before the store of
    iteration $i$. Because non-volatile local memory reads emit no external `Obs`
    in `EventualBehaviorOf`, the external `List Obs` trace remains identical and
    the state converges upon epilog completion.

##### Use Case 10: `BundleHazardPacker` — VLIW Bundle Packer, Delay-Slot Filler & Pipeline Hazard Checker

- **Role & Problem Solved:** Verified post-pass bundle packer and hazard checker
  for VLIW multi-issue packets (`{ I₀ || I₁ || I₂ || I₃ }` with simultaneous
  pre-bundle read semantics) and MIPS/SPARC branch delay slots.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement & Obligations:*
    `Compiles SeqIsaLang BundledIsaLang bundleCodec s t` plus `VerificationResult`
    obligations (`NoDoubleWriteInBundle`, `LatencyInterlockSatisfied`,
    `DelaySlotNoBranchInSlot`).
- **Architectural Stress Tests:**
  - *Sequential vs. Simultaneous Step Semantics in `SmallStepMachine`:*
    `SeqIsaLang` steps one instruction at a time; `BundledIsaLang` evaluates all
    bundle operands in the pre-bundle state $\Sigma$ and commits all writes
    simultaneously (stepping to `.failed .ub` on double writes). Packing
    `add r1, r2, r3; sub r4, r1, r5` into `{ add r1, r2, r3 || sub r4, r1, r5 }`
    is immediately rejected by `Compiles` (RAW hazard reads stale `r1`), whereas
    parallel register swap `{ mov r1, r2 || mov r2, r1 }` refines a sequential
    3-move temporary swap.

---

### 4. Category D: Assemblers, Encoders, Linkers & Post-Link Optimizers (Use Cases 11–14)

`Basis: source + normative + documentation + derived`

#### 4.1 Real-World Tool Family Deep-Dive

1. **Verified Assemblers and Instruction Encoders/Decoders (`Coqbin` /
   `CompCertAssembler`, `CakeML lab_to_target` & `L3`, `riscv-coq`/`Bedrock2`,
   `RockSalt`/`x86model`, `LNSym`):**
   - **`Coqbin` / `CompCertAssembler` (Kennedy, Benton, Jensen, Dagand, PPDP
     2013, DOI `10.1145/2505879.2505897`; Wu, Wang, Cai, Shao, POPL 2016):**
     Verified x86-32/x86-64 assemblers in Coq proving round-trip encode/decode
     bijections (`decode (encode i) = Some i`) and variable-length branch
     displacement relaxation.
   - **`CakeML lab_to_target` (`compiler/backend/lab_to_targetProofScript.sml`)
     and `L3` (Anthony Fox, ITP 2015):** Resolves symbolic labels into concrete
     byte offsets via iterative jump-width relaxation and encodes instructions
     through HOL4 bitvector models exported from `L3`.
   - **`riscv-coq` / `Bedrock2` (`mit-plv/riscv-coq`, `mit-plv/bedrock2`,
     Erbsen et al., PLDI 2019; `opencompl/riscv-lean@7c6b500c17`):** Spec-driven
     RISC-V instruction encoders, decoders, and flat-memory transition systems.
   - **`RockSalt` / `x86model` (Morrisett, Tan, Tassarotti, Tristan, Gan, PLDI
     2012, DOI `10.1145/2254064.2254111`) and `LNSym`
     (`leanprover/LNSym@5c05220ff9`):** `x86model` formalizes x86 prefix/ModR/M/SIB
     decoding in Coq via parser combinators; `LNSym` formalizes ARMv8-A 32-bit
     instruction decoding and symbolic simulation in Lean 4 from ARM ASL.

2. **Verified Linkers and ELF Relocation Semantics (`CompCertELF`, `linksem`,
   `mold`/`lld`/`wild`):**
   - **`CompCertELF` (Wang, Xu, Wilke, Shao, PLDI 2020, DOI
     `10.1145/3385412.3385989`):** Extends `CompCert` all the way to relocatable
     ELF `.o` files and verified static linking into an executable ELF image
     with concrete section layout and relocation patching (`R_X86_64_*`).
   - **`linksem` (Kell, Mulligan, Sewell, OOPSLA 2016, DOI
     `10.1145/2983990.2983996`):** Executable Lem/HOL4/Isabelle specification of
     System V ELF static linking, symbol resolution rules (strong/weak/COMMON),
     and AMD64/AArch64 relocations (`R_X86_64_GOTPCRELX`, veneer insertion).
   - **Production Linkers (`ld.lld`, `mold` `rui314/mold`, `wild`
     `davidlattimore/wild`):** High-speed parallel linkers performing post-codegen
     code relaxations (`R_X86_64_GOTPCRELX` indirect `mov` to `lea`, RISC-V
     `R_RISCV_RELAX` 8-byte `auipc+jalr` to 4-byte `jal` or 2-byte `c.jal` with
     byte deletion) that alter instruction bytes after compilation.

3. **Compositional and Multi-Language Linking Frameworks (`SepCompCert`,
   `CompCertM`, `CompCertO`, `DimSum`):**
   - **`SepCompCert` (Kang, Kim, Hur, Dreyer, Viktorov, POPL 2016, DOI
     `10.1145/2837614.2837642`):** Lightweight separate compilation for syntactic
     pass pipelines.
   - **`CompCertM` (Song, Cho, Kim, Kang, Hur, POPL 2020, DOI
     `10.1145/3371083`):** Multi-language C + assembly linking via Refinement
     Under Self-related Contexts (RUSC) and mixed-simulation diagrams.
   - **`CompCertO` (Koenig, Shao, PLDI 2021, DOI `10.1145/3453483.3454097`):**
     Game-semantics-inspired open transition systems parameterized by calling
     convention simulation conventions ($\mathbb{R}_A \twoheadrightarrow \mathbb{R}_B$).
   - **`DimSum` (Sammler, Spies, Song, D'Osualdo, Krebbers, Garg, Dreyer, POPL
     2023, DOI `10.1145/3571219`):** Decentralized event-based multi-language
     linking in Coq/Iris where modules written in high-level, C-like, and
     assembly languages compose horizontally through shared external event
     traces and angelic/demonic wrappers.

4. **Post-Link Profile-Guided Optimizers and Binary Recompilers (`LLVM BOLT`,
   `Google Propeller`, `Egalito`, `BinRec`):**
   - **`LLVM BOLT` (Panchenko et al., CGO 2019, DOI
     `10.1109/CGO.2019.8661201`) and `Google Propeller` (Shen et al., ASPLOS
     2023, DOI `10.1145/3575693.3575727`):** Reorder basic blocks, split cold
     blocks into `.text.cold`, invert conditional branches, and fold tail calls
     using hardware LBR profiles (`BOLT` via post-link disassembly; `Propeller`
     via compiler-emitted basic-block sections and relinking).
   - **`Egalito` (Williams-King et al., ASPLOS 2020, DOI
     `10.1145/3373376.3378522`) and `BinRec` (Altinay et al., EuroSys 2020, DOI
     `10.1145/3342195.3387550`):** Layout-agnostic binary lifting and
     recompilation frameworks.

---

#### 4.2 Concrete Tool Specifications & Mapping onto Anneal's `trusted/` Primitives (Use Cases 11–14)

##### Use Case 11: `BijectiveCodecIsa` — Verified Bidirectional Machine-Code Encoder/Decoder & Branch Relaxation (`x86-64`, `AArch64`, `RV64GC`)

- **Role & Problem Solved:** Verified assembler, instruction encoder/decoder,
  and branch-displacement relaxation pass bridging symbolic assembly ASTs
  (`SymbolicAsmLang`) and flat machine-code bytes (`MachineBytesLang`). Widens
  short 8-bit jumps (`jmp rel8`, `jcc rel8`, RISC-V `RVC` `c.beqz`/`c.j`,
  AArch64 `tbz`/`cbz`) to 32-bit near jumps or veneers and proves round-trip
  decoding `∀ i, decodeInstr (encodeInstr i) = some (canonicalizeInstr i, (encodeInstr i).size)`,
  covering `x86-64` `REX`/`VEX`/`EVEX`, `ModR/M`, `SIB` (including the mandatory
  `[rsp]` `SIB` escape byte `0x24` and `[rbp]` `disp8=0` encoding rule), and
  next-instruction `RIP`-relative displacements (`rip_next = rip_curr + len`).
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement Direction:*
    `Compiles SymbolicAsmLang MachineBytesLang asmBytesCodec asmProg bytes`.
  - *Fetch-Decode-Execute in `SmallStepMachine`:* `MachineBytesLang` fetches
    $1..15$ bytes from `.text` at `rip : UInt64`, runs `decodeInstr`, advances
    `rip := rip + instrLen`, and executes the decoded instruction transition.
    `asmBytesCodec.encodeQuery` maps abstract `(fnId, 0)` entry points to
    `baseAddr + symOffset(fnId)`.
- **Architectural Stress Tests:**
  - *Instruction-Length-Dependent `RIP` Displacements:* Widening a single
    `jcc rel8` (2B) to `jcc rel32` (6B) shifts all downstream label addresses by
    $+4$ bytes. Proving `Compiles` after the relaxation fixpoint verifies that
    every encoded `disp32`/`rel8` matches the final byte layout.

##### Use Case 12: `AnnealLinkELF` — Verified ELF / Mach-O / PE Relocation Engine & Static Linker (`CompCertELF`)

- **Role & Problem Solved:** Verified object-file relocation engine and static
  linker resolving `.symtab` symbols, merging `.text`/`.rodata`/`.data`/`.bss`
  sections, synthesizing `.got`/`.plt` stubs, and applying architecture
  relocations (`x86-64` `R_X86_64_64`, `R_X86_64_PC32`/`PLT32` with 32-bit
  signed overflow checks, `R_X86_64_GOTPCRELX` `mov`-to-`lea` relaxation;
  `AArch64` `R_AARCH64_ADR_PREL_PG_HI21`, `R_AARCH64_CALL26` $\pm 128\text{ MiB}$
  veneers; `RISC-V` paired `R_RISCV_PCREL_HI20` + `R_RISCV_PCREL_LO12_I` and
  `R_RISCV_RELAX`).
- **Mapping onto Anneal's 4 `trusted/` Primitives + Single-Source `.olean`
  Binding:**
  - *Refinement & Obligations:*
    `Compiles RelocObjectLang LinkedImageLang elfLinkCodec objs linkedImg` plus
    `VerificationResult` obligations (`RelocInRange::<sym>`,
    `NoDuplicateStrongSymbol`, `SectionNoOverlap`).
  - *Single-Source `.olean` Binding:* `Trusted.emitCrateElfBytes : ByteArray` is
    bound in the `.olean` environment and verified by `anneal-audit` against the
    on-disk ELF binary.
- **Architectural Stress Tests:**
  - *Block-to-Flat Memory Injection without Hardware Guard Pages:* In
    `RelocObjectLang`, stepping out of bounds of global `A` triggers UB
    (`(sem s q).defined = False`). In `LinkedImageLang`, stepping past `A` lands
    in adjacent global `B`. Because `Partial` ordering allows any target behavior
    when the source is undefined (`defined = False`), flat-memory global
    adjacency after linking satisfies `Compiles` without requiring guard pages
    between globals.

##### Use Case 13: `DimSumLink` — Compositional Cross-Module & Cross-Language Linking (`CompCertO` / `DimSum`)

- **Role & Problem Solved:** Compositional horizontal and vertical linking engine
  for heterogeneous crates linking verified Rust (`MirLang`), verified C
  (`ClightLang`), and handwritten assembly (`X86AsmLang`) modules $M_1, M_2, M_3$
  compiled independently to $T_1, T_2, T_3 \in \text{RelocObjectLang}$.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Shared `SemObs` Spine & `StepResult.externalCall` Discharge:* All three
    source languages have distinct `Query` and `Out` types but share
    `SemObs := EventualOut ExternalIoObs Unit` via `obs_decodeOut`. When caller
    module $M_1$ invokes `f` via `StepResult.externalCall pre_f post_f`, the
    horizontal linking theorem in `theory/` replaces the demonic
    `.choice .demonic post_f` step in $M_1$ with callee $M_2$'s execution,
    using $M_2$'s `ProductiveOn pre_f` + `post_f` proof to discharge the open
    call assumption.
- **Architectural Stress Tests:**
  - *Reentrant Callbacks ($M_1 \to M_2 \to M_1$) & Private Heap Framing:* Framing
    private module memory blocks inside `StepResult.externalCall`'s `branches`
    postcondition preserves caller invariants across reentrant C-to-Rust
    callbacks without altering `SmallStepMachine`.

##### Use Case 14: `BoltPropellerTV` — Post-Link Profile-Guided Binary Optimizer Validator (`BOLT` / `Propeller`)

- **Role & Problem Solved:** Binary-to-binary translation validator for post-link
  optimizers (`LLVM BOLT` and Google `Propeller`) performing hot/cold basic-block
  reordering, `.text.cold` splitting, branch condition inversion
  (`je L_t; jmp L_f` $\leftrightarrow$ `jne L_f; jmp L_t`), and tail-call
  duplication.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement Direction:*
    `Compiles LinkedElfLang LinkedElfLang boltCodec binOrig binBolt`, where
    `boltCodec` translates entry PCs via `bbMap : VAddr → VAddr`.
- **Architectural Stress Tests:**
  - *Fallthrough vs. Explicit Jump Elasticity ($0 \leftrightarrow 1$ Steps):*
    Moving a cold fallthrough block out of line to `.text.cold` turns a
    0-instruction fallthrough into a 1-instruction `jmp` (and inverts a taken
    `jcc` into a 0-step fallthrough), which `EventualBehaviorOf` absorbs with
    zero change to `SemObs`.

---

### 5. Category E: Translation Validators for Unverified Compilers (Use Cases 15–16)

`Basis: source + documentation + derived`

#### 5.1 Real-World Tool Family Deep-Dive

1. **`seL4 GraphRefine` (`seL4/graph-refine@94c93d18830d680fc6732d21fb16ca58ebca9dc5`;
   Sewell, Myreen, Klein, PLDI 2013, DOI `10.1145/2491956.2462183`):**
   - *Goals & Lineage:* Translation validator verifying the compiled ARM/RISC-V/x86-64
     binary of the seL4 microkernel (`gcc -O2`) against its C specification in
     Isabelle/HOL without trusting `gcc`.
   - *Design Philosophy & Tradeoffs:* Decompiles both C (`c-to-graph`) and
     compiled machine code (`asm-to-graph`, using Cambridge HOL4/L3 ISA models)
     into a common loop-cut-point representation **`GraphLang`**, scalarizes
     in-bounds stack spills (`stack_logic.py`), and discharges loop-free path
     equivalence obligations via SMT solvers (`Z3`/`CVC4` with proof
     reconstruction or trusted oracle in the binary TV step).

2. **`Alive2` (`AliveToolkit/alive2@adacbd5180ccf95075e9867c4f0c259f59c9fef2`,
   v21.0; Lopes, Lee, Hur, Liu,uno, Regehr, PLDI 2021, DOI
   `10.1145/3453483.3454030`):**
   - *Goals & Lineage:* Bounded SMT translation validator for LLVM IR passes and
     backend target-lowering (`alive-tv`), modeling `poison`, `undef`, `freeze`,
     byte-level memory (`Pointer` provenance, `noalias`, `align`), and two-step
     refinement (`src ⊑ tgt`).

3. **`Tristan-Govereau-Morrisett` (PLDI 2011, DOI `10.1145/1993498.1993533`),
   `Necula TV` (Necula, PLDI 2000, DOI `10.1145/349299.349314`), and `LNSym`
   (`leanprover/LNSym@5c05220ff970e3bdd7813ad0c9ef3741522c8b92`):**
   - *Goals & Lineage:* Necula (PLDI 2000) introduced structure-preserving
     simulation relations for `gcc -O2`; Tristan-Govereau-Morrisett (PLDI 2011)
     introduced Equality Saturation (`PEG`s) for LLVM intra-procedural TV;
     `LNSym` verifies cryptographic C/assembly equivalence against ARMv8-A
     semantics in Lean 4 via symbolic execution and `bv_decide`.

---

#### 5.2 Concrete Tool Specifications & Mapping onto Anneal's `trusted/` Primitives (Use Cases 15–16)

##### Use Case 15: `LlvmO3Validator` — Per-Function Symbolic Translation Validator for `rustc + LLVM -O3`

- **Role & Problem Solved:** Certifying binary/assembly translation validator
  (combining `seL4 GraphRefine`, `Alive2`, and `AnLLVM`
  `anllvm-verified-llvm-lowering-tree-borrows-noalias-and-binary-tv-2026`) that
  verifies the actual `.o` machine code emitted by `rustc -C opt-level=3`
  against Anneal's captured `Runtime(PostCleanup)` MIR, removing LLVM from
  Anneal's TCB while retaining full `-O3` performance.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement & `ProductiveOn` Composition:*
    `Compiles MirLang X86MachineLang mirToX86Codec mirFn x86Fn`. Because
    `Compiles` is defined over `Partial`, any state `q` where `MirLang` triggers
    UB (arithmetic overflow, out-of-bounds projection, or Tree Borrows aliasing
    violation) has `(MirLang.sem mirFn q).defined = False`, licensing `-O3`
    optimizations that exploit UB-freedom (`noalias` load forwarding, dead
    bounds-check elimination). Composing with the frontend proof
    `MirLang.ProductiveOn Pre mirFn` yields unconditional machine-code safety:
    `X86MachineLang.ProductiveOn (mirToX86Codec.encodePre Pre) x86Fn`.
  - *`VerificationResult` Cut-Point Granularity:* Any path or complex
    auto-vectorized loop whose relational invariant cannot be discharged
    automatically by `bv_decide`/LRAT surfaces as a named `Obligation` in
    `VerificationResult`.
- **Architectural Stress Tests:**
  - *Provenance-Erasing Pointer-to-Integer Lowering across `BehaviorCodec`:*
    `MirLang` pointers carry `(AllocId, BorrowTag)` provenance, whereas
    `X86MachineLang` registers hold raw `UInt64`. `mirToX86Codec.encodeQuery`
    maps each initial `AllocId` to its concrete base virtual address in
    `X86State` (inverted by `decodeQuery`), while `SemObs := EventualOut IoEvent Unit`
    erases internal pointer provenance from observable syscall/MMIO byte events
    so `obs_decodeOut` holds strictly.

##### Use Case 16: `CraneliftValidator` — Fast Symbolic Translation Validator for `rustc_codegen_cranelift` & `GCC`

- **Role & Problem Solved:** Lightweight, millisecond-scale per-basic-block
  translation validator specialized for structure-preserving backends such as
  `rustc_codegen_cranelift` (`cg_clif`) and `rustc_codegen_gcc` (`-O0`/`-O1`/`-Og`),
  which preserve 1-to-1 basic-block CFG structure with MIR while applying `ISLE`
  instruction selection, e-graph GVN, and `regalloc2`.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement & Incremental `VerificationResult` Obligations:*
    `Compiles MirLang X86MachineLang clifCodec mirFn clifFn`, decomposing each
    MIR basic block `bb_0 .. bb_N` into an independent, parallelizable
    `Obligation` (`ClifBlockSim::<fn>::<bb_i>`) in `VerificationResult`.

---

### 6. Category F: Binary Lifters, Decompilers & Inline-Asm Bridges (Use Cases 17–19)

`Basis: source + normative + documentation + derived`

#### 6.1 Real-World Tool Family Deep-Dive

1. **`TInA` and `RUSTInA` (Recoules, Bardin, Bonichon, Mounier, Potet, ESEC/FSE
   2019 DOI `10.1145/3338906.3338962` & ICSE/ISSTA 2021 DOI
   `10.1145/3293883.3295709`):**
   - *Goals & Lineage:* Verification-oriented inline-assembly lifters developed
     at CEA LIST (`BINSEC`). `TInA` lifts GCC extended `asm` blocks into
     equivalent C code for Frama-C; `RUSTInA` audits inline assembly blocks for
     compliance with declared register, memory, flag-clobber, and early-clobber
     (`&` / `lateout`) interface contracts.

2. **`Islaris` (`rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`,
   Sammler et al., PLDI 2022, DOI `10.1145/3519939.3523434`), `Vale`
   (`project-everest/vale@bbae0eb891`), and `Jasmin`
   (`jasmin-lang/jasmin@34f15840f1`):**
   - *Goals & Tradeoffs:* `Islaris` lifts authoritative `Sail` (`ARMv8-A`/`RISC-V`)
     per-instruction SMT symbolic execution traces (`Isla`) into Coq/Iris
     separation logic (`isla-lang`); `Vale` verifies annotated structured
     assembly in F*/Dafny/Lean; `Jasmin` compiles a high-assurance
      assembly-in-the-large language to x86-64/ARM64 with Coq proofs of
     functional correctness and constant-time safety (`EasyCrypt`).

3. **Cambridge Decompilation into Logic (Myreen, Gordon, Slind, POPL 2008 /
   PLDI 2010, DOI `10.1145/1806596.1806610`), `seL4 GraphLang`, and `HolBA`/`BIR`
   (Lindner, Guanciale, Dam, SEFM 2019):**
   - *Goals & Lineage:* Myreen's *Decompilation into Logic* translates raw
     machine-code bytes (`ARM`, `x86-64`, `PowerPC`, `RISC-V`) into tail-recursive
     functions in HOL4 together with a machine-checked certificate theorem
     proving that the extracted function describes the exact transition behavior
     of the binary; `HolBA` lifts binaries into the Binary Intermediate
     Representation (`BIR`) inside HOL4 with certifying lifters.

4. **`FoxDec` (`ssrg-vt/FoxDec`, Verbeek, Bockenek, Ravindran, CCS / ACM TOPS
   2022–2024) and Unverified Binary Lifters (`Remill`, `McSema`, `revng`):**
   - *Goals & Comparison:* `Remill`/`McSema` (`lifting-bits`) and `revng` lift
     x86-64/ARM binaries to LLVM IR using heuristic stack-frame and control-flow
     recovery without formal proofs. By contrast, `FoxDec` uses Isabelle/HOL
     abstract interpretation to infer provably sound control-flow graphs,
     pointer-separation invariants, and recompilable C/IR abstractions from
     stripped production `x86-64` binaries.

---

#### 6.2 Concrete Tool Specifications & Mapping onto Anneal's `trusted/` Primitives (Use Cases 17–19)

##### Use Case 17: `InlineAsmSimdLifter` — `core::arch::asm!` & SIMD Intrinsic Lifter into `MirLang`

- **Role & Problem Solved:** Verified lifter bridging `core::arch::asm!`,
  `core::arch::global_asm!`, and vendor SIMD intrinsics (`core::arch::x86_64::*`,
  `core::arch::aarch64::*`, `core::arch::riscv64::*`) into `MirLang` (cross-referencing
  `anneal-isa-integration-architecture-and-roadmap-synthesis-2026`). Decodes
  inline-asm templates via `BijectiveCodecIsa` and verifies adherence to declared
  `options(nostack, preserves_flags, pure, readonly, nomem, noreturn)` and
  operand constraints (`in(reg)`, `out(reg)`, `inout(reg)`, `lateout(reg)`,
  `clobber_abi("C")`).
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Refinement Direction:*
    `Abstracts MirLiftedLang TargetAsmBlockLang asmBridgeCodec liftedMir rawAsmBlock`
    plus `VerificationResult` obligations (`InlineAsmOptionsValid::<loc>`,
    `InlineAsmNoUndefClobber::<loc>`).
  - *Demonic Register Assignment in `SmallStepMachine`:* Under The Rust
    Reference (`[asm.register-operands]`, `rust-lang/reference@82da570baf`),
    `out(reg)` is guaranteed disjoint from `in(reg)` registers, whereas
    `lateout(reg)` may alias any `in(reg)` register. `MirLiftedLang` models the
    compiler's physical register assignment via **demonic choice**
    (`.choice .demonic`) over all physical register mappings permitted by the
    constraint set. If an early-clobbered output is mistakenly marked
    `lateout(reg)`, the demonic branch that aliases `lateout(reg)` with `in(reg)`
    corrupts the input and refutes the user's proof with an explicit register
    collision counterexample.

##### Use Case 18: `GraphLangBinaryLifter` — Verified Binary-to-SSA Lifter (`seL4 GraphLang` / `HolBA` Style)

- **Role & Problem Solved:** Certifying binary-to-IR lifter that lifts compiled
  ELF/Mach-O binaries (`ElfBinaryLang`) upward into a typed SSA CFG
  (`SsaGraphLang`) so users can verify safety and functional properties on
  `SsaGraphLang` and transfer them down to the raw machine bytes.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Upward Abstraction Direction:*
    `Abstracts SsaGraphLang ElfBinaryLang lifterCodec graph bin`
    (`ElfBinaryLang.sem bin ≤ lifterCodec.toMorphism (SsaGraphLang.sem graph)`).
- **Architectural Stress Tests:**
  - *Deferred Indirect-Jump Resolution via `Partial` Top ($\top$):* Resolving a
    switch-table jump `jmp [table + rax*8]` requires knowing `rax < N`, which
    depends on high-level dataflow invariants. In `SsaGraphLang`, the lifter
    emits `if rax < N then switch(rax) else .failed .ub`. Wherever `rax ≥ N`,
    `(SsaGraphLang.sem graph q).defined = False` ($\top$), so `Abstracts` holds
    trivially during lifting, and the obligation to prove `rax < N` is deferred
    cleanly to `SsaGraphLang.ProductiveOn Pre graph`.

##### Use Case 19: `VerifiedDecompiler` — Certifying Binary Decompiler & Control-Flow Structuralizer (`FoxDec` / `McSema` Style)

- **Role & Problem Solved:** Lifts raw machine binaries (`ElfBinaryLang`) to
  structured high-level control flow (`StructuredHirLang` with typed stack
  variables, non-aliasing local frames, and `while`/`if`/`match` blocks).
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Upward Abstraction & Obligations:*
    `Abstracts StructuredHirLang ElfBinaryLang decompCodec hir bin`, surfacing
    every implicit decompiler assumption (`ReturnAddrUnmodified::<fn>`,
    `StackFrameSeparation::<fn>`, `CallingConvAdherence::<fn>`) as a first-class
    `Obligation` in `VerificationResult`.

---

### 7. Category G: Sandboxing Compilers, Bytecode Verifiers & JITs (Use Cases 20–22)

`Basis: source + normative + documentation + derived`

#### 7.1 Real-World Tool Family Deep-Dive

1. **WebAssembly and SFI Sandboxing Verifiers/Compilers (`VeriWasm`, `vWasm`,
   `RockSalt`, `ARMor`, `WasmCert`/`veRA`):**
   - **`VeriWasm` (Johnson, Thien, Alharthi,ow, Narayan, Brown, Stefan,
     Lerner, NDSS 2021, DOI `10.14722/ndss.2021.24296`):** Offline abstract
     interpretation verifier (with Coq soundness proof) checking that native
     `x86-64` binaries compiled from Wasm (`Lucet`/`Cranelift`) never read,
     write, or jump outside the SFI linear-memory and stack sandbox.
   - **`vWasm` (Bosamiya, Lim, Parno, USENIX Security 2022):** Formally verified
     provably-safe Wasm-to-x86-64 sandboxing compiler written in F* (`rWasm`
     adds a verified Rust backend).
   - **`RockSalt` (Morrisett et al., PLDI 2012, DOI `10.1145/2254064.2254111`)
     and `ARMor` (Zhao, Laubner, Regehr, OOPSLA 2011, DOI
     `10.1145/2048066.2048105`):** Coq/HOL-verified Software Fault Isolation
     binary checkers for Google Native Client (`NaCl` x86) and ARM code.
   - **`WasmCert` (`WasmCert/WasmCert-Coq@58a3d3f8b7`,
     `WasmCert/WasmCert-Isabelle@d9b4659c8b`; Watt, POPL 2018) and `veRA`
     (Brown, Stefan, Lerner, POPL 2020):** Mechanized Wasm semantics and SMT
     verification of JIT range-analysis bounds-check elimination passes.

2. **eBPF Bytecode Verifiers, Abstract Domains & Verified JITs (`PREVAIL`,
   `Agni`, `Jitterbug`, `CertrBPF`):**
   - **`PREVAIL` (`vbpf/prevail@cefe6a799f8b8f37aa2560e196f223802717c1e7`,
     Gershuni et al., PLDI 2019, DOI `10.1145/3314221.3314590`):** Polynomial-time
     eBPF bytecode verifier using the Zone abstract domain (`Crab`) used in
     Windows eBPF.
   - **`Agni` (Vishwanathan, Shacham, Narayana, Nagarakatte, CAV/PACMPL 2022–2023,
     DOI `10.1145/3591280`):** SMT verification of the Linux kernel eBPF
     verifier's tristate-number (`tnum`) and signed/unsigned 32/64-bit interval
     abstract operators (`torvalds/linux@0fcb05b723`).
   - **`Jitterbug` (`uw-unsat/jitterbug@78d1e75ad506498b585fbac66985ff9d9d05952d`,
     Nelson, Jacob, Bornholt, Wang, OSDI 2020) and `CertrBPF`
     (`future-proof-iot/CertFC@75690097c9`, Yuan et al., CAV 2022):**
     `Jitterbug` verifies Linux kernel eBPF-to-native (`RV64`, `RV32`, `ARM32`,
     `ARM64`, `x86-64`) JIT compilers in Rosette/Serval; `CertrBPF` verifies an
     in-kernel eBPF interpreter and JIT in Coq (`CompCert`).

3. **GPU Compute Shader Verifiers and Translators (`GPUVerify`, `Faial`,
   `Naga`/`Tint`/`spirv-val`):**
   - **`GPUVerify` (Betts, Chong, Donaldson, Qadeer, Thomson, OOPSLA 2012, DOI
     `10.1145/2384616.2384625`) and `Faial` (Cogumbreiro, Lange, Liew, Zicarelli,
     CAV 2021, DOI `10.1007/978-3-030-81685-8_11`):** Prove barrier convergence
     (uniformity) and shared-memory data-race freedom in SIMT GPU kernels
     (`GPUVerify` via two-thread predicated lockstep reduction; `Faial` via
     memory access protocols).
   - **`Naga` (`gfx-rs/wgpu/naga`), `Tint` (Chromium `Dawn`), and `spirv-val`
     (`KhronosGroup/SPIRV-Tools`):** Industrial WebGPU (`WGSL`) and Vulkan
     (`SPIR-V`) validators and shader compilers enforcing structured control-flow
     uniformity and robustness bounds clamping.

---

#### 7.2 Concrete Tool Specifications & Mapping onto Anneal's `trusted/` Primitives (Use Cases 20–22)

##### Use Case 20: `WasmSfiSandbox` — Certifying WebAssembly-to-Native & SFI Sandboxing Compiler (`Wasmtime` / `VeriWasm` Style)

- **Role & Problem Solved:** Verified Wasm-to-native (`X86MachineLang` /
  `AArch64MachineLang`) compiler and SFI verifier certifying **two orthogonal
  theorems**:
  1. *Theorem A (Semantics Preservation for Valid Wasm):*
     `Compiles WasmLang X86MachineLang wasmCodec w (compileWasmSfi w)`.
  2. *Theorem B (Unconditional Target Sandbox Safety for Arbitrary/Adversarial
     Input):*
     `∀ (u : UntrustedWasmModule), X86SandboxedLang.ProductiveOn (HostSandboxPre sandboxBounds) (compileWasmSfi u)`.
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Why Target-Level `ProductiveOn` Is Essential for Sandboxing:* `Compiles`
    alone guarantees target refinement only when the source module `u` has no
    source-level UB. Stating SFI containment directly as
    `X86SandboxedLang.ProductiveOn (HostSandboxPre bounds) (compileWasmSfi u)`
    (where any memory access outside `[r15 .. r15 + 4GiB + guard)` or write to
    pinned host register `r15` steps to `.failed .ub` in `X86SandboxedLang`)
    certifies unconditional hardware containment on arbitrary untrusted inputs
    via 32-bit zero-extension masking (`mov eax, eax; [r15 + rax + disp]`).

##### Use Case 21: `EbpfJitterbug` — Verified Linux eBPF Bytecode Verifier & Native JIT Compiler (`PREVAIL` / `Jitterbug`)

- **Role & Problem Solved:** End-to-end verified eBPF verification and native
  JIT pipeline combining a sound Zone + `tnum` abstract interpreter
  (`EbpfAbsLang`) with a verified native JIT compiler (`KernelIsaLang`).
- **Mapping onto Anneal's 4 `trusted/` Primitives (The Verification Triangle):**
  1. `Abstracts EbpfAbsLang EbpfBytecodeLang ebpfAbsCodec absCert bpfProg`
     validates the `PREVAIL`/`Agni` abstract fixpoint.
  2. `EbpfBytecodeLang.ProductiveOn ValidEbpfCtxPre bpfProg` proves the bytecode
     never faults or diverges.
  3. `StepResult.externalCall` models BPF helper calls (`bpf_map_lookup_elem`)
     with pointer/nullability preconditions (`boundaryInv`) and range postconditions
     (`branches`).
  4. `Compiles EbpfBytecodeLang KernelIsaLang ebpfJitCodec bpfProg (jitCompile bpfProg)`
     transfers `ProductiveOn` down to the native kernel machine code:
     `KernelIsaLang.ProductiveOn (ebpfJitCodec.encodePre ValidEbpfCtxPre) (jitCompile bpfProg)`.

##### Use Case 22: `GpuShaderGuardian` — Verified GPU Compute Shader Bounds, Uniformity & SIMT Compiler (`SPIR-V` / `WGSL` → `AMDGPU` / `PTX`)

- **Role & Problem Solved:** Verified SIMT shader verifier and backend compiler
  checking subgroup barrier uniformity (`UniformBarrier::<id>`), descriptor
  buffer bounds (`StorageBufferInBounds::<id>`), workgroup shared-memory race
  freedom (`WorkgroupSharedRaceFree::<id>`), and structured-CFG-to-exec-mask
  lowering (`OpSelectionMerge`/`OpLoopMerge` $\to$ `s_and_saveexec_b64` /
  `s_or_b64 exec`).
- **Mapping onto Anneal's 4 `trusted/` Primitives:**
  - *Lockstep Wavefront `SmallStepMachine`:* `AmdgpuWavefrontLang` instantiates
    `SmallStepMachine` with scalar registers (`sgpr0..102`), 64-lane vector
    registers (`vgpr0..255 : Fin 64 → UInt32`), and active lane mask
    `exec : UInt64`. A workgroup barrier checks `boundaryInv := (exec == fullSubgroupMask)`
    and steps to `.failed .ub` on divergent lane masks, enabling `Compiles` +
    `ProductiveOn` to certify GPU deadlock freedom with zero changes to
    `trusted/`.

---

### 8. Cross-Cutting Synthesis: Architectural Laws & Primitive Stress-Test Matrix

`Basis: derived + source`

| Primitive / Mechanism | Sub-Domain 4 Stress Tests (Use Cases 1–22) | Architectural Law & Design Resolution in `theory/` |
| :--- | :--- | :--- |
| **`Language SemObs` + `BehaviorCodec L₁ L₂`** | • Caller-saved scratch registers (`r10`, `r11`, `rflags`) & popped stack bytes (`NaiveCodegen`, `FlagFusePeephole`)<br>• Upper AVX lane zeroing (`SouperCert`)<br>• Provenance-erasing pointer-to-`UInt64` lowering (`LlvmO3Validator`)<br>• Block-to-flat ELF memory (`AnnealLinkELF`)<br>• Multi-language `MirLang` + `Clight` + `Asm` linking (`DimSumLink`) | • Parameterizing `Language` by `SemObs` (`obs : Out → SemObs`) lets languages with heterogeneous internal states compose over a shared `SemObs := EventualOut IoObs Unit` spine.<br>• Quotient unobservable caller-saved scratch registers and dead flags in `L₂.Out` while enforcing target representation invariants (2-valued `bool`, `VEX`-zeroed upper lanes, preserved callee-saved registers) via partial `decodeOut : L₂.Out → Option L₁.Out`. |
| **`Compiles` vs. `Abstracts` Dual Polarities** | • Downward compilation & TV (`NaiveCodegen`, `VeriISLE`, `CertRegAlloc2`, `LlvmO3Validator`)<br>• Upward binary lifting & decompilation (`InlineAsmSimdLifter`, `GraphLangBinaryLifter`, `VerifiedDecompiler`, `EbpfJitterbug`) | • Both `Compiles` and `Abstracts` are instances of `L_low.sem ≤ codec.toMorphism (L_high.sem)` over `Partial`.<br>• In `Compiles`, source UB (`defined = False`, $\top$) licenses compiler optimizations and flat-memory adjacency.<br>• In `Abstracts`, lifted-IR assertion failures (`defined = False`, $\top$) defer dynamic switch-table bounds proofs to `ProductiveOn`. |
| **`ProductiveOn` + `InhabitedPre`** | • Bounded stack headroom (`StackingPacker`)<br>• Unconditional SFI sandboxing of *untrusted* Wasm modules (`WasmSfiSandbox`)<br>• eBPF kernel safety + termination (`EbpfJitterbug`)<br>• GPU wavefront barrier convergence (`GpuShaderGuardian`) | • `Compiles` alone only guarantees safety when the source is UB-free. Stating `TargetLang.ProductiveOn SandboxPre (compile u)` directly on the target machine certifies unconditional SFI hardware isolation even on adversarial inputs `u`. |
| **`VerificationResult` (Positive Per-Obligation)** | • Custom ISLE rule VCs (`VeriISLE`)<br>• Stack watermarks (`StackingPacker`)<br>• ELF relocation bounds (`AnnealLinkELF`)<br>• Per-cut-point `-O3`/`Cranelift` VCs (`LlvmO3Validator`, `CraneliftValidator`)<br>• `asm!` constraints (`InlineAsmSimdLifter`)<br>• Decompiler separation (`VerifiedDecompiler`) | • Positive per-obligation clauses (`ob.id ∈ waived ∨ ob.prop`) decompose backend, linker, inline-asm, and decompiler checks into parallelizable obligations without Principle-of-Explosion contamination. |
| **`SmallStepMachine` + `EventualBehaviorOf` + `StepResult.externalCall`** | • $1 \to k$ (`NaiveCodegen`), $k \to 1$ (`VeriISLE`), $0 \leftrightarrow k$ (`CertRegAlloc2`), $0 \leftrightarrow 1$ (`BoltPropellerTV`)<br>• Loop pipelining (`ModuloPipelines`) & VLIW bundles (`BundleHazardPacker`)<br>• Multi-target ABI & red-zone contracts (`AbiMarshal`, `DimSumLink`)<br>• Demonic `asm!` register allocation (`InlineAsmSimdLifter`)<br>• Lockstep 64-lane SIMT wavefronts (`GpuShaderGuardian`) | • `EventualBehaviorOf` insulates `Language` and `BehaviorCodec` from silent step-count ratios and basic-block address permutations.<br>• `StepResult.externalCall boundaryInv branches` captures the exact two-sided ABI boundary contract and models compiler register-allocation degrees of freedom via `.choice .demonic`. |
| **Single-Source `.olean`-Bound Emission (`anneal-audit`)** | • `.s` assembly string (`Trusted.emitX86CrateAsm` in `NaiveCodegen`)<br>• `.o` / ELF linked byte array (`Trusted.emitCrateElfBytes` in `BijectiveCodecIsa` + `AnnealLinkELF`) | • Binding the final `.s` or `.o`/ELF `ByteArray` inside the kernel-checked `.olean` environment and checking byte identity in `anneal-audit` eliminates dual-emitter drift. |

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **Pancake (`CakeML/cakeml/tree/master/pancake`, PLDI 2024), Wasmtime `Winch`,
  and Eurydice (`AeneasVerif/eurydice`):** HOL4-verified imperative systems
  language for device drivers, single-pass baseline codegen, and Rust MIR-to-
  Clight verified compilation.
- **Arrival (CMU/Cranelift 2024-2025), Ruler/Diospyros (`uwplse/ruler`), and
  GreenThumb (`mangpo/greenthumb`):** Chained multi-rule ISLE lowering verifier
  against Arm ASL and e-graph SIMD/instruction-selection synthesizers.
- **ARM-TV and RISCV-TV (`AliveToolkit/alive2`, 2022-2025):** Whole-backend LLVM
  IR to `AArch64` and `RV64GC` assembly translation validators built on Alive2.
- **VeriCert (`ymherklotz/vericert`, OOPSLA 2021) and CompCertM / CompCertOC /
  Simuliris (`snu-sf/CompCertM`, POPL 2020-2024):** Rocq-verified SDC modulo
  pipeline scheduler and open-module C + assembly relational refinement
  frameworks.
- **Katamaran (`katamaran-project/katamaran`), `x86proved`, Binsec `DBA`, and
  `rev.ng` Clift (2023-2025):** Verified Sail ISA bit-codecs (`BehaviorCodec`),
  binary lifters, and comb-free type-safe decompilation dialects.
- **Jitk (`xiw/jitk`, OSDI 2014), K2 (`smartnic/k2`, SIGCOMM 2021), EPSO/Merlin
  (ASPLOS 2024-2025), and Rex (`rex-rs/rex`, ATC 2025):** Coq-verified in-kernel
  BPF JIT, SMT-verified eBPF superoptimizers, and safe Rust kernel extension
  frameworks.

## Boundaries

- **`not examined` — Dynamic shared-object (`dlopen` / `ld-linux.so`) lazy
  PLT/GOT symbol binding at runtime:** Use Case 12 (`AnnealLinkELF`) and Use
  Case 13 (`DimSumLink`) cover static and relocatable ELF linking (including
  static `.got`/`.plt` synthesis and `R_X86_64_GOTPCRELX` relaxation); runtime
  dynamic loader symbol interposition (`LD_PRELOAD`) and lazy resolver mutation
  of `.got.plt` during execution were not modeled.
- **`not examined` — Self-modifying JIT code caches and instruction-cache
  (`icache` / `dcache`) hardware coherence flushes:** Use Case 20
  (`WasmSfiSandbox`) and Use Case 21 (`EbpfJitterbug`) verify ahead-of-time or
  load-time JIT emission prior to execution under `MachineBytesLang`'s
  read-only `.text` fetch invariant; runtime code patching with explicit
  `icbi`/`dc cvau`/`isb` instruction-cache invalidation pipelines belongs to the
  weak-memory/hardware model boundary.
- **`known not to apply` — Unconstrained `Compiles SrcLang TgtLang` as a standalone
  sandbox guarantee for untrusted bytecode:** As established in Use Case 20
  (`WasmSfiSandbox`), proving `Compiles WasmLang X86MachineLang` alone does
  *not* establish sandbox isolation if the input module triggers source-level
  UB; unconditional SFI isolation requires a target-level
  `X86SandboxedLang.ProductiveOn` theorem.

## Evidence

1. **Anneal Trusted Core & MIR-to-x86-64 Pipeline (`source`):**
   - `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`:
     `trusted/lean/Trusted/Refinement.lean` (`Partial`, `Behavior`, `Language`,
     `BehaviorCodec`, `Compiles`, `Abstracts`, `VerificationResultOn`),
     `trusted/lean/Trusted/StepResult.lean` (`StepResult`, `SmallStepMachine`,
     `BehaviorOf`).
   - `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`:
     `trusted/lean/Trusted/X86Semantics.lean` (`X86Machine`, `X86Lang`),
     `theory/Anneal/Compiler/NaiveCodegen.lean` (`compileStmt`, `compileStage0`,
     `naiveCodec`), `theory/Anneal/Compiler/Peephole.lean` (`optimizePeephole`),
     `trusted/audit/TrustedBoundary.lean`.
   - `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`:
     `PRINCIPLES.md`, `README.md`, `trusted/lean/Trusted.lean`.
   - Existing `reference` corpus reports cross-referenced:
     `anneal-behavior-codec-and-progress-refinement-2026`,
     `anneal-structural-external-calls-and-tcb-mutation-testing-2026`,
     `anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`,
     `anneal-rustc-obligation-inventory-and-single-source-codegen-2026`,
     `anllvm-verified-llvm-lowering-tree-borrows-noalias-and-binary-tv-2026`,
     `anneal-isa-integration-architecture-and-roadmap-synthesis-2026`,
     `sail-islaris-compcert-access-foundations`,
     `lean4-wasm-formalizations-and-virtual-isa-verification-2026`,
     `jvm-ebpf-and-typed-admission-frontiers`.
2. **External Compiler Backends, Register Allocators, Linkers, Lifters &
   Sandboxes (`source + normative + documentation`):**
   - *Category A:* `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`
     (v3.18, `backend/Selection.v`, `backend/RTLgen.v`, `backend/Mach.v`,
     `x86/Asm.v`; Leroy CACM 2009 DOI `10.1145/1538788.1538814`); `CakeML/cakeml`
     (Tan et al., JFP 2019 DOI `10.1017/S0956796818000229`); `uwplse/oeuf`
     (Mullen et al., CPP 2018 DOI `10.1145/3167089`); `VeriISLE`/`Crocus`
     (`bytecodealliance/wasmtime` `cranelift/isle/veri`, VanHattum et al.,
     ASPLOS 2024 DOI `10.1145/3620665.3640367`); `Peek` (Mullen et al., PLDI
     2016 DOI `10.1145/2908080.2908109`); `Souper` (`google/souper`,
     arXiv:1711.04422); `Minotaur` (`minotaur-toolkit/minotaur`, Liu et al., CGO
     2024 DOI `10.1109/CGO57630.2024.10444836`); `STOKE` (Schkufza et al.,
     ASPLOS 2013 DOI `10.1145/2451116.2451150`); `Slothy`
     (`slothy-optimizer/slothy`, Abdulrahman et al., TCHES 2024); `Hydra`
     (Mukherjee & Regehr, OOPSLA 2024).
   - *Category B:* `CompCert` `backend/Allocproof.v` & `backend/Movesproof.v`
     (Rideau, Serpette, Leroy, POPL 2008); `bytecodealliance/regalloc2`
     (`src/checker.rs`); `Stack-Aware CompCert` (Wang, Wilke, Shao, POPL 2019
     DOI `10.1145/3290352`; Carbonneaux et al., PLDI 2014 DOI
     `10.1145/2594291.2594301`); `Gankra/abi-cafe`; `CompCert`
     `backend/Conventions1.v`.
   - *Category C:* `Chamois-CompCert` (`BTL` & `postpass`, Six et al., OOPSLA
     2020 DOI `10.1145/3428208` & CPP 2022 DOI `10.1145/3497775.3503679`);
     Tristan & Leroy (POPL 2008 DOI `10.1145/1328438.1328460`, PLDI 2010 DOI
     `10.1145/1806596.1806609`); `CerCo` (Amadio et al., FMSD 2014 DOI
     `10.1007/s10703-014-0207-x`).
   - *Category D:* `Coqbin` (Kennedy et al., PPDP 2013 DOI
     `10.1145/2505879.2505897`); `CompCertELF` (Wang et al., PLDI 2020 DOI
     `10.1145/3385412.3385989`); `linksem` (Kell, Mulligan, Sewell, OOPSLA 2016
     DOI `10.1145/2983990.2983996`); `SepCompCert` (Kang et al., POPL 2016 DOI
     `10.1145/2837614.2837642`); `CompCertM` (Song et al., POPL 2020 DOI
     `10.1145/3371083`); `CompCertO` (Koenig & Shao, PLDI 2021 DOI
     `10.1145/3453483.3454097`); `DimSum` (Sammler et al., POPL 2023 DOI
     `10.1145/3571219`); `LLVM BOLT` (Panchenko et al., CGO 2019 DOI
     `10.1109/CGO.2019.8661201`); `Google Propeller` (Shen et al., ASPLOS 2023
     DOI `10.1145/3575693.3575727`); `Egalito` (ASPLOS 2020 DOI
     `10.1145/3373376.3378522`); `BinRec` (EuroSys 2020 DOI
     `10.1145/3342195.3387550`).
   - *Category E:* `seL4/graph-refine@94c93d18830d680fc6732d21fb16ca58ebca9dc5`
     (Sewell, Myreen, Klein, PLDI 2013 DOI `10.1145/2491956.2462183`);
     `AliveToolkit/alive2@adacbd5180ccf95075e9867c4f0c259f59c9fef2` (Lopes et
     al., PLDI 2021 DOI `10.1145/3453483.3454030`); Tristan-Govereau-Morrisett
     (PLDI 2011 DOI `10.1145/1993498.1993533`); Necula (PLDI 2000 DOI
     `10.1145/349299.349314`); `leanprover/LNSym@5c05220ff970e3bdd7813ad0c9ef3741522c8b92`.
   - *Category F:* `TInA`/`RUSTInA` (Recoules et al., ESEC/FSE 2019 DOI
     `10.1145/3338906.3338962` & ISSTA 2019 DOI `10.1145/3293883.3295709`);
     `rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9` (Sammler et
     al., PLDI 2022 DOI `10.1145/3519939.3523434`); `project-everest/vale@bbae0eb891`;
     `jasmin-lang/jasmin@34f15840f1`; Myreen, Gordon, Slind (PLDI 2010 DOI
     `10.1145/1806596.1806610`); `HolBA` (Lindner et al., SEFM 2019); `FoxDec`
     (`ssrg-vt/FoxDec`, Verbeek et al.).
   - *Category G:* `VeriWasm` (Johnson et al., NDSS 2021 DOI
     `10.14722/ndss.2021.24296`); `vWasm` (Bosamiya, Lim, Parno, USENIX Security
     2022); `RockSalt` (Morrisett et al., PLDI 2012 DOI
     `10.1145/2254064.2254111`); `ARMor` (Zhao et al., OOPSLA 2011 DOI
     `10.1145/2048066.2048105`); `WasmCert` (`WasmCert-Coq@58a3d3f8b7`);
     `veRA` (Brown et al., POPL 2020); `vbpf/prevail@cefe6a799f` (Gershuni et
     al., PLDI 2019 DOI `10.1145/3314221.3314590`); `Agni` (Vishwanathan et al.,
     PACMPL 2023 DOI `10.1145/3591280`); `uw-unsat/jitterbug@78d1e75ad5`
     (Nelson et al., OSDI 2020); `future-proof-iot/CertFC@75690097c9` (`CertrBPF`);
     `GPUVerify` (Betts et al., OOPSLA 2012 DOI `10.1145/2384616.2384625`);
     `Faial` (Cogumbreiro et al., CAV 2021 DOI `10.1007/978-3-030-81685-8_11`).

## Revalidation

To revalidate the architectural mappings and primitive invariants in this report
after a change to `trusted/lean/` or the target backend pipelines:

1. **Verify `BehaviorCodec`, `EventualBehaviorOf`, and `StepResult.externalCall`
   primitives:** Inspect `trusted/lean/Trusted/Refinement.lean` and
   `trusted/lean/Trusted/StepResult.lean` in `joshlf/anneal` and confirm that:
   - `Language SemObs` retains `obs : Out → SemObs`;
   - `PartialBehaviorCodec` / `BehaviorCodec` enforces `decodeOut (encodeOut o₁) = some o₁`,
     `decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`, and `obs_decodeOut`;
   - `EventualBehaviorOf` defines `Query := State` and `Out := EventualOut Obs Val`
     without leaking internal step counts into `Query`; and
   - `StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop)`
     branches to `.choice .demonic branches` when `boundaryInv = true` and
     `.failed .ub` when `boundaryInv = false`.
2. **Rerun the mechanized Lean 4.34.1 probes in companion corpus packages:**
   - Re-check `reports/anneal-behavior-codec-and-progress-refinement-2026/support/behavior_codec_progress_probe.lean`
     (variable-step `EventualBehaviorOf`, `PartialBehaviorCodec`, and `π_opt`
     anti-degeneracy);
   - Re-check `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/support/`
     (`StepResult.externalCall` reentrancy and frame isolation); and
   - Re-check `reports/anllvm-verified-llvm-lowering-tree-borrows-noalias-and-binary-tv-2026/support/round2_track5_probe.lean`
     (`GraphLang` stack-slot scalarization and $k:1$ unrolled loop binary TV).
3. **Validate corpus metadata:** Run `python3 tools/reference.py check` from the
   `reference` worktree root.
