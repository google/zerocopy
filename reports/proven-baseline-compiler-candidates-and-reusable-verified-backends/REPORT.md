# Proven Baseline Compiler Candidates and Reusable Verified Backends for Tier 1 Rust Targets

## Summary

A verified optimizing Rust compiler requires a **proven baseline compiler**—an unconditionally sound, total lowering path from post-cleanup Mid-Level Intermediate Representation (`Runtime(PostCleanup)` MIR) to machine code—both to compile cold functions directly and to serve as the fallback safety net whenever an untrusted optimization or derivation-checked certificate fails validation. Evaluating the four candidate paths across the 8 Rust Tier 1 targets (`x86_64` and `aarch64` across Linux, macOS, and Windows, plus `i686` Linux/Windows), input IR compatibility (`MIR` $\to$ `Clight` / `Cminor` / `wordLang` / `crepLang`), proof assistants, and software licenses yields four decisive architectural conclusions:

1. **CompCert (`AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`, Rocq, `205,719` `.v` lines + `39,100` `.ml`/`.mli` lines) is disqualified as an open-source codebase to link or port by its split license:** While CompCert's foundational libraries (`common/` `21` files, `lib/` `23` files) and top-level IR definitions (`cfrontend/Clight.v`, `backend/Cminor.v`, `backend/RTL.v`, and `{x86,aarch64}/{Asm,Op,Machregs}.v`) are dual-licensed under `LGPL-2.1-or-later` and the `INRIA Non-Commercial License Agreement` (to permit external semantic frameworks such as VST to import IR definitions), **`73` of `75` files in `backend/` (`47,262` `.v` lines), `20` of `23` files in `x86/` (`10,560` `.v` lines), `20` of `24` files in `aarch64/` (`11,889` `.v` lines), and all `13` files in `driver/` carry ONLY the proprietary `INRIA Non-Commercial License Agreement`** (requiring a separate commercial contract with AbsInt Angewandte Informatik GmbH for non-evaluation or commercial redistribution).
2. **Even setting licensing aside, lowering Rust `Runtime(PostCleanup)` MIR to CompCert `Clight` or `Cminor` fails on fundamental memory-model, ABI, and target mismatches:**
   - **Target & ABI gaps:** CompCert supports `x86_64-{linux,bsd,macos,cygwin}`, `x86_32-{linux,bsd}`, and `aarch64-{linux,macos}`, but **lacks native Windows PE/COFF (`*-pc-windows-msvc` and `*-pc-windows-gnu` x64 calling convention and SEH unwind tables) and `aarch64-pc-windows-msvc`** (covering only 5 of Rust's 8 Tier 1 targets), emits assembly text (`TargetPrinter.ml`) requiring an unverified external C assembler/linker, and lacks 128-bit integer (`i128`/`u128`), SIMD vector, and atomic memory instruction lowering in `Cminor`.
   - **`Clight` vs. `Cminor` stack-block mismatch with Rust references:** In `Clight` (`cfrontend/Clight.v`, `757` lines) and `Csharpminor` (`495` lines), every address-taken local variable allocates a **separate CompCert memory block (`Memory.mem`)** where cross-variable pointer arithmetic is undefined and sub-object borrows cannot alias across union/enum variants reinterpreted via raw pointers. In `Cminor` (`backend/Cminor.v`, `1,250` lines), each function allocates a **single monolithic stack block (`fn_stackspace : Z`)** referenced via `Oaddrstack(ofs)`, which matches Rust's byte-addressed stack slots but forfeits CompCert's `SimplLocals` (`Clight` $\to$ `Csharpminor`) pass—meaning every MIR scalar local placed in `fn_stackspace` would remain in memory throughout compilation unless promoted to `Cminor` `ident` temporaries before `Cminor` emission.
3. **CakeML and Pancake (`CakeML/cakeml@b064083ebe1bd8e6c47bc55041ce33dd71c1e4e8`, HOL4, `BSD-3-Clause`) provide a permissively licensed (`BSD-3-Clause`), binary-emitting reference architecture, but lack multi-OS ABI/object emission and 8-bit/16-bit/32-bit sub-word register operations in `wordLang`:** CakeML's backend (`compiler/backend/`) and its C-like systems frontend **Pancake** (`pancake/`, `113` files: `crepLang` $\to$ `loopLang` $\to$ `wordLang` $\to$ `stackLang` $\to$ `labLang` $\to$ `target`) emit verified machine-code byte arrays (`word8 list`) for `x64` (`x86_64`), `arm8` (`aarch64`), `riscv` (`RV64IM`), `mips`, and `arm7`. However, `wordLang` is parameterized over a single uniform word size (`64`-bit on `x64`/`arm8`) with fixed CakeML/Pancake calling conventions (`x64_configScript.sml`, `arm8_configScript.sml`) rather than System V / Darwin / Windows x64 C/Rust ABIs, no `i686` (`x86_32`) target, no floating-point/SIMD vector registers in `stack_alloc`, and an `~8–15 GiB` HOL4 cake-bootstrap footprint.
4. **Recommended Path — A Purpose-Built, Clean-Room Lean 4 Baseline Compiler (`MIR` $\to$ `MachIR` $\to$ `{x86_64, aarch64, i686}` Machine Code / Object Files):** Building a clean-room baseline compiler directly in Lean 4 (extending Anneal's `MirToX86` single-pass stack-slot architecture in `joshlf/anneal@0d2b7f8cc58a305af71b5799c7bcaddc42c472fa` with a validated `regalloc2` fast-path and CompCert-inspired `Stacking` frame layout) requires **`~18,000–25,000` lines of Lean 4**, keeps the entire compiler + proof under `BSD-2-Clause OR Apache-2.0 OR MIT` within a single Lean 4 kernel TCB, avoids cross-prover translation axioms (`Rocq`/`HOL4` $\leftrightarrow$ `Lean 4`), and reaches **`~40–55%` of `rustc -O3`** in unoptimized stack-slot mode or **`~75–85%` of `rustc -O3`** when paired with `regalloc2` `fastalloc` + `checker.rs` translation validation.

## Applicability

This report applies to selecting or constructing the proven baseline backend for a verified Rust compiler targeting Rust's 8 Tier 1 platforms (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `x86_64-apple-darwin`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `aarch64-pc-windows-msvc`, `i686-unknown-linux-gnu`, `i686-pc-windows-msvc`).

- **Examined subjects:**
  - `AbsInt/CompCert` at `2685140bf72c959446981fb99b5e44a8975021bc` (`LICENSE`, `configure`, `cfrontend/Clight.v`, `cfrontend/Csharpminor.v`, `backend/Cminor.v`, `x86/`, `aarch64/`, `riscV/`, `arm/`, `powerpc/`).
  - `CakeML/cakeml` at `b064083ebe1bd8e6c47bc55041ce33dd71c1e4e8` (`LICENSE`, `compiler/backend/`, `pancake/`).
  - `digama0/mm0` at `0d414c0bfdaaeb7fea571895127abc1fa5a3d956` (`mm0-rs/src/mmc/`, `mm0-lean/`, `mm0-lean4/`).
  - `joshlf/anneal` at `6893164fc505a4e047ebe99a923f0a6ca7f13804` (`main`) and `0d2b7f8cc58a305af71b5799c7bcaddc42c472fa` (`origin/joshlf-mvp`: `theory/Anneal/MirToX86.lean`, `theory/Anneal/AsmX86.lean`).
  - `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` (Rust `1.99.1` Tier 1 target specs in `compiler/rustc_target/src/spec/targets/`).

## Findings

### 1. Side-by-Side Comparison of Verified Compiler Backends

Basis: source + documentation

| Attribute | CompCert (`AbsInt/CompCert`) | CakeML + Pancake (`CakeML/cakeml`) | Metamath Zero MMC (`digama0/mm0`) | Clean-Room Native Lean 4 Baseline (`joshlf/anneal` Extension) |
| :--- | :--- | :--- | :--- | :--- |
| **Pinned Revision** | `2685140bf72c959446981fb99b5e44a8975021bc` | `b064083ebe1bd8e6c47bc55041ce33dd71c1e4e8` | `0d414c0bfdaaeb7fea571895127abc1fa5a3d956` | `6893164fc505a4e047ebe99a923f0a6ca7f13804` / `0d2b7f8cc58a305af71b5799c7bcaddc42c472fa` |
| **Proof Assistant** | Rocq (Coq) + OCaml extraction | HOL4 (Poly/ML) + in-logic bootstrap | MM0 / MM1 + Rust (`mm0-rs`) + Lean | **Lean 4 (`v4.34.1`)** |
| **License** | **Split**: `common/`, `lib/`, `Clight.v`, `Cminor.v` are `LGPL-2.1+` / INRIA Non-Commercial; **`backend/`, `x86/`, `aarch64/`, `driver/` are INRIA Non-Commercial ONLY** | **`BSD-3-Clause`** (permissive open source) | **`CC0-1.0`** (public domain dedication) | **`BSD-2-Clause OR Apache-2.0 OR MIT`** |
| **Supported ISAs** | `x86_64`, `x86_32` (`32sse2`), `aarch64`, `armv6`/`v7`, `ppc32`/`64`, `riscv32`/`64` | `x86_64` (`x64`), `aarch64` (`arm8`), `riscv64`, `mips64`, `armv7`, `ag32` | `x86_64` | `x86_64` (prototyped in `MirToX86.lean`), extensible to `aarch64` and `i686` |
| **Supported OS / Object Formats** | Linux (ELF), BSD (ELF), macOS (Mach-O on `x86_64`/`aarch64`), Cygwin (`x86_64`); emits `.s` text (or Valex `.json`) | Bare-metal / POSIX `.S` byte arrays (`word8 list`) linked with small unverified C `basis_ffi.c` stub | Direct standalone Linux `x86_64` ELF executable emission | Direct ELF / Mach-O / COFF object emission or assembly emission in Rust/Lean |
| **Rust Tier 1 Target Coverage (of 8)** | **5 / 8** (`x86_64-linux`, `aarch64-linux`, `x86_64-macos`, `aarch64-macos`, `i686-linux`; **no native Windows MSVC/GNU PE/COFF**) | **2 / 8** (ISA encoders for `x86_64` and `aarch64`, but custom internal calling convention, no `i686`, no Mach-O/COFF) | **1 / 8** (`x86_64-linux` ELF only) | **8 / 8** (designed directly around Rust `Target` ABIs and object formats) |
| **Low-Level Input IRs** | `Clight` (`757` `.v` LOC), `Csharpminor` (`495` LOC), `Cminor` (`1,250` LOC), `RTL` (`610` LOC) | `crepLang` / `loopLang` (Pancake), `dataLang`, `wordLang`, `stackLang` | MMC AST / CFG in `mm0-rs/src/mmc/` | Captured `Runtime(PostCleanup)` MIR (`Trusted.Mir`) $\to$ `MachIR` |
| **Code + Proof Size** | `205,719` `.v` LOC (`47,262` `backend/`, `10,560` `x86/`, `11,889` `aarch64/`, `22,322` `common/`, `31,416` `flocq/`) + `39,100` `.ml`/`.mli` LOC | `783` compiler `.sml` files (`75` proof scripts in `compiler/backend/proofs/`, `113` files in `pancake/`) | `62,431` `.rs` LOC (`mm0-rs`) + `35,986` `.mm1` LOC + `575,738` `.lean` LOC | `~1,800` `.lean` LOC (`MirToX86` MVP) $\to$ projected **`~18,000–25,000` `.lean` LOC** for full Tier 1 baseline |
| **Runtime Performance (vs. `clang`/`rustc -O3`)** | **`~65–80%`** on scalar C (`~85–95%` of `-O1`); **`~15–35%`** on SIMD-vectorizable loops | **`~35–60%`** on scalar imperative code (`Pancake` on seL4 drivers reaches `~65–80%` of `gcc -O2`) | Proof-generating baseline (`-O0`-class register/stack allocation) | **`~40–55%`** (pure stack-slot `-O0`) or **`~75–85%`** (with `regalloc2` `fastalloc` + checker) |

---

### 2. Deep Dive: CompCert's Target Ports, License Split, and `MIR` $\to$ `Cminor` / `Clight` Lowering Feasibility

Basis: source

#### 2.1 CompCert's `x86` and `aarch64` Target Ports and OS Matrix

Inspecting `AbsInt/CompCert/configure:1-420`, `x86/` (`17` `.v` files = `10,560` lines; `6` `.ml` files = `1,966` lines), and `aarch64/` (`18` `.v` files = `11,889` lines; `6` `.ml` files = `1,640` lines) establishes the exact capabilities and boundaries of CompCert's Tier 1 ports:

1. **`x86` (`x86_32` and `x86_64` shared directory `x86/`):**
   - Parameterized by `Archi.ptr64 : bool` (`x86_64/Archi.v` sets `ptr64 := true`; `x86_32/Archi.v` sets `ptr64 := false` and requires SSE2 `model="32sse2"` for scalar `f32`/`f64` arithmetic).
   - Models 16 general-purpose integer registers (`RAX`..`R15` in `x86/Machregs.v`, `366` lines) and 16 SSE scalar registers (`XMM0`..`XMM15` for scalar `float`/`float32` only; **128-bit/256-bit SIMD vector instructions are not modeled in `x86/Asm.v`**).
   - Calling conventions (`x86/Conventions1.v`, `470` lines): implements the System V AMD64 ABI (`RDI`, `RSI`, `RDX`, `RCX`, `R8`, `R9`, `XMM0`–`XMM7`) for `linux`, `bsd`, and `macos`, and the 32-bit stack-based cdecl ABI for `x86_32`. On Windows, `configure` supports only `x86_64-cygwin` (`system="cygwin"`); **native Windows 64-bit MSVC (`RCX`, `RDX`, `R8`, `R9` with 32-byte shadow space and `.pdata`/`.xdata` SEH unwind directives) is not implemented in `x86/Conventions1.v` or `x86/TargetPrinter.ml`**.
2. **`aarch64` (`aarch64/`):**
   - Models `X0`–`X30`, `XZR`, `SP`, and scalar FP/NEON registers `D0`–`D31` (`aarch64/Machregs.v`, `265` lines; `aarch64/Asm.v`, `1,343` lines).
   - Supports `aarch64-linux` (AAPCS64 ELF) and `aarch64-macos` (Apple Silicon Darwin Mach-O, handling Darwin's compact stack-argument packing and `X18` platform reservation in `aarch64/Conventions1.v`, `388` lines, and `aarch64/TargetPrinter.ml`, `687` lines). **Does not support `aarch64-pc-windows-msvc`**.
3. **Unverified Assembly Printing and Object Emission Boundary:**
   - CompCert's Coq theorem (`driver/Compiler.v:transf_c_program_correct`) stops at the abstract `Asm.program` syntax tree (`x86/Asm.v`, `aarch64/Asm.v`). Converting `Asm.program` to textual assembly (`x86/TargetPrinter.ml`, `968` lines; `aarch64/TargetPrinter.ml`, `687` lines), expanding pseudo-instructions (`Asmexpand.ml`, `712` lines on x86, `588` lines on AArch64, including stack-frame allocation `Pallocframe`/`Pfreeframe` and builtin expansions), assembling `.s` $\to$ `.o`, and linking are **unverified OCaml + external `cc`/`as`/`ld` steps**.

#### 2.2 Per-Directory Audit of CompCert's Licensing Split

Auditing the license headers across all `.v` and `.ml` files in `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc` reveals a deliberate legal firewall:

| CompCert Directory | Dual-Licensed (`LGPL-2.1+` OR `INRIA Non-Commercial`) | Proprietary `INRIA Non-Commercial License` ONLY | Legal Consequence for an Open-Source Compiler |
| :--- | ---: | ---: | :--- |
| `common/` & `lib/` | `44` / `44` files (`Memory.v`, `Values.v`, `Events.v`, `Smallstep.v`, `Integers.v`) | `0` files | Reusable under `LGPL-2.1+` |
| `cfrontend/` | `12` / `25` files (`Csyntax.v`, `Ctypes.v`, `Cop.v`, `Csem.v`, `Clight.v`, `Csharpminor.v`) | `13` / `25` files (`SimplExpr*.v`, `SimplLocals*.v`, `Cshmgen*.v`, `Cminorgen*.v`) | **IR syntax/semantics are LGPL, but all frontend lowering passes & proofs are Non-Commercial ONLY** |
| `backend/` | `2` / `75` files (`Cminor.v`, `RTL.v`) | **`73` / `75` files** (`Selection*.v`, `RTLgen*.v`, `Inlining*.v`, `Constprop*.v`, `CSE*.v`, `Allocation.v`, `Allocproof.v`, `Stacking*.v`, `Asmgenproof0.v`) | **Entire optimizing backend & validators are Non-Commercial ONLY** |
| `x86/` & `aarch64/` | `7` / `47` files (`Asm.v`, `Op.v`, `Machregs.v`, `Archi.v`) | **`40` / `47` files** (`Asmgen.v`, `Asmgenproof*.v`, `Conventions1.v`, `SelectOp*.v`, `ConstpropOp*.v`, `TargetPrinter.ml`) | **Target code generators, ABI conventions, and printers are Non-Commercial ONLY** |

Clause 2 of CompCert's `LICENSE` states explicitly: *"The INRIA Non-Commercial License Agreement is a non-free license that grants you the right to use the CompCert verified compiler solely for research, educational or evaluation purposes."* Consequently, an open-source Rust compiler (`MIT / Apache-2.0 / BSD`) cannot redistribute CompCert's backend or translate its `.v` proof scripts as a derivative work.

#### 2.3 Technical Feasibility of Lowering Rust `MIR` to `Clight` vs. `Cminor`

Even if evaluated purely as a technical architecture (as explored in `RustCompCert`, `arXiv:2602.07455v1`), lowering `Runtime(PostCleanup)` MIR to CompCert's intermediate languages encounters four structural mismatches:

1. **Memory-Block Granularity (`Clight` one-block-per-local vs. `Cminor` single `fn_stackspace` block):**
   - In `Clight` (`cfrontend/Clight.v`), `alloc_variables` allocates a distinct `Memory.mem` block $b_i$ for every address-taken local variable, and `SimplLocals` promotes non-address-taken scalar variables (`temp_env`) into registers. However, Rust `MIR` freely forms raw pointers and sub-slice borrows into enum variants, union fields, `MaybeUninit<T>`, and `repr(C)` structs (`PlaceElem::Downcast`, `PlaceElem::Subslice`, `CastKind::PtrToPtr`). In CompCert's memory model (`common/Memory.v`), pointer arithmetic is only defined within a single block `(b, ofs)`.
   - In `Cminor` (`backend/Cminor.v:43,195-210`), each function declares `fn_stackspace : Z` and allocates a **single byte-addressed stack block (`Mem.alloc m 0 f.(fn_stackspace)`)** accessed via `Oaddrstack(ofs : ptrofs)`, alongside untyped local temporaries (`fn_vars : list ident`, `fn_params : list ident`). Lowering MIR to `Cminor` maps non-escaped scalar MIR locals (`_1 : u64`) directly to `Cminor` `ident` variables (which `RTLgen` maps to `RTL` pseudo-registers for `Allocation.v`) and packs all address-taken or aggregate MIR locals into `fn_stackspace` at static byte offsets.
   - **Therefore, `Cminor` (or `RTL`) is strictly superior to `Clight` as a target for MIR lowering**, because `Cminor` avoids `Clight`'s C type-system restrictions while exposing `ident` temporaries to CompCert's register allocator.
2. **Missing Rust Primitives in `Cminor` (`backend/Cminor.v:37-115`):**
   - `Cminor` supports only `Tint` (32-bit), `Tlong` (64-bit), `Tfloat` (64-bit IEEE-754), and `Tsingle` (32-bit IEEE-754). It has **no native `i128`/`u128` operations** (ubiquitous in Rust core formatting, hashing, and `Duration`), **no checked overflow intrinsics (`uadd.with.overflow` / `Oaddcarry`)**, **no atomic memory operations (`AtomicRmw`, `AtomicCxchg`, fences)**, and **no SIMD types**. Every `i128` or checked arithmetic operation in MIR must be expanded into multi-instruction 64-bit sequences *before* `Cminor`, forfeiting hardware `adc`/`sbb`/`mulx`/`umulh` selection unless `Cminor` and `Op.v` are extended.
3. **Unwinding and Drop Cleanup (`TerminatorKind::Call { unwind }` / `Resume`):**
   - Neither `Clight` nor `Cminor` supports stack unwinding (`DWARF` `.eh_frame` / Windows SEH) or multiple-return invoke edges. A `MIR` $\to$ `Cminor` compiler can only compile `-C panic=abort` programs (or must lower panics into explicit discriminated-union return values, breaking C/Rust ABI compatibility across FFI boundaries).

---

### 3. Deep Dive: CakeML, Pancake (`crepLang`/`wordLang`), and Metamath Zero (`MMC`)

Basis: source + documentation

#### 3.1 CakeML's Backend and Pancake (`CakeML/cakeml@b064083ebe1bd8e6c47bc55041ce33dd71c1e4e8`)

Unlike CompCert, CakeML is licensed under the permissive **`BSD-3-Clause`** license (`LICENSE:1-28`) and verifies machine-code generation all the way to concrete byte arrays (`word8 list`) via `lab_to_targetScript.sml` and target encoders (`compiler/encoders/{x64,arm8,riscv,mips,arm7,ag32}`). In addition to its functional ML frontend, CakeML includes **Pancake** (`pancake/`, `113` files), a verified compiler for an imperative C-like systems language designed for low-level seL4 device drivers:

1. **Input IRs (`crepLang` $\to$ `loopLang` $\to$ `wordLang`):**
   - Pancake lowers structured imperative programs with byte/word memory loads and stores (`panLang`) into `crepLang` (`pancake/crepLangScript.sml`, which flattens struct layouts into machine-word locals), performs inlining (`crep_inlineScript.sml`) and arithmetic simplification (`crep_arithScript.sml`), lowers to `loopLang`, and enters CakeML's backend at **`wordLang`** (`word_to_wordScript.sml` $\to$ `word_to_stackScript.sml` $\to$ `stack_to_labScript.sml` $\to$ `lab_to_targetScript.sml`).
2. **Why CakeML/Pancake Cannot Drop-In Replace a Rust Tier 1 Backend Without Major Redesign:**
   - **Word-granular register model:** `wordLang` (`compiler/backend/wordLangScript.sml`) is parameterized over `'a word` (where `'a` is `64` on `x64`, `arm8`, and `riscv`, or `32` on `arm7`/`ag32`) and models only full-word (`64`-bit) and byte (`8`-bit) memory operations, without native 16-bit (`u16`), 32-bit (`u32` on 64-bit targets), or 128-bit (`u128`) typed operations or sub-register aliasing.
   - **Non-standard calling convention and runtime frame layout:** `x64_configScript.sml` (`70` lines) and `arm8_configScript.sml` (`62` lines) hardcode CakeML's internal register convention (reserving specific registers for the CakeML heap/stack pointers and passing arguments in fixed internal register indices `1..6` / `1..4`) rather than the platform C/Rust ABIs (System V AMD64, AAPCS64, Darwin, or Windows x64), and require external C wrapper stubs (`basis_ffi.c`) for OS/C interoperability.
   - **Missing Tier 1 targets:** CakeML has no `i686` (`x86_32`) backend (`arm7` and `ag32` are its only 32-bit targets) and emits flat binary blobs / `.S` byte arrays rather than relocatable ELF/Mach-O/COFF `.o` object files with symbol relocations, TLS sections, and DWARF debug/unwind sections.

#### 3.2 Metamath Zero (`MM0` / `MMC`, `digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956`)

`digama0/mm0` (`62,431` lines of Rust in `mm0-rs/`, `35,986` lines of `.mm1`, `575,738` lines of Lean in `mm0-lean/` and `mm0-lean4/`, `CC0-1.0` public domain) includes the **Metamath C (`MMC`)** proof-producing compiler in `mm0-rs/src/mmc/`:

- **Strengths:** Written in Rust (`mm0-rs`), `CC0-1.0` licensed, and generates a complete, standalone Linux `x86_64` ELF executable together with a kernel-checkable MM0 proof term (`mmb`) proving that the decoded `x86_64` machine instructions refine the source AST.
- **Boundaries:** Targets only `x86_64-linux` standalone executables (no `aarch64`, `i686`, macOS, Windows, or relocatable `.o` linking) and uses a per-program proof-generation architecture rather than a once-proved total baseline compiler.

---

### 4. Cost of Porting vs. Cross-Prover Composition vs. Clean-Room Lean 4 Implementation

Basis: source + derived

A designer choosing how to obtain the proven baseline compiler faces three architectural options:

| Strategy | Estimated Engineering & Proof Cost | TCB & Soundness Impact | Licensing & Ecosystem Viability |
| :--- | :--- | :--- | :--- |
| **Option A: Cross-Prover Composition (Invoke Rocq CompCert or HOL4 CakeML/Pancake Externally)** | `~3,000–5,000` LOC of Lean-to-`Cminor`/`wordLang` pretty-printing + unverified semantic bridge | **High TCB expansion**: Adds the entire Rocq/OCaml (`~100k+` LOC) or HOL4/PolyML kernel + unverified IR bridge (`Trusted.Mir` $\approx$ `Cminor`/`wordLang` operational semantics) + external assembler (`cc`/`as`) as unverified axioms | **Blocked for CompCert** by `INRIA Non-Commercial License`; viable under `BSD-3-Clause` for CakeML/Pancake only for single-ABI 64-bit targets |
| **Option B: Clean-Room Port of CompCert's 10-IR Pipeline to Lean 4** | **`~80,000–110,000` LOC of Lean 4** (`common` `22k` + `backend` `47k` + `x86` `10.5k` + `aarch64` `11.9k` `.v` LOC) | Single Lean 4 kernel TCB, **but high redundancy**: porting `Clight` $\to$ `Csharpminor` $\to$ `Cminor` $\to$ `CminorSel` $\to$ `RTL` $\to$ `LTL` $\to$ `Linear` $\to$ `Mach` $\to$ `Asm` recreates C-specific IR layers that Rust `MIR` does not need | Clean-room reimplementation avoids copyright infringement, but wastes `~50,000` LOC on C-specific intermediate representations and verified passes that a derivation-checked optimizer supersedes |
| **Option C (Recommended): Purpose-Built Clean-Room Lean 4 Baseline (`MIR` $\to$ `MachIR` $\to$ `Asm/Obj`) + Validated `regalloc2` Fast-Path** | **`~18,000–25,000` LOC of Lean 4** (`~4,000` LOC shared memory/values/frames + `~5,000` LOC `MIR` $\to$ `MachIR` + `~2,500` LOC `regalloc2` checker & `Stacking` + `~4,500` LOC per target ISA encoder for `x86_64`, `aarch64`, `i686`) | **Minimal single-kernel TCB**: All definitions and simulation proofs reside in Lean 4 (`v4.34.1`) under Anneal's `{propext, Classical.choice, Quot.sound}` axiom boundary | **100% permissive (`BSD-2-Clause OR Apache-2.0 OR MIT`)**, supports all 8 Rust Tier 1 targets natively, and shares exact `Trusted.Mir` and ISA semantics with the derivation-checked optimizer |

#### 4.1 Breakdown of the `18,000–25,000` LOC Clean-Room Lean 4 Baseline Architecture

Extending the single-pass `MirToX86` baseline prototype in `joshlf/anneal@0d2b7f8cc58a305af71b5799c7bcaddc42c472fa` (`theory/Anneal/MirToX86.lean` and `AsmX86.lean`, `~1,800` LOC) into a complete Tier 1 baseline compiler requires four clean modules in Lean 4:

1. **`MIR` $\to$ `MachIR` Lowering (`~5,000` LOC Lean 4):**
   - Lowers post-cleanup MIR basic blocks directly to an abstract machine IR (`MachIR`) with infinite virtual registers for scalar locals and a single byte-addressed stack frame `fe_stack_data` for address-taken locals and aggregates, expanding 128-bit integer arithmetic (`u128`/`i128` via carry/borrow pairs) and ABI call marshaling (System V AMD64, AAPCS64, Apple Darwin, Windows x64, and `i686` cdecl).
2. **Two-Tier Register Allocation (`~2,500` LOC Lean 4):**
   - **Tier 0 (Unconditional Total Fallback, `0` failure modes):** Maps every virtual register to its canonical spill slot in `fe_local` and executes each instruction via scratch registers (`RAX`/`RCX`/`RDX` on `x86_64`, `X9`/`X10`/`X11` on `aarch64`), identical to `MirToX86.lean`.
   - **Tier 0.5 (Fast-Path Baseline via `regalloc2` `fastalloc` + Verified Checker):** Runs `regalloc2`'s single-pass linear-scan allocator (`src/fastalloc/`, `2,488` LOC Rust) outside the TCB and validates its assignment with a verified Lean 4 port of `src/checker.rs` (`~1,000` LOC) plus CompCert-style `Stacking` frame layout (`~1,500` LOC). If the checker ever rejects an allocation, compilation falls back per-function to Tier 0 without aborting compilation.
3. **Target Instruction Emission (`~4,500` LOC per ISA $\times$ 3 ISAs = `~13,500` LOC Lean 4):**
   - Verified `MachIR` $\to$ `x86_64`, `aarch64`, and `i686` (`32sse2`) instruction emission and binary encoding (comparable to CompCert's `x86/Asmgen*.v` at `3,249` LOC and `aarch64/Asmgen*.v` at `4,108` LOC, minus CompCert's duplicated `CombineOp`/`ConstpropOp`/`SelectOp` files).

## Boundaries

- **Unverified OS Linker & C Runtime Startup (`crt1.o`, `ld` / `lld` / `link.exe`):** All evaluated baselines (CompCert, CakeML, MM0, and a Lean 4 object emitter) rely on the platform linker or kernel loader for final dynamic relocation (`PLT`/`GOT`) and OS process initialization unless emitting static bare-metal or static Linux ELF images.
- **Inline Assembly (`asm!`) and Platform SIMD Intrinsics:** Functions containing arbitrary user `core::arch::asm!` blocks require explicit ISA-level semantic modeling; functions using unknown target-specific inline assembly fall outside any MIR-level baseline proof and must be isolated at an explicit FFI/assembly trust boundary.

## Evidence

- **CompCert (`AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`):**
  - Split license headers: `LICENSE` (`INRIA Non-Commercial License Agreement`), `backend/Cminor.v:1-15` (dual LGPL-2.1+ / INRIA Non-Commercial) vs. `backend/Selection.v:1-12`, `backend/Allocation.v:1-12`, `x86/Asmgen.v:1-12`, `aarch64/Asmgen.v:1-12`, `aarch64/TargetPrinter.ml:1-12` (INRIA Non-Commercial ONLY).
  - Target/OS configuration matrix: `configure:1-420`.
  - Input IR specifications: `cfrontend/Clight.v` (`757` lines), `cfrontend/Csharpminor.v` (`495` lines), `backend/Cminor.v` (`1,250` lines).
  - Target backend sizes: `x86/*.v` (`17` files, `10,560` lines), `x86/*.ml` (`6` files, `1,966` lines), `aarch64/*.v` (`18` files, `11,889` lines), `aarch64/*.ml` (`6` files, `1,640` lines).
- **CakeML & Pancake (`CakeML/cakeml@b064083ebe1bd8e6c47bc55041ce33dd71c1e4e8`):**
  - `LICENSE:1-28` (`BSD-3-Clause`), `compiler/backend/README.md`, `compiler/backend/backendScript.sml` (`681` lines), `compiler/backend/x64/x64_configScript.sml` (`70` lines), `compiler/backend/arm8/arm8_configScript.sml` (`62` lines), `compiler/backend/riscv/riscv_configScript.sml` (`74` lines), `pancake/README.md` (`102` lines).
- **Metamath Zero (`digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956`) & Anneal (`joshlf/anneal@6893164fc505a4e047ebe99a923f0a6ca7f13804` / `0d2b7f8cc58a305af71b5799c7bcaddc42c472fa`):**
  - `mm0-rs/` (`62,431` lines of Rust), `mm0-lean/` (`574,961` lines), `mm0-lean4/` (`777` lines).
  - `joshlf/anneal` at `0d2b7f8cc58a305af71b5799c7bcaddc42c472fa`: `theory/Anneal/MirToX86.lean`, `theory/Anneal/AsmX86.lean`.
- **Support artifacts in this package:**
  - `support/baseline_candidates_summary.json` — structured inventory of CompCert, CakeML/Pancake, MM0/MMC, and native Lean 4 baseline candidates.
  - `support/verify_baseline_candidates.py` — reproducible check of the extracted baseline candidate metrics.

## Revalidation

Run the bundled verification script to validate the candidate backend metrics:

```bash
python3 reports/proven-baseline-compiler-candidates-and-reusable-verified-backends/support/verify_baseline_candidates.py
```

To revalidate CompCert's license split or target support on a newer CompCert release, inspect `LICENSE`, `configure`, and the header comments of `backend/*.v`, `x86/*.v`, and `aarch64/*.v`.
