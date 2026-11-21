# Verifying Compiled C/C++ Machine Code in Lean 4: Lifting, Cutpoints, Untrusted Hints, and Proof Scaling

## Summary

Verifying compiler-generated C and C++ object files (`.o`/`.a`) inside Lean 4
under a three-axiom ceiling (`{propext, Classical.choice, Quot.sound}`) and
standalone private-level kernel replay (`trustLevel := 0`, `plugins := #[]`,
`loadExts := false`, `level := .private`) differs structurally from verifying
hand-written leaf assembly (`.S` or Rust `asm!`). Empirical compilation of six
realistic FFI archetypes under `gcc`/`g++` 15.2.0 (`-O2`, `-O3 -mavx2`, and
hardened `-fPIC -fstack-protector-strong -fstack-clash-protection
-fcf-protection=full`) shows that compiler-emitted code introduces seven
phenomena largely absent from cryptographic `.S` kernels:

1. **Cross-section hot/cold CFG splitting and `.rela.rodata` jump-table
   relocations:** A 16-case C `switch` emits a `.text.unlikely` cold stub
   (`opcode_dispatch_16.cold`) that jumps back into the middle of the hot
   function, a CET-IBT `notrack jmp rdx` (`3e ff e2`), and 16 `R_X86_64_PC32`
   relocations inside `.rela.rodata` whose raw `.rodata` bytes are all zero in
   the unlinked `.o`. Any verifier that decodes only `.text` and `.rela.text`
   cannot resolve compiler jump tables.
2. **Multi-versioned auto-vectorization and dynamic stack realignment:** A
   three-line C loop grows from 15 instructions / 4 basic blocks (`-O2`) to 80
   instructions / 24 basic blocks / 4 back-edges / 3 `ret` instructions under
   hardened `-O3 -mavx2` (two runtime pointer-overlap guards, 256-bit AVX2 main
   loop + `vzeroupper`, 128-bit SSE epilog, scalar tail, and scalar alias
   fallback). Stack frames ≥ 8 KiB under `-O3 -mavx2 -fstack-clash-protection`
   combine `and rsp, -32` (symbolic `rsp_entry - rsp ∈ {8248, 8256, 8264,
   8272}`), unrolled `sub rsp, 0x1000; or QWORD PTR [rsp], 0x0` guard-page
   probes (reading uninitialized stack bytes), and TLS stack canaries (`mov
   reg, QWORD PTR fs:0x28` + `__stack_chk_fail@PLT`).
3. **Sibling tail calls, zero-`ret` functions, and compiler-synthesized libc
   calls:** `-ftree-loop-distribute-patterns` replaces hand-written C `for`
   loops with `call memset@PLT` and tail `jmp memcpy@PLT`, producing functions
   with `ret_count = 0`.
4. **C++ speculative devirtualization and exception landing pads:** Default
   `g++ -O2` emits `R_X86_64_REX_GOTPCRELX` vtable comparisons, `.text.unlikely`
   `.cold` cleanup stubs, `.gcc_except_table`, `_Unwind_Resume`,
   `__gxx_personality_v0`, and a second `endbr64` at an exception landing pad
   unreachable from normal control flow. Compiling with `-fno-exceptions
   -fno-rtti` eliminates all unwinding surfaces.

Across four machine-code verification architectures for 50–5,000-instruction
compiled `.o` functions in Lean 4:

- **Direct un-pruned symbolic execution** (`s2n-bignum`/`LNSym`-style
  step-chaining) hits Lean 4's default `200,000`-heartbeat `whnf` timeout by
  `N = 40` spill-heavy instructions and blows up exponentially (`O(2^B)`) across
  `B` sequential branch diamonds (`23.28 s` / `842 MB` RSS / `7,206` LOC at
  `B = 8`, 256 paths). In addition, `s2n-bignum`'s x86-64 decoder explicitly
  rejects `FS`/`GS` prefixes, `LOCK`, indirect `CALL`/`JMP`, and `DIV`/`IDIV`.
- **Cutpoint symbolic execution** collapses `B`-diamond path explosion from
  `O(2^B)` to `O(B)` (`3.44 s` / `323 MB` RSS for `B = 32`, `4.29 × 10^9` paths),
  but per-instruction stepping over a flat `List Instr` still scales
  superlinearly (`15.56 s` compile, `2.50 s` kernel replay at `N = 400`) and
  hits Lean 4's default `maxRecDepth = 512` ceiling at `N = 800` when
  `set_option` is forbidden.
- **Sharded balanced-tree certified lifting into SSA/functional IR**
  (`CodeTree` of `≤ 64`-instruction leaves with `O(log B)` reflected leaf
  verification + `CutBox` leaf composition) is the only paradigm tested that
  scales linearly to **`N = 5,000` spill-heavy instructions** under default
  `maxRecDepth = 512` and zero `set_option` overrides (`17.49 s` compile,
  `407 MB` RSS, `1.82 MB` `.olean`, `1.84 s` genuine private-level kernel
  replay, axioms `{propext, Quot.sound}`).
- **Compiler-IR verification / translation validation** (CompCert/VST, CN,
  Vellvm/Crellvm, Alive2) either requires replacing GCC/Clang with CompCert (no
  C++, no AVX2, no `-fstack-clash-protection`) or leaves the optimizing backend
  (`llc`/GCC RTL) inside the TCB.
- **Cross-prover certificate replay** (`hol2dk`, OpenTheory) incurs prohibitive
  proof-artifact volume (`3 GB`–`135 GB` proof dumps in `hol2dk` benchmarks) and
  still proves theorems only against the *source* prover's ISA model rather than
  Lean's trusted ISA and Rust `FnAbi` semantics.

Untrusted metadata (`.eh_frame`, DWARF v5, `.BTF`, symbol tables, C headers)
can be consumed safely inside untrusted proof bodies without expanding the TCB
by enforcing **Statement-Origin Separation** (mechanically verified in
`support/HintSeparationProbe.lean`: `0` `UntrustedHints.*` constants in
`ConstantInfo.type`, `6` in `ConstantInfo.value`, `194 ms` private replay,
axioms `{propext, Quot.sound}`). Empirically, `.eh_frame` is the highest-value
structural hint (always emitted on SysV x86-64 even without `-g`), whereas
DWARF v5 live variable coverage drops to `28.6%` of parameters and `12.5%` of
locals (`0%` of C++ locals) once synthetic `DW_OP_entry_value` expressions are
excluded, and `g++ -gbtf` silently emits no `.BTF` section at all.

Finally, on Lean `v4.34.1`, `omega`, `bv_omega`, and `grind` (banned by
Anneal's Pass-1 repository syntax allowlist in `theory/`) replay cleanly
against `Init` in `40–60 ms` and remain strictly inside the 3-axiom ceiling
(`{propext, Classical.choice, Quot.sound}`), making them sound candidates for
isolated sandboxed target-crate proof scripts. By contrast, `bv_decide`
(`Std.Tactic.BVDecide`) injects per-theorem native-reflection axioms
(`<thm>._native.bv_decide.ax_1`) on non-trivial bitvector VCs, violating the
3-axiom ceiling regardless of isolation.

## Applicability

This report characterizes the verification of **compiler-generated x86-64 ELF
relocatable objects (`.o`/`.a`)** produced from C and C++ FFI code when
targeting a **Lean 4 (`v4.34.1`) kernel-replay verifier** enforcing a closed
three-axiom ceiling (`{propext, Classical.choice, Quot.sound}`), zero
`Lean.ofReduceBool` / `Lean.trustCompiler` reflection axioms, and
Statement-Origin Separation (as instantiated by `joshlf/anneal` at
`c131b320eeeb26ef692e5afd5ec8db49ee518613`).

How the subjects in `REPORT.json` relate:

- **Empirical codegen baseline:** `gcc` and `g++` `15.2.0` (`Debian 15.2.0-14`,
  `x86_64-linux-gnu`), inspected with GNU Binutils `2.47` (`objdump`, `readelf`)
  and Debian LLVM `21.1.8` (`llvm-dwarfdump`) across ten compilation profiles
  on C (`support/ffi_anatomy_suite.c`), C++ (`support/ffi_anatomy_cpp.cpp`),
  and hand-written assembly (`support/handwritten_leaf.S`).
- **Lean 4 kernel & trust-boundary target:** `leanprover/lean4` `v4.34.1`
  (`5045d0056413266e57c625dcd7c365b10e377c52`) and `joshlf/anneal`
  (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), specifically
  `trusted/audit/TrustedBoundary.lean` (`allowedTheoryTacticKinds`,
  `importEnv` with `level := .private`, `base.toKernelEnv.replay`) and
  `docs/trust-model.md`.
- **Comparative machine-code and compiler-IR verification systems:** Direct
  primary-source comparison across `awslabs/s2n-bignum`, `leanprover/LNSym`,
  `HOL-Theorem-Prover/HOL` (decompiler), `seL4/graph-refine`, `ssrg-vt/FoxDec`,
  `rems-project/islaris`, `rems-project/CN2Islaris`, `rems-project/cn`,
  `rems-project/cerberus`, `AbsInt/CompCert`, `snu-sf/crellvm`,
  `vellvm/vellvm`, `AliveToolkit/alive2`, `Deducteam/hol2dk`, and
  `AeneasVerif/kraken`.
- **Empirical Lean 4 proof-scaling & replay probes:** Executed directly on Lean
  `v4.34.1` (`-DElab.async=false -Ddebug.skipKernelTC=false -j1 -M2048`) over
  a self-contained x86-64-like machine semantics (`support/MachineLiftBase.lean`,
  `support/HintSeparationProbe.lean`, `support/bench_lean4_scaling_and_axioms.py`).

Scope qualifications:

- Empirical `.o` measurements apply strictly to `gcc`/`g++` 15.2.0 targeting
  System V AMD64 ELF (`x86_64-linux-gnu`). Clang/LLVM and AArch64 exhibit
  analogous structural phenomena (jump tables in `.rodata`, hot/cold splitting,
  auto-vectorization, TLS canaries, PAC/BTI), though exact instruction idioms,
  relocation types, and DWARF coverage ratios differ (not measured here).
- Empirical Lean 4 timing/memory measurements quantify **control-flow, memory
  framing, code-storage indexing, branch merging, and kernel-replay scaling**
  on an idealized 64-bit register/memory/jump-table/canary machine model; they
  do **not** include the constant-factor cost of full x86-64 byte-level decoding
  and EFLAGS/SIMD semantics (see **Boundaries**).
- This report builds on, without repeating, prior corpus analyses of
  certified lifting towers (`autocorres-vst-everest-certified-lifting-towers-and-rust-mir-transfer`),
  object-level `asm!` lifting (`object-level-asm-lifting-core-arch-llvm-lowering-and-pass2-isa-correspondence`),
  hand-written cryptographic assembly (`jasmin-s2n-bignum-cslib-and-verified-cryptographic-assembly`),
  `Kraken` WP (`kraken-wp-foundation-parser-theorem-closure-and-certificate-checking`),
  cross-prover TCB accounting (`cross-prover-interoperability-verified-checkers-and-tcb-accounting`),
  and Pass-1 syntactic tactic allowlists (`syntactic-tactic-allowlists-reflection-certificates-and-omega-free-isa-correspondence`).

## Findings

### 1. Empirical Anatomy of Compiled C/C++ `.o` Files vs. Hand-Written `.S`

Basis: execution (`support/analyze_ffi_objects.py` + `support/ffi_anatomy_results.json`) + normative (System V AMD64 ABI, ELF x86-64 psABI, Intel CET).

Compiling six representative C FFI archetypes (`support/ffi_anatomy_suite.c`),
one C++ virtual-dispatch/RAII workload (`support/ffi_anatomy_cpp.cpp`), and a
hand-written leaf assembly baseline (`support/handwritten_leaf.S`) with
`gcc`/`g++` 15.2.0 demonstrates a qualitative jump in CFG, relocation, stack,
and ABI complexity between hand-written `.S` and real compiler output.

#### 1.1 Quantitative Comparison Across Hardened Production Codegen

All metrics below are directly measured on `gcc 15.2.0` profile
`c_hardened_O3_avx2` (`-O3 -mavx2 -fPIC -fstack-protector-strong
-fstack-clash-protection -fcf-protection=full -g`), `g++ 15.2.0` profile
`cpp_hardened_O2_exc` (same hardening flags at `-O2`), `cpp_O2_noexc`
(`-O2 -fno-exceptions -fno-rtti -g`), and `asm_handwritten` (`gcc -c`):

| Function (Archetype) | Profile | Section | Bytes | Insns | BBs | Back-Edges | `ret` | `endbr64` | Callee-Saved Pushes | `sub rsp` (B) | `[rsp]` Refs | TLS / Clash / SIMD | Ind. Jmp / Call | Direct / Tail Calls | Relocs (Types) |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: | :---: | :---: | --- |
| `leaf_add_u64` (hand-written `.S`) | `asm_handwritten` | `.text` | 39 | 14 | 5 | 1 | 1 | 1 | 0 | 0 | 0 | 0 / 0 / 0 | 0 / 0 | 0 / 0 | 0 |
| `tlv_parse_checksum` (pointer/buffer loop + spills) | `c_hardened_O3_avx2` | `.text` | 797 | 202 | 15 | 3 | 1 | 1 | 6 (`r12`–`r15`,`rbp`,`rbx`) | 104 | 39 | 0 / 0 / 0 | 0 / 0 | 2 / 0 | 2 (`PLT32`) |
| `opcode_dispatch_16` (16-way `switch`) | `c_hardened_O3_avx2` | `.text` | 540 | 131 | 19 | 15 | 1 | 1 | 0 | 24 | 16 | 0 / 0 / 0 | 1 / 0 | 4 / 0 | 6 (`PC32`, `PLT32`) + 16 `.rela.rodata` |
| `opcode_dispatch_16.cold` (cold split default) | `c_hardened_O3_avx2` | `.text.unlikely` | 12 | 2 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 / 0 / 0 | 0 / 0 | 0 / 1 | 1 (`PC32` into `.text+0x382`) |
| `vec_add_aliased` (3-line loop, no `restrict`) | `c_O2` | `.text` | 60 | 15 | 4 | 1 | 1 | 0 | 0 | 0 | 0 | 0 / 0 / 0 | 0 / 0 | 0 / 0 | 0 |
| `vec_add_aliased` (3-line loop, no `restrict`) | `c_hardened_O3_avx2` | `.text` | 320 | 80 | 24 | 4 | 3 | 1 | 0 | 0 | 0 | 0 / 0 / 6 | 0 / 0 | 0 / 0 | 0 |
| `vec_add_restrict` (3-line loop, `restrict`) | `c_hardened_O3_avx2` | `.text` | 223 | 58 | 16 | 2 | 2 | 1 | 0 | 0 | 0 | 0 / 0 / 6 | 0 / 0 | 0 / 0 | 0 |
| `sibling_tail_dispatch` (direct + indirect tail call) | `c_hardened_O3_avx2` | `.text` | 64 | 19 | 7 | 0 | 1 | 1 | 0 | 0 | 0 | 0 / 0 / 0 | 1 / 0 | 0 / 1 | 1 (`PLT32`) |
| `synth_zero_and_copy` (compiler-synthesized libc) | `c_hardened_O3_avx2` | `.text` | 78 | 25 | 5 | 0 | 0 | 1 | 3 (`r12`,`rbp`,`rbx`) | 0 | 0 | 0 / 0 / 0 | 0 / 0 | 2 / 2 | 4 (`PLT32`: `memset`, `memcpy`, `ext_consume_buf`) |
| `stack_buf_hash_small` (128 B local buf) | `c_hardened_O3_avx2` | `.text` | 880 | 203 | 35 | 20 | 1 | 1 | 3 | 160 | 22 | 2 / 0 / 40 | 0 / 0 | 3 / 0 | 15 (`PC32`, `PLT32`) |
| `stack_buf_hash_large` (8 KiB local buf) | `c_hardened_O3_avx2` | `.text` | 495 | 129 | 25 | 4 | 1 | 1 | 3 | 8224 | 15 | 2 / 2 / 12 | 0 / 0 | 2 / 0 | 3 (`PC32`, `PLT32`) |
| `cpp_codec_invoke` (C++ virtual + RAII, default exc) | `cpp_hardened_O2_exc` | `.text` | 192 | 50 | 10 | 3 | 1 | 2 | 1 | 16 | 2 | 0 / 0 / 0 | 0 / 2 | 1 / 1 | 5 (`PC32`, `PLT32`, `REX_GOTPCRELX`) |
| `cpp_codec_invoke.cold` (exception cleanup) | `cpp_hardened_O2_exc` | `.text.unlikely` | 18 | 4 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 / 0 / 0 | 0 / 0 | 2 / 0 | 2 (`PLT32`: `ext_cpp_log`, `_Unwind_Resume`) |
| `cpp_codec_invoke` (`-fno-exceptions -fno-rtti`) | `cpp_O2_noexc` | `.text` | 192 | 50 | 10 | 3 | 1 | 0 | 1 | 16 | 2 | 0 / 0 / 0 | 0 / 2 | 1 / 0 | 4 (`PC32`, `PLT32`) |

#### 1.2 Seven Compiler-Generated Hazards That Break Hand-Written-`.S` Assumptions

1. **`.rela.rodata` jump-table relocations and cross-section hot/cold CFG
   splitting:** In `opcode_dispatch_16`, GCC emits `cmp edi, 0xf; ja
   .text.unlikely` (`R_X86_64_PC32 .text.unlikely-0x4`), loads the jump-table
   base via `lea rdx, [rip+0x0]` (`R_X86_64_PC32 .rodata-0x4`), fetches a signed
   32-bit offset `movsxd rax, DWORD PTR [rdx+rdi*4]; add rdx, rax`, and jumps
   via `3e ff e2 notrack jmp rdx` (the `0x3e` CET `notrack` prefix suppresses
   IBT `endbr64` enforcement on the 16 case labels). The 64-byte `.rodata`
   section in the unlinked `.o` is **all zeros**; its real case targets exist
   only as 16 `R_X86_64_PC32` entries in `.rela.rodata` targeting `.text +
   case_offset` with offset-adjusted addends `S + A_i - P_i = base(.text) +
   case_i.offset - base(.rodata)`. Simultaneously, `opcode_dispatch_16.cold` in
   `.text.unlikely` executes `mov rax, -1; jmp .text+0x382`, jumping back into
   the middle of `opcode_dispatch_16`'s epilogue. **Implication:** A `.o`
   verifier's trusted image model must capture all code sections (`.text`,
   `.text.*`, `.text.unlikely`) *and* `.rodata` together with `.rela.rodata`
   symbolic relocations, and its CFG closure cannot assume single-section
   function boundaries.
2. **Runtime pointer-aliasing version guards and multi-tail SIMD:** Compiling
   the identical 3-line `for (size_t i = 0; i < n; ++i) dst[i] = a[i] + b[i];`
   loop under `-O3 -mavx2` expands `vec_add_aliased` from 15 instructions / 4
   BBs (`-O2`) to 80 instructions / 24 BBs / 4 back-edges / 3 `ret` exits. GCC
   emits two modular unsigned overlap checks (`(dst - 4) - a <= 24` and
   `(dst - 4) - b <= 24`), a 256-bit `vpaddd ymm` loop, a `vzeroupper`
   transition, a 128-bit `vpaddd xmm` epilog, a scalar tail, and a separate
   scalar alias fallback loop. Even with `restrict`, `vec_add_restrict` still
   emits 58 instructions / 16 BBs / 2 back-edges / 2 `ret` exits.
   **Implication:** Machine-code proofs of `-O3` C loops must discharge modular
   64-bit pointer-wraparound aliasing guards and prove equivalence across
   2–4 specialized loop variants (plus `vzeroupper` AVX/SSE state transition).
3. **Dynamic 32-byte stack realignment (`and rsp, -32`), stack-clash probes,
   and TLS canaries:** In `stack_buf_hash_large` under `c_hardened_O3_avx2`,
   GCC aligns the 8 KiB AVX2 buffer via `and rsp, -32`, making the dynamic
   frame offset `rsp_entry - rsp` symbolic in `{8248, 8256, 8264, 8272}` and
   restoring the stack via `lea rsp, [rbp-0x10]` rather than a constant
   `add rsp, K`. Under `-fstack-clash-protection`, GCC emits two unrolled page
   probes (`sub rsp, 0x1000; or QWORD PTR [rsp], 0x0`) that read-modify-write
   **uninitialized** stack bytes—meaning any ISA memory model that treats reads
   of freshly allocated stack bytes as UB/poison will falsely reject hardened
   GCC frames! Under `-fstack-protector-strong`, GCC reads `fs:0x28`
   (`64 48 8b ...`, FS segment override), stores the canary on the stack,
   compares it at exit, and conditionally invokes `__stack_chk_fail@PLT`.
   **Implication:** The trusted ISA model must support `fs:0x28` TLS state,
   symbolic `and rsp, -32` alignment separation, non-poison uninitialized stack
   slot reads for `or [rsp], 0`, and non-returning failure stubs.
4. **Sibling tail calls and zero-`ret` functions:** `sibling_tail_dispatch`
   terminates via both a direct relocated tail jump (`jmp ext_sink_fn@PLT`,
   `R_X86_64_PLT32`) and an indirect register tail jump (`ff e2 jmp rdx`).
   Worse, in `synth_zero_and_copy`, GCC's `-ftree-loop-distribute-patterns`
   replaces *both* explicit C `for` loops with `call memset@PLT` and tail
   `jmp memcpy@PLT` (plus tail `jmp ext_consume_buf@PLT`), leaving
   **`ret_count = 0`** across the entire function. **Implication:** Function
   postconditions cannot assume termination occurs solely at `ret`; ABI
   verification must model tail-call delegation (transferring the caller's
   return address and postcondition directly to the callee's contract) and
   require compositional specifications for compiler-synthesized runtime symbols
   (`memcpy`, `memset`, `memmove`, `__stack_chk_fail`).
5. **C++ speculative devirtualization, GOT relocations, and exception landing
   pads:** In `cpp_hardened_O2_exc`, `g++ 15.2.0` speculatively devirtualizes
   `codec->process(...)` by comparing `[vptr + 0x10]` against
   `[rip + GOT(_ZNK8XorCodec7processEPKhm)]` (`R_X86_64_REX_GOTPCRELX`),
   inlining `XorCodec`'s body on match and falling back to indirect `call rax`
   otherwise. With default C++ exceptions enabled, `cpp_codec_invoke` gains
   `cpp_codec_invoke.cold` in `.text.unlikely`, `.gcc_except_table`,
   `.data.rel.local.DW.ref.__gxx_personality_v0`, undefined symbols
   `_Unwind_Resume` and `__gxx_personality_v0`, and a **second `endbr64`** at
   offset `0xb4` marking an exception landing pad entered indirectly by the
   unwinder rather than any branch in `.text`. Compiling C++ FFI units with
   `-fno-exceptions -fno-rtti` eliminates all unwinding metadata, `.cold`
   cleanup stubs, and extra landing pads while keeping `cpp_codec_invoke`
   limited to direct/indirect calls.
6. **Hardware CET / SHSTK notes and relocation diversity:** Hardened profiles
   emit `.note.gnu.property` (`x86 feature: IBT, SHSTK`), entry `endbr64`
   instructions, `notrack` prefixes, `R_X86_64_PC32`, `R_X86_64_PLT32`, and
   `R_X86_64_REX_GOTPCRELX`. Every external call/tail-call and `.rodata`
   constant pool reference (`.LC1`, `.LC11`, jump tables) is symbolic in `.o`
   and must be linked/abstracted cleanly in the object-level semantics.
7. **Stack-spill density in real code:** `tlv_parse_checksum` (a modest 55-line
   C parser) saves 6 callee-saved registers, allocates a 104-byte frame, and
   executes 39 `[rsp+...]` memory accesses across 202 instructions and 3
   loops. Any memory model that represents every stack spill as an un-pruned
   nested store over a flat byte-memory map hits catastrophic term blowup
   (quantified in Section 2.1).

---

### 2. Head-to-Head Comparison of Four Machine-Code Proof Architectures in Lean 4

Basis: source (`s2n-bignum`, `LNSym`, `HOL4`, `graph-refine`, `FoxDec`, `Islaris`, `CN2Islaris`, `CompCert`, `Crellvm`, `Vellvm`, `Alive2`, `hol2dk`, `Kraken`, `Anneal`) + execution (`support/bench_lean4_scaling_and_axioms.py`, `support/lean4_scaling_and_axioms_results.json`) + derived.

#### 2.1 Paradigm Summary Matrix (50–5,000 Compiled `.o` Instructions in Lean 4)

| Dimension | 1. Cutpoint Symbolic Execution / VCGen | 2. Certified Lifting to SSA/Functional IR | 3. Compiler-IR Verification / Translation Validation | 4. Cross-Prover Proof / Certificate Replay |
| --- | --- | --- | --- | --- |
| **Representative systems** | `s2n-bignum` (`ENSURES_TAC`), `LNSym`, `Islaris`, `Kraken` WP | HOL4 decompiler (`decompilerLib`), `AutoCorres`, `FoxDec`, `seL4/graph-refine`, `ShardedTreeLift` | `CompCert` + `VST`, `CN`/`Cerberus`, `Crellvm`/`Vellvm`, `Alive2` | `hol2dk` (HOL Light → Dedukti/Rocq), OpenTheory, Lean certificate checkers |
| **TCB impact (under Lean 4 3-axiom replay)** | Minimal: Lean kernel + `Trusted` ISA + ELF/reloc + `FnAbi`. | Minimal (identical to #1): lifter & SSA IR live in untrusted `theory/`; backward simulation `Abstracts` is kernel-checked. | **Large or restrictive:** CompCert adds CompCert C/ASM semantics & excludes C++/AVX2/hardening; LLVM IR TV (`Crellvm`/`Alive2`) leaves `llc` backend lowering in TCB. | **Unchanged or larger** unless Lean proves semantic equivalence between foreign ISA model and `Trusted` ISA + `FnAbi` (otherwise foreign ISA enters TCB). |
| **Compiled C/C++ `.o` readiness** | Poor on un-pruned stepping (`s2n-bignum` decoder rejects `FS`, indirect `JMP`/`CALL`, `DIV`/`IDIV`); viable only with cutpoint merging + frame pruning. | **Best fit for 200–5,000 insns:** isolates ISA decode, stack-spill promotion, and jump-table resolution into a 1-pass certified front-end; functional/loop proofs run on clean SSA IR. | High source productivity for C (`VST`, `CN`), but breaks on GCC/Clang `-O3`/AVX2/hardening or C++ unless paired with binary TV (`seL4/graph-refine`, `CN2Islaris`). | Covers only existing libraries verified in foreign provers (mostly hand-written crypto `.S`, not arbitrary compiled C/C++ `.o`). |
| **Scaling bottleneck in Lean 4 (`v4.34.1`)** | Un-pruned `let`-chains hit `200,000`-heartbeat timeout at `N = 40`; uncut branches blow up `O(2^B)`; flat-`List` `Cutpoint20` is `O(N^2)` and hits `maxRecDepth = 512` at `N = 800`. | Flat-`List` single-shot lifting hits `maxRecDepth = 512` at `N = 200`. **Balanced `CodeTree` (`≤ 64`-insn leaves) scales linearly to `N = 5,000`** (`17.49 s`, `1.84 s` replay). | `Alive2` hits SMT timeouts on loops and unverified lowering; `CompCert` lacks C++/SIMD; `graph-refine` notes GCC `-O2` loop unrolling stresses SMT search. | Proof-object size explosion (`hol2dk`: `3 GB` for `hol.ml`, `135 GB` / `21 h 14 m` on 32 cores for `make_complex.ml`) + ISA semantic bridge cost. |
| **Satisfies 3-axiom ceiling `{propext, Classical.choice, Quot.sound}`?** | Yes if avoiding `bv_decide` (note: `LNSym` uses `bv_decide`, which violates it). | **Yes** (`{propext, Quot.sound}` in `ShardedTreeLift` benchmark). | CompCert/VST/Crellvm are Rocq-native (not Lean 4); `Alive2`/`CN`/`graph-refine` rely on external SMT solvers (`Z3`/`Bitwuzla`) without 3-axiom Lean replay. | Theoretically yes via proof-term translation, practically blocked by gigabyte-scale replay and foreign ISA mismatch. |

#### 2.2 Empirical Lean `v4.34.1` Scaling & Replay Measurements

All experiments ran synchronously on `leanprover/lean4` `v4.34.1`
(`-DElab.async=false -Ddebug.skipKernelTC=false -j1 -M2048`), with **zero**
`set_option` overrides (matching Anneal Pass-1 fixed `maxRecDepth = 512` and
`maxHeartbeats = 200000`), followed by standalone private-level kernel replay
(`importModules ... (trustLevel := 0) (plugins := #[]) (loadExts := false)
(level := .private)` + `base.toKernelEnv.replay`, asserting non-dummy private
proof bodies) in `support/bench_lean4_scaling_and_axioms.py`.

##### Experiment 1: Register-Spill & Memory-Framing Scaling (`N = 8..5,000` Instructions)

Workload: alternating 4-instruction cycles (`addImm .rax k; spillStore slot
.rax; xorReg .rdi .rax; spillLoad .rax slot`) modeling GCC register-spill
density while proving `pc = N`, no fault/halt, `rsp` preservation, and exact
heap-framing (`∀ addr ∉ stackFrame, sf.mem addr = s.mem addr`). Four regimes
were benchmarked against the same `MachineLiftBase.lean` (`2.54 s`, `1.95 MB`
`.olean`):

1. **`DirectSym` (un-pruned `let`-chain symbolic stepping):** Models naive
   step-by-step symbolic execution over `MState`.
2. **`Cutpoint20` (flat `List Instr`, 20-instruction `CutBox` windows):**
   Wraps each 20-instruction boundary invariant in an opaque `CutBox` structure
   (`structure CutBox (tag : Nat) (P : Prop) : Prop where val : P`) and applies
   per-instruction Hoare stepping lemmas so nested `let` zeta-blowup is avoided.
3. **`FlatCertLift` (flat `List Instr`, single-shot reflected `checkDropLift_sound`):**
   Checks the entire block's liftability and bytecode match in one `rfl` pass
   and applies a universal backward-simulation soundness theorem to lift
   machine steps to pure functional `evalLiftedBlock`.
4. **`ShardedTreeLift` (balanced binary `CodeTree` of `≤ 64`-insn leaves):**
   Stores code in `CodeTree` (`depth ≤ 7` at `N = 5,000`), verifies each
   `≤ 64`-instruction leaf via `O(log B + |blk|)` `checkLeafAt` (`rfl`), and
   composes leaves via `CutTreeInv` + `runTree_add`.

| `N` (Insns) | Regime | Status (`rc`) | Source LOC | Compile Wall (s) | Compile CPU (s) | Peak RSS (MB) | `.olean` (B) | Private Replay (ms) | Replayed Consts | Axioms |
| ---: | --- | :---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 8 | `DirectSym` | 0 | 87 | 0.30 | 0.29 | 279.4 | 97,184 | 178 | 461 | `propext`, `Quot.sound` |
| 16 | `DirectSym` | 0 | 133 | 1.82 | 1.81 | 279.9 | 153,296 | 132 | 461 | `propext`, `Quot.sound` |
| 24 | `DirectSym` | 0 | 180 | 4.93 | 4.93 | 286.5 | 202,936 | 142 | 461 | `propext`, `Quot.sound` |
| 32 | `DirectSym` | 0 | 226 | 10.33 | 10.32 | 292.0 | 252,536 | 203 | 461 | `propext`, `Quot.sound` |
| **40** | **`DirectSym`** | **1 (FAIL)** | 272 | 17.48 | 17.44 | 284.0 | 0 | — | — | `whnf` timeout (`200,000` heartbeats) |
| 40 | `Cutpoint20` | 0 | 163 | 0.46 | 0.45 | 279.4 | 216,392 | 211 | 468 | `propext`, `Quot.sound` |
| 40 | `FlatCertLift` | 0 | 73 | 0.30 | 0.29 | 277.2 | 134,104 | 142 | 463 | `propext`, `Quot.sound` |
| 40 | `ShardedTreeLift` | 0 | 55 | 0.45 | 0.44 | 277.3 | 161,896 | 157 | 466 | `propext`, `Quot.sound` |
| 100 | `Cutpoint20` | 0 | 310 | 1.78 | 1.75 | 287.4 | 367,792 | 324 | 471 | `propext`, `Quot.sound` |
| 100 | `FlatCertLift` | 0 | 133 | 0.40 | 0.39 | 277.2 | 233,560 | 191 | 463 | `propext`, `Quot.sound` |
| 100 | `ShardedTreeLift` | 0 | 61 | 0.85 | 0.83 | 281.5 | 267,464 | 179 | 469 | `propext`, `Quot.sound` |
| 200 | `Cutpoint20` | 0 | 555 | 5.27 | 5.22 | 297.9 | 588,608 | 768 | 476 | `propext`, `Quot.sound` |
| **200** | **`FlatCertLift`** | **1 (FAIL)** | 233 | 0.37 | 0.36 | 269.2 | 0 | — | — | `maxRecDepth = 512` (`checkDropLift`) |
| 200 | `ShardedTreeLift` | 0 | 73 | 1.24 | 1.23 | 283.4 | 362,248 | 189 | 475 | `propext`, `Quot.sound` |
| 400 | `Cutpoint20` | 0 | 1,045 | 15.56 | 15.52 | 322.7 | 1,031,256 | 2,496 | 486 | `propext`, `Quot.sound` |
| 400 | `ShardedTreeLift` | 0 | 91 | 1.81 | 1.78 | 286.7 | 556,800 | 349 | 484 | `propext`, `Quot.sound` |
| **800** | **`Cutpoint20`** | **1 (FAIL)** | 2,025 | 22.18 | 22.08 | 331.3 | 0 | — | — | `maxRecDepth = 512` (`listGet?`) |
| 800 | `ShardedTreeLift` | 0 | 127 | 3.40 | 3.37 | 300.9 | 961,320 | 427 | 502 | `propext`, `Quot.sound` |
| 1,600 | `ShardedTreeLift` | 0 | 199 | 6.53 | 6.47 | 322.6 | 1,356,944 | 875 | 538 | `propext`, `Quot.sound` |
| 3,200 | `ShardedTreeLift` | 0 | 349 | 13.61 | 13.57 | 362.5 | 1,559,040 | 1,198 | 613 | `propext`, `Quot.sound` |
| **5,000** | **`ShardedTreeLift`** | **0** | **523** | **17.49** | **17.41** | **406.7** | **1,816,216** | **1,842** | **700** | `propext`, `Quot.sound` |

Three decisive architectural findings emerge from Experiment 1:

1. **Flat-list code storage hits a hard `maxRecDepth = 512` wall when
   `set_option` is forbidden:** Both `FlatCertLift` (at `N = 200`, inside
   `checkDropLift`) and `Cutpoint20` (at `N = 800`, inside `listGet? img.code
   pc` as `pc` approaches 512) fail with `maximum recursion depth has been
   reached`. Even before failing, `Cutpoint20` exhibits `O(N^2)` compile and
   replay cost because `listGet?` scans `O(pc)` cons cells on every instruction.
2. **Balanced binary-tree code storage (`CodeTree`) + leaf-sharded certified
   lifting achieves strict `O(N)` scaling to 5,000 instructions:** At `N = 400`,
   `ShardedTreeLift` is `8.6×` faster to compile (`1.81 s` vs. `15.56 s`) and
   `7.15×` faster to kernel-replay (`349 ms` vs. `2,496 ms`) than `Cutpoint20`.
   At `N = 5,000` (79 leaves of `≤ 64` instructions, tree depth 7),
   `ShardedTreeLift` compiles in `17.49 s` (`3.50 ms/insn`), uses `407 MB` RSS,
   produces a `1.82 MB` `.olean` (`363 B/insn`), and replays through the
   standalone kernel in **`1.84 s`**—`1.35×` *faster* than `Cutpoint20`
   replaying only `400` instructions (`2.50 s`). This mirrors the canonical
   binary-trie memory insight from `canonical-extensional-binary-tries-for-lean4-verified-memory-and-heap-models`:
   logarithmic-depth persistent trees are mandatory for both code and memory
   under fixed kernel recursion bounds.
3. **Why `LNSym` needs custom metaprogramming where certified lifting does not:**
   In `leanprover/LNSym@49f8a1d9e4`, direct symbolic simulation of even a
   straight-line unrolled 32-round SHA-512 block requires `5,543` LOC
   (`365.9 KB`) in `Proofs/SHA512/SHA512LoopBlocks.lean`, `44.8 KB` of custom
   state-pruning metaprogramming (`Tactics/PruneUpdates.lean`), `13 KB` of
   `CSE.lean`, and `bv_decide`. Certified lifting eliminates per-instruction
   proof-term bloat by factoring decoding and stack-slot promotion into a
   single-pass reflected checker (`checkLeafAt`) proved sound once.

##### Experiment 2: Branch-Diamond Path Explosion (`Uncut` vs. `Cutpoint`)

Workload: `B` sequential conditional branch diamonds (`jzBit0 .rdi` choosing
between two 3-step arms that reconverge at `5*(d+1)`), creating `2^B` distinct
control-flow paths.

| `B` (Diamonds) | Paths (`2^B`) | Regime | LOC | Compile Wall (s) | Compile CPU (s) | Peak RSS (MB) | `.olean` (B) | Private Replay (ms) |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 16 | `Uncut` | 466 | 1.05 | 1.04 | 297.1 | 150,208 | 254 |
| 6 | 64 | `Uncut` | 1,820 | 5.40 | 5.38 | 425.3 | 257,552 | 426 |
| **8** | **256** | **`Uncut`** | **7,206** | **23.28** | **23.25** | **841.8** | **557,088** | **1,859** |
| 4 | 16 | `Cutpoint` | 162 | 0.39 | 0.37 | 281.8 | 136,848 | 136 |
| 6 | 64 | `Cutpoint` | 230 | 0.48 | 0.47 | 281.4 | 181,184 | 161 |
| **8** | **256** | **`Cutpoint`** | **298** | **0.74** | **0.73** | **289.3** | **226,576** | **163** |
| 16 | 65,536 | `Cutpoint` | 570 | 1.33 | 1.32 | 299.1 | 404,928 | 315 |
| **32** | **4,294,967,296** | **`Cutpoint`** | **1,114** | **3.44** | **3.43** | **323.4** | **761,632** | **625** |

At just `B = 8` (256 paths—smaller than the 24–35 BBs of a single `-O3`
auto-vectorized function), cutpoint merging is **`31.5×` faster to compile**,
**`11.4×` faster to kernel-replay**, **`2.9×` smaller in peak RSS**, and
**`24.2×` shorter in LOC**, scaling cleanly to `B = 32` (`4.29 × 10^9` paths)
in `3.44 s` and `625 ms` replay.

#### 2.3 Primary-Source Limitations of Paradigms 1, 3, and 4 on Compiled `.o`

- **Cutpoint symbolic execution (`s2n-bignum`, `Islaris`, `Kraken`):**
  - `awslabs/s2n-bignum@280a220986` (`x86/proofs/decode.ml:90-93, 438-445`)
    explicitly returns `NONE` on `0x64` (`FS` segment prefix, breaking
    `-fstack-protector-strong`), `0x65` (`GS`), `0xf0` (`LOCK`), `0x67`
    (address-size override), indirect `CALL`/`JMP` (`(T,T,2)`/`(T,T,4)`,
    breaking jump tables, indirect tail calls, and C++ virtual calls), and
    `DIV`/`IDIV` (`F,_,6`/`7`, used in `opcode_dispatch_16` cases 7 and 13).
  - `rems-project/islaris@c978e10f50` achieves authoritative Sail ISA fidelity
    (AArch64 / RISC-V) via Iris separation logic in Rocq over straight-line
    symbolic traces (`isla-footprint`), but relies on user-supplied cutpoints
    and targets systems stubs (hundreds of instructions) rather than Lean 4
    kernel replay.
- **Verified decompilation / certified lifting (`HOL4`, `FoxDec`, `seL4/graph-refine`):**
  - `HOL-Theorem-Prover/HOL@1c803b0f54` (`examples/machine-code/decompiler/decompilerLib.sml`)
    performs 4-stage proof-producing decompilation: (1) instruction-level Hoare
    triple derivation, (2) CFG/loop grouping into tail-recursive functional HOL
    definitions, (3) composition of step theorems into a whole-function Hoare
    triple, and (4) hiding intermediate PCs/flags. The exact proof obligations
    required when transplanting this pattern into Lean 4 untrusted `theory/`
    (with a kernel-checked `Abstracts` backward simulation to `Trusted` ISA)
    are: (a) **CFG and jump-table closure** (proving every indirect `jmp`
    target resolves via `.rela.rodata` within verified code bounds), (b)
    **stack-frame separation from heap** (proving callee stack slots—including
    symbolic `and rsp, -32` realigned frames—are disjoint from caller heap
    pointers and restored on exit), (c) **calling-convention framing**
    (callee-saved register preservation + tail-call delegation), and (d)
    **loop-cutpoint / multi-version equivalence** (linking auto-vectorized
    main/epilog/scalar-fallback loops back to one functional specification).
  - `ssrg-vt/FoxDec@d9206efe59` (Isabelle/HOL, PLDI 2022 / CCS 2024) demonstrates
    that sound x86-64 lifting of real GCC binaries requires symbolic pointer
    aliasing bounds and explicit `.rodata`/PIC symbolization; `seL4/graph-refine@33d94bbdd6`
    (`stack_logic.py`, `search.py`) automates matching C/SIMPL against GCC-compiled
    binary graphs via `QF_ABV` SMT, explicitly noting that `-O2` loop unrolling
    remains computationally expensive and that SMT validity is trusted rather
    than replayed in a 3-axiom proof kernel.
- **Compiler-IR verification / translation validation (`CompCert`+`VST`, `CN`, `Crellvm`/`Vellvm`, `Alive2`):**
  - `AbsInt/CompCert@2685140bf7` eliminates backend miscompilation for C99/C11
    via a Rocq-verified compiler, but provides no C++, no AVX2 auto-vectorization,
    no `-fstack-clash-protection`, and proves theorems against CompCert's
    memory/assembly model rather than linking arbitrary GCC/Clang `.o` files.
  - `snu-sf/crellvm@668249b887` (`coq/proof/Adequacy.v` over `vellvm/vellvm@7f0610c38d`)
    mechanizes relational Hoare-logic translation validation for LLVM IR passes
    (with incomplete proofs in `TODOProof.v`), while `AliveToolkit/alive2@3bdd4f5e1c`
    uses unverified SMT checks on bounded LLVM IR. Neither verifies LLVM's
    `SelectionDAG`/`GlobalISel`/MachineIR lowering (`llc`) to x86-64 `.o`
    machine bytes, leaving the entire backend inside the TCB.
  - `rems-project/cn@f2e8eeb471` (built on `rems-project/cerberus@e29a8ec9f2`)
    verifies C source via refinement types and SMT, leaving the C compiler
    trusted unless bridged to binary level (see `CN2Islaris` in Section 3).
- **Cross-prover certificate replay (`hol2dk`, OpenTheory):**
  - `Deducteam/hol2dk@7f0da9630e` (`README.md:208-215`) documents the exact
    cost of replaying HOL Light proof dumps into Rocq via Dedukti/Lambdapi:
    exporting base `hol.ml` (`5,687` theorems, `3M` steps) produces a **`3 GB`**
    dump → `1 GB` `.v` files → `10 m 23 s` `coqc -j32`; exporting
    `Multivariate/make_complex.ml` (`40,728` theorems, `85M` steps) produces a
    **`135 GB`** dump → `91 GB` `.v` files → **`21 h 14 m`** on 32 cores with
    128 GB RAM.
  - Even if a comparable Lean 4 replayer ingested `s2n-bignum` HOL Light proofs
    or `Jasmin`/EasyCrypt/`VST` Rocq proofs, replay alone yields a theorem
    quantified over the **foreign prover's ISA/memory definition**—requiring a
    full Lean 4 semantic correspondence proof bridging the foreign ISA to
    Lean's `Trusted` ISA + Rust `FnAbi` before the imported theorem can discharge
    a Rust FFI obligation without enlarging the TCB (matching the TCB accounting
    in `cross-prover-interoperability-verified-checkers-and-tcb-accounting`).

---

### 3. Untrusted Structural Hints (`.eh_frame`, DWARF v5, `.BTF`, Headers, Symbol Tables) Without Expanding the TCB

Basis: execution (`support/ffi_anatomy_results.json`, `support/HintSeparationProbe.lean`, `support/lean4_scaling_and_axioms_results.json`) + source (`rems-project/CN2Islaris`, `joshlf/anneal`).

#### 3.1 Empirical Fidelity & Availability of Compiler Metadata in GCC/G++ 15.2.0

| Metadata Source | Emitted Without `-g`? | Observed Size (`c_O2` / `c_hardened_O3_avx2` / `cpp_hardened_O2_exc`) | What It Reliably Supplies as Untrusted Hints | Observed Gaps & Failure Modes |
| --- | :---: | --- | --- | --- |
| **`.eh_frame` (CIE/FDE CFA)** | **Yes (always on SysV x86-64)** | `360 B` (`9` FDEs, `49` CFA rows) / `408 B` (`9` FDEs, `41` rows, `6` `rbp` rows) / `232 B` (`5` FDEs, `9` rows) | Exact hot + `.cold` function PC ranges, CFA frame sizes (`rsp+8..rsp+160`), switch to frame-pointer CFA (`rbp+16`) under `and rsp, -32`, and exact callee-saved restore offsets (`rbx@c-56..r15@c-16, ra@c-8`). | Does not encode lower stack-frame bounds under `and rsp, -32`, stack-clash probe counts, or local variable types; `.cold` stubs require cross-FDE pairing. |
| **`.symtab` + `.rela.*`** | **Yes** (unless stripped) | `648 B` `.symtab` + `432 B` `.rela.text` + `384 B` `.rela.rodata` (`c_O2`) | Function entry symbols, `.cold` split symbols, undefined external callees (`memcpy`, `memset`, `__stack_chk_fail`), and exact `.rodata` jump-table target relocations (`16` `R_X86_64_PC32`). | Stripping removes `.symtab` (local symbols); `.rela.*` remains mandatory in relocatable `.o` files. |
| **DWARF v5 (`.debug_*`)** | No (`-g` required) | `9,737 B` / `11,646 B` / `8,541 B` (`~6–8×` `.BTF`) | Parameter and local names, C/C++ types, source line-to-PC maps (loop-header candidate discovery), inlined call-site DIEs (`10` inlined functions in C++). | **Severe live-location erosion under optimization:** In `c_hardened_O3_avx2`, `28/28` params show 100% coverage *only* via `73` synthetic `DW_OP_entry_value` + `106` `DW_OP_stack_or_implicit_value` expressions; excluding `DW_OP_entry_value`, only **`8/28` (`28.6%`)** params and **`4/32` (`12.5%`)** locals have 100% live coverage (`12,092/18,230 B` = `66.3%` scope bytes). In `cpp_hardened_O2_exc`, only **`10/38` (`26.3%`)** processed params (excl. entry values) and **`0/9` (`0%`)** locals have 100% live coverage. |
| **`.BTF` (`-gbtf`)** | No (`-gbtf` required) | `1,543 B` (`c_O2_btf`: `10` `FUNC`, `11` `FUNC_PROTO`, `4` `RESTRICT`, `6` `PTR`, `10` `TYPEDEF`, `10` `INT`) / **`0 B` (`cpp_O2_btf`)** | Compact (`~6.3×` smaller than DWARF) machine-readable C function prototypes, `restrict` qualifiers, and struct/typedef layouts—superior to parsing raw C headers. | Zero PC-to-register locations, zero stack-frame offsets, zero loop cutpoints; **`g++ 15.2.0 -O2 -gbtf` exits `0` while silently emitting NO `.BTF` section at all**. |
| **C/C++ Headers (`.h`)** | External | Source text | Human-level FFI signatures and `const`/`restrict` intent for drafting specs. | Preprocessor/ABI-flag fragile (`#ifdef`, struct packing, `long` width); cannot be trusted in theorem statements without checking raw Rust `FnAbi` register/stack bindings. |

#### 3.2 Zero-TCB Hint Architecture: Statement-Origin Separation

External metadata can guide untrusted proof synthesis without entering the TCB
if and only if every hint is **validated against raw `.o` machine bytes inside
the proof term** and **excluded from the locked theorem statement**:

1. **Trusted theorem surface (TCB):** Quantifies exclusively over the captured
   `.o` object image (`.text*` + `.rodata` + symbolic relocations), the
   `Trusted` ISA transition relation (`run`), and the Rust caller's `FnAbi`
   contract (entry registers `rdi`/`rsi`..., return register `rax`, callee-saved
   preservation, `rsp` balance, and heap disjointness). Zero DWARF, `.eh_frame`,
   `.BTF`, or C-header constants may appear in `ConstantInfo.type`.
2. **Untrusted hint extraction & proof-body consumption (outside TCB):** An
   offline extractor parses `.eh_frame` CFA tables, `.rela.rodata` jump tables,
   DWARF line/location hints (analogous to `rems-project/CN2Islaris@f34f9a2f0a`'s
   use of `read-dwarf`, which currently supports only loop-free `unsigned long`
   AArch64 functions), and `.BTF` prototypes into a pure data certificate
   (`UntrustedHints.HintCert`). A reflected checker (`checkHintCert img h = true`)
   discharges bytecode, prologue/epilogue CFA offset, canary slot, and 16-way
   jump-table case matching inside the proof body via `rfl`.
3. **Mechanized verification in `support/HintSeparationProbe.lean`:**
   - Models a 43-instruction compiled 16-case switch with `-fstack-protector-strong`
     (`subRsp 32`, `loadCanary .r10`, `spillStore 3 .r10`, `jmpTable .rdi 16 0
     36`, 16 case blocks, `.text.unlikely` default block, `cmpCanary 3 42`,
     `addRsp 32`, `ret`, `__stack_chk_fail` trap).
   - Compiles on Lean `v4.34.1` in `0.83 s` (`298.9 MB` RSS, `555,864 B`
     `.olean`).
   - Standalone private-level kernel replay (`trustLevel := 0`, `loadExts :=
     false`, `level := .private`) succeeds in **`194 ms`** (`500` replayed
     constants, axioms `{propext, Quot.sound}`) and mechanically confirms:
     - **`type_hints = 0`** (zero `UntrustedHints.*` constants reachable from
       `LockedObligation.verify_compiled_dispatch_abi`'s type);
     - **`val_hints = 6`** (`UntrustedHints.*` hint certificate and soundness
       lemmas genuinely consumed inside the private proof term, with
       `_inhabitedExprDummy` confirmed absent).
   - **Fail-closed guarantee:** Corrupting any DWARF/`.eh_frame` hint (e.g.,
     wrong CFA size, canary slot, or jump-table bound) merely causes
     `checkHintCert img h = true` (`rfl`) to fail to typecheck; it can never
     weaken or falsify `verify_compiled_dispatch_abi`.

---

### 4. Target-Crate vs. Repository-Theory Proof Budgets in Lean 4 (`v4.34.1`)

Basis: source (`joshlf/anneal@c131b320ee:trusted/audit/TrustedBoundary.lean:529-575`, `docs/trust-model.md:52-95, 240-315`) + execution (`support/bench_lean4_scaling_and_axioms.py`, `support/lean4_scaling_and_axioms_results.json`).

In `joshlf/anneal`, repository-level `theory/` and `correspondence/` modules
are audited by `TrustedBoundary.lean` under **two distinct layers of control**:
(1) a **syntactic preflight allowlist** (`allowedTheoryTacticKinds`, 37 syntax
node kinds excluding `omega`, `bv_omega`, `grind`, `bv_decide`, `native_decide`,
`decide!`, `rfl'`, `set_option`, `macro`, `elab`, `syntax`, `initialize`),
designed to prevent adversarial compile-time metaprogramming in CI without full
elaborator sandboxing, and (2) **kernel-level audit + replay** against the
locked `Init` foundation enforcing the 3-axiom ceiling `{propext,
Classical.choice, Quot.sound}` and forbidding `unsafe`, `partial`, `opaque`,
and `Lean.ofReduceBool` / `Lean.trustCompiler`.

By contrast, an **isolated target-crate proof** (proving obligations for a
specific linked C/C++ `.o` function inside a sandboxed elaboration step before
standalone `trustLevel := 0, loadExts := false, level := .private` kernel
replay) faces a fundamentally different trade-off: elaborator complexity does
not enter the TCB *provided* the resulting `.olean` replays cleanly through the
standalone kernel within the 3-axiom ceiling and locked foundation.

#### 4.1 Empirical Benchmark of Five Tactic Regimes on Four Real Compiled-Code VCs

All five modules discharge the same four verification conditions extracted from
the GCC 15.2.0 objects in Section 1:

- `vc1_stack_heap_disjoint`: stack-frame vs. heap-buffer address disjointness;
- `vc2_jumptable_bound`: `cmp edi, 15; ja default` → `op.toNat < 16`;
- `vc3_avx2_alias_lane`: GCC `-O3 -mavx2` runtime overlap guard `(24#64 < (dst - 4#64) - a) → dst ≠ a + 4#64`;
- `vc4_cfa_rsp_roundtrip`: CFA stack restoration `(rsp - 160#64) + 160#64 = rsp`.

| Module / Tactic Regime | Allowed in Anneal Pass-1 `theory/`? | Compile Wall / CPU (s) | Peak RSS (MB) | `.olean` (B) | Private Replay Base / Time / Consts | Transitive Axioms (`all_vcs`) | Inside 3-Axiom Ceiling? |
| --- | :---: | :---: | ---: | ---: | --- | --- | :---: |
| `Budget_Pass1_Explicit` (`rw`/`decide`/term lemmas) | **Yes** | 0.20 / 0.19 | 265.5 | 31,344 | `Init` / **2 ms** / 5 | `propext` | **Yes** |
| `Budget_Target_Omega` (`omega`) | No (syntax allowlist) | 0.51 / 0.50 | 488.0 | 212,384 | `Init` / **60 ms** / 10 | `propext`, `Quot.sound` | **Yes** |
| `Budget_Target_BvOmega` (`bv_omega`) | No (syntax allowlist) | 0.51 / 0.50 | 487.4 | 188,344 | `Init` / **56 ms** / 9 | `propext`, `Quot.sound` | **Yes** |
| `Budget_Target_Grind` (`grind`) | No (syntax allowlist) | 0.52 / 0.51 | 490.6 | 111,920 | `Init` / **40 ms** / 9 | `Classical.choice`, `propext`, `Quot.sound` | **Yes** |
| `Budget_Target_BvDecide` (`bv_decide` via `Std.Tactic.BVDecide`) | No (syntax + axiom + `Std` import) | 0.73 / 0.63 | 683.5 | 842,408 | `Std.Tactic.BVDecide` / 17,043 ms / 11,363* | `Classical.choice`, `propext`, `Quot.sound`, **`vc1._native.bv_decide.ax_1`**, **`vc2._native.bv_decide.ax_1`**, **`vc3._native.bv_decide.ax_1`** | **NO (FAIL)** |

\* Note on `Budget_Target_BvDecide` replay count: `Budget_Target_BvDecide`
implicitly imports the full `Init` umbrella (no `prelude`) alongside
`Std.Tactic.BVDecide`, whereas `Std.Tactic.BVDecide` imports only selective
`Init.*` submodules; the `11,363` constants replayed include the `Init` subset
not transitively imported by `Std.Tactic.BVDecide`. More importantly, per-VC
`#print axioms` inspection confirms that `vc1`, `vc2`, and `vc3` each introduce
a distinct `_native.bv_decide.ax_1` native-reflection axiom (only `vc4` stays
within `{propext, Classical.choice, Quot.sound}` because `bv_decide`'s
algebraic preprocessor discharges `(rsp - 160) + 160 = rsp` without invoking
native LRAT checking).

#### 4.2 Concrete Target-Crate vs. Repository-Theory Budget Guidance

1. **Repository `theory/` (shared certified lifter, `CodeTree` lemmas, ABI
   combinators):** Keep strictly inside Pass-1 `allowedTheoryTacticKinds` and
   default `maxRecDepth = 512` / `maxHeartbeats = 200000` (zero `set_option`).
   Because `Budget_Pass1_Explicit` compiles in `0.20 s` (`31 KB` `.olean`,
   `2 ms` replay) and `ShardedTreeLift` scales to `5,000` instructions within
   default limits, core lifting infrastructure does **not** require loosening
   Pass-1 repository rules.
2. **Isolated target-crate proofs (per-`.o` function verification):** Under an
   OS-sandboxed elaboration phase followed by mandatory standalone private
   kernel replay (`trustLevel := 0`, `plugins := #[]`, `loadExts := false`,
   `level := .private`) + 3-axiom check + Statement-Origin Separation:
   - **Admitting `omega`, `bv_omega`, and `grind`** is **sound under the
     3-axiom ceiling** (empirically verified: `40–60 ms` replay against `Init`,
     `112–212 KB` `.olean`, `~490 MB` RSS, zero non-standard axioms) and
     dramatically reduces manual proof effort on GCC modular pointer-aliasing
     guards (`vc3`) and jump-table/stack arithmetic (`vc1`, `vc2`).
   - **`bv_decide` MUST remain rejected** under any 3-axiom kernel-replay gate
     because Lean `v4.34.1` discharges non-trivial bitvector VCs via native
     LRAT checker reflection (`_native.bv_decide.ax_*`), placing the C++/Rust
     compiled Lean runtime and native LRAT verifier inside the TCB.
   - **External SMT certificates (`cvc5`/`z3` + proof-reconstructing tactics):**
     Only admissible if the tactic reconstructs a genuine Lean kernel proof term
     passing `base.toKernelEnv.replay` with zero extra axioms (never oracle
     axioms or `Lean.ofReduceBool`) and executes inside the elaboration sandbox.
   - **Memory and `.olean` replay budgets:** A single 5,000-instruction lifted
     function requires `~407 MB` compile RSS and `~1.82 MB` `.olean`, while
     batch private-level replay of 32 modules in one Lean process peaked at
     `8.51 GB` RSS (`44.4 s` total) because Lean retains imported module data
     across a process. Production verifiers auditing large C/C++ static
     libraries (`.a`) should shard functions into per-function or per-TU Lean
     modules and replay them in bounded-memory worker batches (e.g., `-M2048`
     to `-M4096` per worker) rather than accumulating all modules in a single
     long-lived replay process.
   - **Audit subtlety confirmed directly on Lean `v4.34.1`:** Importing `.olean`
     files with default `level := .exported` replaces theorem proof bodies with
     `_inhabitedExprDummy`, silently hiding proof-body constants and weakening
     inspection. Standalone replay auditors MUST pass `(level := .private)`,
     call `env.setExporting false`, read theorem bodies with
     `ConstantInfo.value? (allowOpaque := true)`, reject `_inhabitedExprDummy`,
     and explicitly check `unsafe`/`partial` flags (since `Lean.Replay`
     silently skips `unsafe` and `partial` constants; see
     `TrustedBoundary.lean:1109-1116`).

## Boundaries

- **Full x86-64 ISA decode and EFLAGS/AVX2 constant factors — `not examined` in
  Lean 4 execution:** `support/MachineLiftBase.lean` models a simplified
  64-bit register/memory/jump-table/canary ISA (`Instr` inductive with 16
  constructors) rather than raw x86-64 variable-length ModRM/SIB/REX/VEX
  instruction bytes, EFLAGS parity/carry/overflow flags, or 256-bit `ymm` lane
  semantics. While the *asymptotic* cliffs (`O(2^B)` uncut branches, `O(N^2)`
  flat-list indexing, `maxRecDepth = 512` wall, and `O(N)` `CodeTree` scaling)
  transfer directly to a full x86-64 model, real per-instruction elaboration
  and kernel-replay constants will be higher and will require an additional
  certified byte-to-abstract-instruction decode table (similar to `CodeTree`
  sharded byte chunks) to avoid blowing `maxHeartbeats` on instruction decoding.
- **Clang/LLVM and AArch64 `.o` codegen profiles — `not examined`:** All
  empirical `.o` disassembly and DWARF/BTF measurements were collected on
  `gcc`/`g++ 15.2.0` targeting `x86_64-linux-gnu`. Clang/LLVM's jump-table
  layout, DWARF `DW_OP_entry_value` ratios, `-gbtf` behavior on C++, and
  AArch64 PAC/BTI/fixed-width-instruction codegen were not measured here.
- **Kernel-checked LRAT proof-term reconstruction inside Lean 4 — `unsupported`
  in `leanprover/lean4@5045d00564` (`v4.34.1`):** `Std.Tactic.BVDecide` relies
  on native evaluation (`_native.bv_decide.ax_*`) rather than kernel reduction
  or kernel proof-term reconstruction; discharging non-trivial SAT/bitvector
  obligations inside `{propext, Classical.choice, Quot.sound}` therefore cannot
  use `bv_decide` on `v4.34.1`.
- **C++ exception unwinding across FFI (`_Unwind_Resume`, `.gcc_except_table`)
  — `not examined` for proof mechanization:** Section 1 empirically documents
  the landing-pad (`endbr64`), `.text.unlikely` `.cold` stub, and personality
  relocation surfaces emitted by default `g++ -O2`, and confirms `-fno-exceptions
  -fno-rtti` removes them. Formally verifying C++ unwinding tables or
  `extern "C-unwind"` ABI propagation inside Lean 4 was not attempted.
- **Cross-TU LTO / dynamic shared-library PLT/GOT resolution — `not examined`:**
  Relocatable `.o` analysis covers `R_X86_64_PC32`, `R_X86_64_PLT32`, and
  `R_X86_64_REX_GOTPCRELX` at the object-file level; verifying post-link
  `ld`/`lld` relaxation, PLT stubs, and dynamic relocation processing
  (`R_X86_64_RELATIVE`, `IFUNC`) lies outside this report.
- **Attractive stronger conclusion `known not to apply`:** Passing
  `ShardedTreeLift` at `N = 5,000` straight-line spill-heavy instructions does
  **not** mean arbitrary 5,000-instruction compiled C/C++ functions are
  automatically proved in 17 seconds. That benchmark measures the **front-end
  lifting and memory-framing floor** (proving `AbstractsFrame` from raw machine
  code to functional SSA IR); discovering loop invariants, proving equivalence
  between AVX2 and scalar fallback paths, and verifying functional correctness
  of the lifted SSA IR remain separate proof obligations whose cost depends on
  algorithmic complexity.
- **Attractive stronger conclusion `known not to apply` (DWARF hints):** High
  headline parameter coverage in `llvm-dwarfdump --statistics` (`28/28` in
  `c_hardened_O3_avx2`) does **not** mean DWARF gives reliable live register
  assignments throughout optimized functions: removing synthetic
  `DW_OP_entry_value` expressions collapses 100% live coverage to `28.6%` of
  parameters and `12.5%` of locals (`0%` of C++ locals). Untrusted hint
  extractors must treat `.eh_frame` + `.rela.rodata` as primary structural
  sources and DWARF solely as a best-effort naming/cutpoint heuristic.

## Evidence

### Preserved Support Material (Self-Contained Package Artifacts)

- `support/ffi_anatomy_suite.c` — Six realistic C FFI workloads (`tlv_parse_checksum`,
  `opcode_dispatch_16`, `vec_add_aliased`, `vec_add_restrict`,
  `sibling_tail_dispatch`, `synth_zero_and_copy`, `stack_buf_hash_small`,
  `stack_buf_hash_large`).
- `support/ffi_anatomy_cpp.cpp` — C++ virtual-dispatch (`Codec` / `XorCodec`)
  and RAII (`ScopedGuard`) FFI workload (`cpp_codec_invoke`, `cpp_xor_direct`).
- `support/handwritten_leaf.S` — Hand-written x86-64 leaf assembly baseline
  (`leaf_add_u64`).
- `support/analyze_ffi_objects.py` — Standalone Python driver compiling all ten
  GCC/G++ `15.2.0` profiles inside `tempfile.TemporaryDirectory()`, parsing
  `objdump -d -r`, `readelf -S -r -s -n -W --debug-dump=frames-interp`,
  `llvm-dwarfdump --statistics`, DWARF DIE counts, and raw `.BTF` binary headers.
- `support/ffi_anatomy_results.json` — Complete machine-readable JSON output
  captured on `2026-11-20` (`gcc`/`g++ 15.2.0`, GNU Binutils `2.47`, Debian
  LLVM `21.1.8`).
- `support/MachineLiftBase.lean` — Simplified 64-bit x86-64-like machine
  semantics (`MState`, `ObjImage`, `step`, `run`, `CutBox`, `AbstractsFrame`,
  `checkDropLift_sound`, balanced `CodeTree`, `TreeObjImage`, `checkLeafAt`,
  `checkTreeLeaf_sound`).
- `support/HintSeparationProbe.lean` — Compiled 16-case switch + canary image
  demonstrating zero-TCB untrusted hint consumption (`UntrustedHints.HintCert`
  + `checkHintCert_sound`) with Statement-Origin Separation on
  `LockedObligation.verify_compiled_dispatch_abi`.
- `support/bench_lean4_scaling_and_axioms.py` — Standalone Lean `v4.34.1`
  benchmark and batch private-level kernel replay harness (`-DElab.async=false
  -Ddebug.skipKernelTC=false -j1 -M2048`, `trustLevel := 0`, `plugins := #[]`,
  `loadExts := false`, `level := .private`, `allowOpaque := true`).
- `support/lean4_scaling_and_axioms_results.json` — Complete empirical output
  across all 35 compiled/attempted Lean modules and 32 private-level kernel
  replays captured on `2026-11-20`.

### Primary Upstream Sources Inspected (Observed `2026-11-20`)

- `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):
  - `trusted/audit/TrustedBoundary.lean:374-429` (`finalizeImportedEnv`,
    `importEnv` with `trustLevel := 0`, `plugins := #[]`, `loadExts := false`,
    `level := .private`), `529-575` (`allowedTheoryTacticKinds`,
    `allowedTheorySyntaxKinds`), `1109-1117` (`ensureReplayableConstant` noting
    `Lean.Replay` skips `unsafe`/`partial`), `1298-1314` (`replayOntoBase`).
  - `docs/trust-model.md:52-95, 240-315` (target-crate vs. Pass-1/Pass-2 trust
    boundaries and axiom allowlist `{Classical.choice, Quot.sound, propext}`).
- `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):
  - Direct execution of `lean` binary (`v4.34.1`) confirming `maxRecDepth = 512`,
    `maxHeartbeats = 200000`, `Lean.Replay`, `ConstantInfo.value? (allowOpaque
    := true)`, and `Std.Tactic.BVDecide` `_native.bv_decide.ax_1` axiom emission.
- `awslabs/s2n-bignum` (`280a220986a0bc6249248187717a771153d073db`):
  - `x86/proofs/decode.ml:75-110, 435-480` (explicit `NONE` decoding for
    `0x64` FS, `0x65` GS, `0xf0` LOCK, `0x67` addr override, indirect
    `CALL`/`JMP`, and `DIV`/`IDIV`).
- `leanprover/LNSym` (`49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`):
  - `Tactics/Sym.lean`, `Tactics/PruneUpdates.lean` (`44.8 KB`), `Tactics/CSE.lean`
    (`13 KB`), `Proofs/SHA512/SHA512LoopBlocks.lean` (`5,543` LOC / `365.9 KB`).
- `HOL-Theorem-Prover/HOL` (`1c803b0f5467e8cf6a50059620c49b2e4810ab6f`):
  - `examples/machine-code/decompiler/decompilerLib.sig`, `decompilerLib.sml`
    (4-stage proof-producing machine-code decompilation into functional HOL).
- `seL4/graph-refine` (`33d94bbdd6448ada368d4d925935e8cfdf7d93b4`):
  - `README.md`, `stack_logic.py`, `search.py` (calling-convention stack framing
    and SMT-based C/SIMPL-to-binary CFG correspondence; `-O2` loop unrolling
    limitation).
- `ssrg-vt/FoxDec` (`d9206efe59a94138924d45c3d69d7c7afa1eb4ac`):
  - Formally verified x86-64 binary lifting of GCC binaries (PLDI 2022 / CCS 2024).
- `rems-project/islaris` (`c978e10f50db5c40f0fdf113f5f76a779782c6f9`) &
  `rems-project/CN2Islaris` (`f34f9a2f0a9b75a6b342aa966d0d14daca58c466`):
  - `CN2Islaris/README.md` (DWARF-guided C-to-Islaris translation via
    `read-dwarf`; current loop-free `unsigned long` AArch64 scope).
- `rems-project/cn` (`f2e8eeb47103a2c9fdf2b73a996969f3da114613`) &
  `rems-project/cerberus` (`e29a8ec9f247ef7e0fbc3a19141dfc8f0f9b902e`):
  - C refinement-type verification over Cerberus C semantics.
- `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`):
  - Verified C99/C11 compiler (excludes C++, AVX2 auto-vectorization, and
    `-fstack-clash-protection`).
- `snu-sf/crellvm` (`668249b88756233f96b3ef21f12993501a348afc`) &
  `vellvm/vellvm` (`7f0610c38d829b79bf6e867edf410c9e6f928f98`):
  - `crellvm/README.md`, `coq/proof/Adequacy.v`, `coq/proof/TODOProof.v`;
    `vellvm/README.md` (LLVM IR formalization; backend lowering outside scope).
- `AliveToolkit/alive2` (`3bdd4f5e1cefa47057e93110e707acd11cfe08e4`):
  - Bounded SMT LLVM IR translation validation (backend lowering outside scope).
- `Deducteam/hol2dk` (`7f0da9630ea948628f9c5f49829d18df6a7073ee`):
  - `README.md:108-290` (exact HOL Light proof-dump sizes and 32-core Rocq
    checking times: `3 GB` / `10 m 23 s` for `hol.ml`; `135 GB` / `21 h 14 m`
    for `Multivariate/make_complex.ml`).
- `AeneasVerif/kraken` (`c9aa45ee1b273892d7efa7bbf8a8a9391e17b2c0`):
  - Lean 4 weakest-precondition architecture (cross-referenced with corpus
    report `kraken-wp-foundation-parser-theorem-closure-and-certificate-checking`).

## Revalidation

To revalidate the findings after a compiler, Lean 4, or trust-boundary update:

1. **Re-run the C/C++ `.o` codegen & metadata anatomy probe (takes ~2 s):**
   ```bash
   python3 support/analyze_ffi_objects.py
   ```
   Diff `support/ffi_anatomy_results.json` to check whether a newer GCC/Clang
   version changes `.rela.rodata` jump-table encoding, `.text.unlikely` cold
   splitting, `-fstack-clash-protection` probe idioms, `g++ -gbtf` `.BTF`
   emission, or `llvm-dwarfdump --statistics` live-location coverage.
2. **Re-run the Lean 4 scaling, axiom-ceiling, and Statement-Origin Separation
   suite (takes ~110 s single-threaded under `-j1 -M2048`):**
   ```bash
   python3 support/bench_lean4_scaling_and_axioms.py
   ```
   Verify in `support/lean4_scaling_and_axioms_results.json`:
   - `ShardedTreeLift` compiles and passes private-level kernel replay through
     `N = 5,000` under default `maxRecDepth` / `maxHeartbeats`;
   - `Budget_Target_Omega`, `Budget_Target_BvOmega`, and `Budget_Target_Grind`
     still report `within_3_axiom_ceiling = true` and `replay_rc = 0`;
   - Check whether a newer Lean 4 release eliminates `_native.bv_decide.ax_*`
     on `Budget_Target_BvDecide` (`vc1`–`vc3`);
   - Verify `exp4_hint_separation` reports `replay_rc = 0`, `type_hints = 0`,
     and `val_hints > 0`.
3. **Check Anneal policy drift:** Inspect `trusted/audit/TrustedBoundary.lean`
   (`allowedTheoryTacticKinds`, `importEnv`, `replayOntoBase`) and
   `trusted/lean/foundation-lock.json` to verify whether target-crate proofs
   adopt a distinct sandboxed tactic/axiom policy or remain bound to the Pass-1
   syntax allowlist.
4. **Check upstream system advances:** Diff `rems-project/CN2Islaris` (for
   loop/x86-64 support), `awslabs/s2n-bignum/x86/proofs/decode.ml` (for
   segment/indirect-branch extensions), and `Deducteam/hol2dk` (for Lean 4
   backend or proof-size compression).
