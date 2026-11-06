# Rust Inline Assembly Contracts, Binary Relocations, SIMD/Union Representation, and ISA Semantics Correspondence

## Summary

Verifying Rust programs that cross inline assembly (`asm!`), naked function (`#[unsafe(naked)]` / `naked_asm!`), module-scoped assembly (`global_asm!`), or SIMD intrinsic boundaries requires obligations that neither source-level compilation, functional MIR extraction, nor final return-value equality can discharge in isolation:

1. **Source-Level Quantifiers vs. Post-Compilation Binary Certificates:**
   Under the Rust Reference (`src/inline-assembly.md`), `asm!` operand constraints (`in`, `out`, `inout`, `lateout`), clobber declarations (`clobber_abi`), and optimizer-visible options (`pure`, `nomem`, `readonly`, `preserves_flags`, `noreturn`, `nostack`) are semantic promises from the author to the compiler. `rustc` accepts false effect contracts at compile time (for example, a memory store marked `nomem` or a flag-modifying comparison marked `preserves_flags` in `support/rust-inline-assembly-contracts-2dafab9/compile_only_invalid_contract.rs`). Furthermore, a source-level template proof must quantify over all register allocations permitted by the operand specification (`atomicAdd_all_allocations` vs. `illegal_lateout_witness` in `support/rust-inline-assembly-contracts-2dafab9/InlineContracts.lean`), whereas a post-compilation binary certificate binds one concrete register allocation and emitted byte sequence.
2. **Information Loss Across MIR, ULLBC, and LLBC Extraction:**
   While `rustc` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) lowers `asm!` and `naked_asm!` to `mir::TerminatorKind::InlineAsm`—retaining the macro kind, template pieces, structured operands, register classes, options, line spans, control-flow targets, and unwind action—and lowers `global_asm!` to `hir::ItemKind::GlobalAsm` and `MonoItem::GlobalAsm`, `AeneasVerif/charon` (`0.1.210` at `a535e914f74db4fd9e6be7048f4233270d8945c0`) strips all structured operands, register constraints, and options when lowering MIR to ULLBC (`TerminatorKind::InlineAsm` keeps only the rendered `asm: String`, normal targets, and `on_unwind`), drops `on_unwind` during ULLBC-to-LLBC structuring (`ullbc_to_llbc.rs`), and skips `GlobalAsm` items entirely during crate traversal (`translate_crate.rs`).
3. **Binary Relocation Binding and `#[inline(never)]` Ignore Rules Across ELF and Mach-O:**
   Under Rust Reference rule `[attributes.codegen.inline.ignored]` (`src/attributes/codegen.md:83-84`), `#[inline]` (including `#[inline(never)]`) is normatively ignored on externally exported functions carrying `#[no_mangle]` or `#[export_name]`. Binary verification must therefore inspect both the relocatable object and the linked image directly. In 64-bit Mach-O `CPU_TYPE_ARM64` objects (`support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/bind_artifacts.py`), an `ARM64_RELOC_ADDEND` (`r_type == 10`) entry modifies the immediately following `ARM64_RELOC_BRANCH26` (`r_type == 2`) entry by relocation-table index (`table_index + 1`) regardless of whether its `r_address` field overlaps the 4-byte `bl` instruction range. In Linux ELF AArch64 and x86-64 builds (`support/rust-assembly-zerocopy-shared-pilot-2026/bind_elf.py`), 36 of 40 whole-function object/executable pairs match byte-for-byte without body relocations, while the 4 C-ABI helper bounce functions differ only at a verified call relocation (`R_AARCH64_CALL26` at function offset 8 with addend 0, or `R_X86_64_PLT32` at field offset 5 with addend `-4`).
4. **Return-Value Equality vs. Memory-Access Multiplicity and Footprint Enforcement:**
   Across the 4-configuration shared Rust/assembly/`zerocopy` pilot (`support/rust-assembly-zerocopy-shared-pilot-2026/pilot.rs`, 4,617 checks per run across AArch64 and QEMU x86-64 at `-C opt-level=0` and `3`), value agreement does not imply identical calling conventions or memory footprints: at `-C opt-level=3`, an internal `zerocopy` decoder (`zc_decode`) promotes its source-level reference parameter to a scalar `i64` passed via internal `fastcc`, and the optimized `zerocopy` 16-byte copy emits four scalar memory accesses of widths `4@0`, `4@3`, `8@7`, and `1@15` (reading and writing byte offset 3 twice, so operand widths sum to 17 bytes per direction while the byte interval union is 16 bytes). Similarly, on a 4-instruction naked AArch64 exchange leaf (`support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/boundary.rs`) and in `leanprover/kraken` (`8af78062037bc237b341d20252aafd1797c1bcb7`), default `Effects.All` and `Executable.eval` ignore `require_read_access`, `require_write_access`, and `require_exec_access` events and check alignment only when the base register is `SP`, accepting out-of-footprint stores (`str x1, [x0, #8]`) and unaligned general-purpose register loads unless a strict footprint-and-alignment observer (`Effects.StrictObserve` in `support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/kraken_effects_and_parser_opacity_probe.lean`) is used.
5. **Kraken Parser Kernel Opacity vs. Fuel-Bounded Reduction and SIMD/Union Representation:**
   In `leanprover/kraken` (`8af78062037bc237b341d20252aafd1797c1bcb7`) under Lean `v4.34.1`, `Kraken.AArch64.Parser.parse` dispatches through `parseAddr` to recursive `partial def parseConstExpr`, which elaborates as an opaque kernel constant (`ConstantInfo.opaqueInfo`) with no equational lemmas (`getEqnsFor? = none`), blocking kernel `rfl`/`decide` reduction unless replaced by a fuel-bounded structural parser (`parseConstExprFuel`). At the SIMD and union representation boundary (`support/rust-neon-vector-and-union-representation-control-1d81eb4/simd_union.rs`), portable `Simd<u32, 4>` and Arm NEON `vaddq_u32` agree with wrapping scalar addition (`(a[i] + b[i]) mod 2^32`) across 64 edge pairs, but differ from checked scalar addition on overflow (`None` vs. `0`) and impose 16-byte alignment (`align_of::<Simd<u32, 4>>() == 16` vs. `align_of::<[u32; 4]>() == 4`), target-feature (`neon`), and `#[repr(C)]` union field bit-validity obligations.

## Applicability

This report synthesizes normative specifications, compiler and extractor source inspections, binary object/executable verifiers, native and emulated runtime executions, and Lean 4 kernel mechanizations across the following subjects recorded in `REPORT.json`:

- **Rust Compiler (`rust-lang/rust`) Multi-Version Coverage:**
  - **Rust 1.89.0 (`29483883eed69d5fb4db01964cdf2af4d86e9cb2`, LLVM 20.1.7):** Used for the 4-configuration shared Rust, whole-function/inline assembly, and `zerocopy` 0.8.63 (`google/zerocopy@8d8ed8dcc98c991d32cee3c3a84e129f29cba136`) execution pilot across `aarch64-unknown-linux-gnu` and `x86_64-unknown-linux-gnu` (`-C opt-level=0` and `3`, `-C codegen-units=1`, `-C panic=abort`, `-C overflow-checks=yes`).
  - **Rust Nightly `nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):** Examined for AST-to-HIR-to-THIR-to-MIR lowering of `asm!`, `naked_asm!` (`mir::TerminatorKind::InlineAsm`), and `global_asm!` (`hir::ItemKind::GlobalAsm` and `MonoItem::GlobalAsm`), paired with `AeneasVerif/charon` `0.1.210` (`a535e914f74db4fd9e6be7048f4233270d8945c0`).
  - **Rust 1.99.0 (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, `aarch64-apple-darwin`):** Used to verify compile-time acceptance of false `nomem` and `preserves_flags` inline-assembly option contracts (`--edition=2024 --emit=metadata`) and LLVM inline-assembly constraint emission.
  - **Rust Nightly `1.101.0-nightly` (`1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6`, LLVM 23.1.3, `aarch64-apple-darwin`):** Used for portable SIMD (`core::simd::Simd<u32, 4>`), Arm NEON (`core::arch::aarch64::vaddq_u32`), and `#[repr(C)]` union layout and execution comparisons (`--edition=2024 -C opt-level=1`).
- **Rust Reference (`rust-lang/reference`) Multi-Version Coverage:**
  - Revisions `9571d4d38cc580bd9fe926f97fccd98f215564a9` (gitlinked by Rust 1.89.0), `ad35aca481751a06afeb23820a672b0f3b11a476` (paired with `nightly`), `2dafab96d919d6ab2884488e970bf95610ff83eb` (paired with Rust 1.99.0 and `1.101.0-nightly`), and `82da570bafd9efed421bdbae0f8603ede8dd308b` (tree `2f158dd465eb5a755cbbf2d77b6f2db0075498f8`).
  - **Invariant Across All Inspected Reference Revisions:** The operand timing contracts (`in`, `out`, `inout`, `lateout`), optimizer-visible option rules (`pure`, `nomem`, `readonly`, `preserves_flags`, `noreturn`, `nostack`), prohibition on unwinding out of ordinary `asm!` (`[asm.rules.unwind]`), `#[unsafe(naked)]` single-`naked_asm!` body rule (`[attributes.codegen.naked.*]`), `[attributes.codegen.inline.ignored]` on exported `#[no_mangle]`/`#[export_name]` functions, and `#[repr(C)]` union field-validity rules are invariant across all four Reference commits.
- **External ABI Specifications, Emulators, and Formal Verification Kernels:**
  - **AAPCS64 (`ARM-software/abi-aa@ec3e2fb69065768aa1caf298813a7808b50bc264`) and SysV x86-64 psABI (`x86-psABIs/x86-64-ABI@e1ce098331da5dbd66e1ffc74162380bcc213236`):** Govern scalar integer, pointer, callee-saved register, stack-frame alignment, and 16-byte SIMD register conventions for the Linux AArch64 and x86-64 pilot.
  - **QEMU User-Mode Emulator (`qemu/qemu@30a68773a4de9960647aa82718e5b8dafea05e7a`, release `v7.2.22`, Debian `1:7.2+dfsg-7+deb12u18+b3`):** Invoked with `-cpu qemu64-v1 -L /usr/x86_64-linux-gnu` for the x86-64 Linux ELF runs (providing baseline SSE/SSE2 `PPRO_FEATURES` defined in `target/i386/cpu.c:609`).
  - **Kraken AArch64 ISA Model (`leanprover/kraken@8af78062037bc237b341d20252aafd1797c1bcb7`, upstream toolchain `leanprover/lean4:v4.20.1`) and Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, release `v4.34.1`):** Used to verify inline-assembly register-allocation theorems (`support/rust-inline-assembly-contracts-2dafab9/InlineContracts.lean`) and Kraken parser opacity / `Effects` footprint theorems (`support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/kraken_effects_and_parser_opacity_probe.lean`).

## Findings

### 1. Normative Rust Inline, Naked, and Global Assembly Contracts and Quantifier Structure

**Basis:** `normative` (`rust-lang/reference` at `9571d4d38cc580bd9fe926f97fccd98f215564a9`, `ad35aca481751a06afeb23820a672b0f3b11a476`, `2dafab96d919d6ab2884488e970bf95610ff83eb`, and `82da570bafd9efed421bdbae0f8603ede8dd308b`) + `execution` + `derived` (`support/rust-inline-assembly-contracts-2dafab9/InlineContracts.lean` and `support/rust-inline-assembly-contracts-2dafab9/compile_only_invalid_contract.rs`).

#### 1.1 Normative Scope and Codegen Rules

Across the inspected Rust Reference revisions (`support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/reference-selected-identities.json`), Rust partitions handwritten assembly into three syntactic forms with distinct compiler contracts:

| Normative Rule | Reference Location | Technical Requirement & Verification Consequence |
| :--- | :--- | :--- |
| `asm!`, `naked_asm!`, `global_asm!` scopes | `src/inline-assembly.md` (`[asm.scope.*]`) | Ordinary `asm!` executes inside a compiler-managed Rust function frame; `naked_asm!` constitutes the entire body of a `#[unsafe(naked)]` function without compiler prologue/epilogue; `global_asm!` emits module-scoped assembly outside any Rust function body. |
| `[attributes.codegen.inline.ignored]` | `src/attributes/codegen.md:83-84` | `#[inline]` (including `#[inline(never)]`) is ignored on externally exported functions carrying `#[no_mangle]` or `#[export_name]`. Source annotations alone cannot guarantee a non-inlined call instruction (`bl` / `call`) in an exported caller wrapper. |
| `[attributes.codegen.naked.intro]` .. `[attributes.codegen.naked.body]` | `src/attributes/codegen.md:148-206` | A `#[unsafe(naked)]` function must consist of a single `core::arch::naked_asm!` call, suppresses compiler prologue/epilogue generation, forbids referencing parameter names directly outside operand bindings, and must manually uphold the declared `extern "C"` ABI and return path. |
| `[asm.rules.abi]` & `[asm.register-operands.abi-clobbers]` | `src/inline-assembly.md:1079-1182` | Any register or memory modification not declared via operands or `clobber_abi` is undefined behavior. On `aarch64` `extern "C"`, the first two 64-bit integer/pointer arguments arrive in `x0` and `x1`, the 64-bit result returns in `x0`, and `x30` (`lr`) holds the return address. |
| `[asm.options.*]` | `src/inline-assembly.md` | Optimizer promises: `pure` requires deterministic dependence only on declared inputs and eventual termination; `nomem` forbids any externally observable memory access or synchronization; `readonly` forbids memory writes and synchronization; `preserves_flags` forbids modifying architectural condition flags; `noreturn` forbids fallthrough; `nostack` forbids touching the stack (including the red zone). |

#### 1.2 Register-Allocation Quantifiers (`out` vs. `lateout`) and Trace Safety

Let `instantiate(template, assignment)` produce the concrete machine instruction sequence for a compiler-chosen register assignment, and let `allowed(assignment, operands, target)` express the register-class and overlap rules permitted by the operand specification:

- **Source-Template Universal Quantifier vs. Post-Compilation Bound Certificate:**
  A source-level correctness theorem for an `asm!` block must establish:
  $$\forall \mathit{assignment},\; \mathit{allowed}(\mathit{assignment}) \longrightarrow \forall s_0,\; \mathit{input\_relation}(\mathit{assignment}, s_0) \longrightarrow \mathit{safe\_execution\_and\_contract}(\mathit{instantiate}(\mathit{template}, \mathit{assignment}), s_0)$$
  By contrast, a build-specific binary certificate replaces the outer universal quantifier over `assignment` with the exact register allocation and machine bytes emitted into the compiled object/executable, requiring the certificate consumer to reject recompilations that alter those bytes.
- **Timing of Input Consumption (`out` vs. `lateout`):**
  Under the Rust Reference, an ordinary `out(reg)` operand may not overlap any `in(reg)` operand because the assembly template may write the output before reading all inputs; a `lateout(reg)` operand permits the compiler to allocate the output to the same physical register as an `in(reg)` operand, which is sound *only* if the assembly reads all inputs before first writing the output. In `support/rust-inline-assembly-contracts-2dafab9/InlineContracts.lean` (checked under Lean `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`):
  - `atomicAdd_all_allocations` and `atomicAdd_frame` prove that a single-instruction addition that reads both input registers from the pre-state before writing the destination register is sound across all register assignments (including when the output register overlaps either input register) and preserves all non-output registers.
  - `illegal_lateout_witness` proves a concrete counterexample for a two-instruction sequence (`mov out, in1; add out, in2`) marked `lateout`: when the allocator assigns `out` and `in2` to the same physical register `r1`, inputs `(in1 = 1, in2 = 2)` produce `2` (`1 + 1`) instead of `3` (`1 + 2`).
- **False Option Contracts Accepted by `rustc` and Transient Out-of-Footprint Writes:**
  In `support/rust-inline-assembly-contracts-2dafab9/compile_only_invalid_contract.rs`, two functions declare deliberately false `options(...)` contracts: a memory store (`str`) annotated with `options(nomem, nostack)` and a condition-flag-modifying comparison (`cmp`) annotated with `options(nomem, nostack, preserves_flags)`. Compiling with `rustc 1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, `--edition=2024 --emit=metadata`, recorded in `support/rust-inline-assembly-contracts-2dafab9/execution.json`) succeeds with exit code `0`, confirming that `rustc` treats `options(...)` as unchecked optimization premises rather than verified properties. Furthermore, `final_frame_does_not_imply_trace_safety` in `support/rust-inline-assembly-contracts-2dafab9/InlineContracts.lean` proves that a `temporaryWrite` program that writes to an out-of-footprint address and restores the original byte before returning satisfies final-state byte equality while violating trace-level memory-footprint safety (`nomem` / `readonly`), and `same_address_is_not_resource_authority` proves that numeric address equality cannot recover erased allocation liveness, initialization, or aliasing permissions.

---

### 2. Lowering and Information Loss Across `rustc` MIR and `Charon` ULLBC/LLBC

**Basis:** `source` + `documentation` + `derived` (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`).

Comparing `rustc`'s internal representations against `Charon` `0.1.210` reveals a sharp information-loss boundary for both function-scoped and module-scoped assembly:

| Stage / Representation | Source Location (`rustc` / `charon`) | Retained Assembly Information | Discarded / Omitted Information |
| :--- | :--- | :--- | :--- |
| **`rustc` HIR (`global_asm!`)** | `compiler/rustc_hir/src/hir.rs` (blob `59d1b4b5576ee47ea6c994977d40d5a948f139ce`) & `compiler/rustc_middle/src/mono.rs` | `ItemKind::GlobalAsm` with `InlineAsm` payload, fake body for `sym` type-checking, and `MonoItem::GlobalAsm` in monomorphization (`compiler/rustc_codegen_ssa/src/base.rs`, blob `78bc07869895ad2a8b67cb5d6115eb1cdbc96db3`). | Separate from function MIR bodies. |
| **`rustc` MIR (`asm!`, `naked_asm!`)** | `compiler/rustc_middle/src/mir/syntax.rs` (blob `07eaa085fabc9742d0d51c73eeba91dcc9e67d2e`) | `TerminatorKind::InlineAsm` retaining macro kind (`asm!` vs. `naked_asm!`), `template`, typed `operands` (split `inout` places, register classes/explicit registers, `const`, `sym`), `options` (including `MAY_UNWIND` inspected by `ffi_unwind_calls.rs` and `abort_unwinding_calls.rs`), `line_spans`, `targets`, and `unwind` action. | Target instruction semantics remain opaque to `rustc`. |
| **`Charon` Crate Traversal (`global_asm!`)** | `charon/src/bin/charon-driver/translate/translate_crate.rs` (blob `53536c6df6e241c9655840f6b1f8a4aca2113f90`) | None. | Explicitly skips `GlobalAsm` items (returns no translation kind), so symbols defined in `global_asm!` vanish from the translated item universe. |
| **`Charon` ULLBC (`asm!`, `naked_asm!`)** | `charon/src/bin/charon-driver/translate/translate_bodies.rs` (blob `c03ca8077f131a2ef701e9d27eaa9e69bb617124`) & `charon/src/ast/ullbc_ast.rs` (blob `3c6179f10742b2ee82c8ca07e6d51be6c8dc7694`) | `TerminatorKind::InlineAsm` containing only rendered `asm: String`, normal `targets`, and `on_unwind`. | Discards all MIR `operands`, register classes, explicit registers, input/output places, `sym` identities, `const` operands, `options` (`nomem`, `readonly`, `nostack`, `noreturn`), macro kind, and `line_spans`. |
| **`Charon` LLBC (`asm!`, `naked_asm!`)** | `charon/src/transform/control_flow/ullbc_to_llbc.rs` (blob `07322359e92f92a4d8b55865a67257bedacb0a62`) & `charon/src/ast/llbc_ast.rs` (blob `40f29f8a4b19f98e929b5fe82b8a009d813120ad`) | LLBC `InlineAsm` statement containing only `asm: String` and normal control-flow targets. | Also discards ULLBC's `on_unwind` edge (`TODO` in `ullbc_to_llbc.rs`). |

Consequently, attaching an ISA instruction model directly to `Charon`'s LLBC output is insufficient to verify inline assembly: LLBC has already erased which Rust places supply input registers or receive output registers and which optimizer promises (`nomem`, `readonly`, `preserves_flags`) `rustc` relied upon when optimizing the surrounding function.

---

### 3. Shared Rust, Assembly, and `zerocopy` Execution Pilot on AArch64 and Emulated x86-64

**Basis:** `source` + `execution` + `derived` (`support/rust-assembly-zerocopy-shared-pilot-2026/pilot.rs`, `aarch64.s`, `x86_64.s`, `vectors.rs`, `expected.json`, `runtime-results.json`, `compile-static/function-bindings.json`, and `compile-static/STATIC-HANDOFF.md`).

#### 3.1 Four-Configuration Execution Matrix and Fixed Oracle Corpus

The shared pilot (`support/rust-assembly-zerocopy-shared-pilot-2026/pilot.rs`, SHA-256 `1b9466576e315530e54eea9622d102e59ae219177473440c2ebade46fd9e4616`), paired with whole-function assembly bodies in `support/rust-assembly-zerocopy-shared-pilot-2026/aarch64.s` (SHA-256 `ad1d035551286a22b0e189a3ba1aed427154258df6a4fac897a4e842e52aa895`) and `support/rust-assembly-zerocopy-shared-pilot-2026/x86_64.s` (SHA-256 `f8a609d98c11518606547a7436f76a23a5f06a4058b898cba75143985c7c5e50`) and pre-generated test vectors in `support/rust-assembly-zerocopy-shared-pilot-2026/vectors.rs` (SHA-256 `4ef9cf1308e4ec9bd55daeb6f98320e1fa6fa24ac022857bd460a89231fbce28`), was compiled with Rust 1.89.0 (`29483883eed69d5fb4db01964cdf2af4d86e9cb2`) against `zerocopy` 0.8.63 (`google/zerocopy@8d8ed8dcc98c991d32cee3c3a84e129f29cba136`) and executed across four target/optimization profiles:

| Image Configuration | Execution Environment | Final Linked ELF SHA-256 | Exit Status / Stderr / Harness Checks |
| :--- | :--- | :--- | :--- |
| `aarch64-O0` (`-C opt-level=0`) | Native Linux AArch64 container | `adb86a7669598af8b9fa65d84bdea9b652fbc95171bff686fa3af85a24d10f20` | `0` / empty stderr / `4,617` checks |
| `aarch64-O3` (`-C opt-level=3`) | Native Linux AArch64 container | `b8047348558fdbc9fb7335e561dbb93f2983a9158f6604b26cfe8ae3d82f87f8` | `0` / empty stderr / `4,617` checks |
| `x86_64-O0` (`-C opt-level=0`) | QEMU `7.2.22` (`-cpu qemu64-v1 -L /usr/x86_64-linux-gnu`) | `ab6265e1c5333c11e971973b39b4cbc0a1ada16763c8c70515b8d881ce40ed4c` | `0` / empty stderr / `4,617` checks |
| `x86_64-O3` (`-C opt-level=3`) | QEMU `7.2.22` (`-cpu qemu64-v1 -L /usr/x86_64-linux-gnu`) | `64a1efa22c13b1b01e540193225fc50f7dd3911cd387a592165f7fe566c7a144` | `0` / empty stderr / `4,617` checks |

As recorded in `support/rust-assembly-zerocopy-shared-pilot-2026/source-call-counts.json`, each profile's 4,617 harness checks encompass 1,145 whole-function assembly entry invocations, 629 inline-assembly wrapper invocations, and corresponding Rust baseline, `zerocopy`, alignment, guard-word, and safe-error comparisons across 11 operation families:

| Operation Family | Fixed Vector Count | Verified Value, Guard, and `zerocopy` Relationships |
| :--- | :--- | :--- |
| `u64` widening multiply to 128-bit | 289 pairs | Low/high 64-bit product limbs (`MUL`/`UMULH` on AArch64, `MUL` on x86-64) vs. Rust `u128` oracle and output guard sentinels. |
| 128-bit addition with carry | 144 pairs | Multi-word carry propagation (`ADDS`/`ADC` on AArch64, `ADD`/`ADC` on x86-64) vs. Rust `overflowing_add`, output sentinels, and diagonal shared-input aliasing. |
| Inline carry-in / carry-out | 578 triples | Carry-in `0`/`1`, sum modulo $2^{64}$, and outgoing carry flag extraction vs. Rust `u128`. |
| Byte-swap and `zerocopy` wire conversion | 17 words | `REV` (AArch64) / `BSWAP` (x86-64) vs. explicit byte oracle and `zerocopy::byteorder::big_endian::U64` (`new`, `set`, `get`, `read_from_bytes`, `write_to`). |
| Whole-function & inline 8-byte load/store | 17 words | Aligned 8-byte memory reads and writes with source-immutability and destination-guard checks vs. Rust baseline. |
| Scalar, SIMD, `zerocopy`, and Rust 16-byte copy | 12 patterns | Disjoint 16-byte guarded spans comparing handwritten scalar (`2 × 8B`), handwritten SIMD (`1 × 16B`), `zerocopy` `[u8; 16]` `read_from_bytes`/`write_to`/`ref_from_bytes` pointer identity, and Rust copy. |
| Whole-function pointer offset return | 204 calls | Same-allocation pointer arithmetic returning base plus offsets `0..=16` (comparing one-past-the-end at offset 16 without dereferencing). |
| Inline assembly local labels | 17 words | Declared assembly label blocks with no output operands mapping `0 ↦ 17` and non-zero `↦ 41`. |
| C-ABI helper bounce (`pilot_helper`) | 289 pairs | Assembly and Rust bounces each invoke `extern "C" fn pilot_helper` once per pair (counted via an atomic counter), computing a rotate/xor/wrapping-multiply-plus-1 oracle. |
| 16-byte SIMD wrapping byte addition | 144 pairs | 16 independent `u8` lanes modulo 256 (`ADD Vd.16B` on AArch64, `PADDB` on x86-64 SSE2) with diagonal shared inputs and source/output guards. |
| Safe `zerocopy` size-mismatch rejection | Lengths 7 & 9 | `read_from_bytes` and `write_to` return `Err` on 7-byte and 9-byte slices while leaving destination buffers untouched; invalid spans never reach assembly. |

#### 3.2 ELF Object-to-Executable Relocation Binding and Calling-Convention Shifts

In `support/rust-assembly-zerocopy-shared-pilot-2026/compile-static/function-bindings.json` and `support/rust-assembly-zerocopy-shared-pilot-2026/compile-static/STATIC-HANDOFF.md` (330 static checks):

1. **Whole-Function Byte Identity and Call Relocations:** Across the 40 whole-function assembly symbol pairs (10 functions $\times$ 4 build profiles), 36 object-to-ELF pairs have identical machine bytes with zero interior relocations, and all whole-function object body hashes are identical between `-C opt-level=0` and `-C opt-level=3` within each architecture. The 4 `pilot_bounce` entries differ between `.o` and linked ELF solely at their call relocation slot targeting `pilot_helper`: AArch64 `R_AARCH64_CALL26` at function byte offset 8 with addend `0`, and x86-64 `R_X86_64_PLT32` at field byte offset 5 with addend `-4`.
2. **Caller Register Allocation and Hoisted Indirect Calls:** At `-C opt-level=3` on x86-64, one loop calling the foreign pointer-offset leaf `pilot_ptr` hoists `lea -0xf7a(%rip), %r13` (resolving `next_pc 0xc9d5 - 0xf7a = 0xba5b = pilot_ptr`) outside the call site and invokes `call *%r13` at `0xcb93` with arguments in `%rdi` and `%rsi`.
3. **Frame/CFI Restoration vs. Unmodeled Compiler Helper Calls:** In `pilot_bounce`, AArch64 saves `x29`/`x30` in a 16-byte aligned frame and x86-64 SysV subtracts 8 bytes from entry `%rsp` ($\equiv 8 \pmod{16}$) before `call` and restores `%rsp` before `ret`, matching the emitted `.eh_frame` CIE/FDE rules. However, at `-C opt-level=3` on AArch64, the Rust callee `pilot_helper` updates its atomic call counter via an out-of-line call to `__aarch64_ldadd8_relax`, introducing compiler/runtime instructions and stack frames beyond the handwritten assembly bounce itself.
4. **Access Multiplicity vs. Byte Interval Union in Optimized `zerocopy`:**
   - At `-C opt-level=3`, the private Rust helper `zc_decode` has its source-level reference argument promoted by LLVM to a scalar `i64` passed in register via internal `fastcc` before executing `rev` / `bswap`.
   - At `-C opt-level=3` on both AArch64 and x86-64, the compiled `zerocopy` 16-byte copy adapter emits four unaligned scalar memory accesses per direction at byte offsets and widths `4@0` (`[0, 4)`), `4@3` (`[3, 7)`), `8@7` (`[7, 15)`), and `1@15` (`[15, 16)`). Because `[0, 4)` and `[3, 7)` overlap at byte offset 3, byte 3 is read twice and written twice; the access widths sum to $4 + 4 + 8 + 1 = 17$ bytes per direction while their spatial interval union is $[0, 16)$ (16 bytes). By contrast, the handwritten scalar assembly copy performs two disjoint 8-byte accesses (`8@0`, `8@8`) and the handwritten SIMD assembly copy performs a single 16-byte access (`16@0`). Value equality on normal RAM therefore does not establish trace equivalence or single-access atomicity/MMIO safety.
5. **Data-Only Negative Controls and Pre-Target Reader Diagnostics:**
   - The initial runtime capture helper (`support/rust-assembly-zerocopy-shared-pilot-2026/capture_runtime_v1.py`, diagnosed in `support/rust-assembly-zerocopy-shared-pilot-2026/runtime-stop-v1-diagnosis.json`) halted before launching any target binary because it sliced 18 ELF header bytes instead of the 20 bytes (including `e_machine`) recorded in the static inventory. `support/rust-assembly-zerocopy-shared-pilot-2026/capture_runtime_v2.py` (`support/rust-assembly-zerocopy-shared-pilot-2026/runtime-v2.diff`) fixed the slice length from 18 to 20, and `support/rust-assembly-zerocopy-shared-pilot-2026/runtime-header-v2-regression.json` verifies 28 pure-data header controls across all 7 ELF files.
   - Twenty-four post-capture data-only stream controls (mutating check count, architecture tag, trailing newline, extra stdout, non-empty stderr, or non-zero exit code) and two 1-bit function-body byte mutations were all deterministically rejected without executing mutated binaries.

---

### 4. Mach-O `aarch64` Relocation Adjacency and Kraken `8af7806` Parser / `Effects` Boundaries

**Basis:** `source` + `execution` + `derived` (`support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/boundary.rs`, `bind_artifacts.py`, `macho_relocation_controls.eval.json`, `kraken_effects_and_parser_opacity_probe.lean`, and `kraken_effects_and_parser_opacity_probe.eval.json`).

#### 4.1 Return-Value vs. Two-Slot Memory-Footprint Discrimination (`boundary.rs`)

In `support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/boundary.rs` (SHA-256 `e6ea8e1c426d4d88c69e20f3753c35806a41fac76e6ea0ad34d2ce509029e21e`), the 4-instruction naked AArch64 exchange leaf `#[unsafe(naked)] pub unsafe extern "C" fn _anneal_exchange(slot: *mut u64, value: u64) -> u64` is tested against a wrong-slot mutation inside a 16-byte `#[repr(C)] struct Pair([u64; 2])` buffer initialized to `[a, b]`:

| Variant | Instruction Sequence | Little-Endian 32-Bit Words | Post-Call `(ret_x0, slot0, slot1)` |
| :--- | :--- | :--- | :--- |
| `positive` (`#[cfg(not(anneal_control))]`) | `ldr x2, [x0]; str x1, [x0]; mov x0, x2; ret` | `0xf9400002, 0xf9000001, 0xaa0203e0, 0xd65f03c0` | `(a, v, b)` |
| `control` (`#[cfg(anneal_control)]`) | `ldr x2, [x0]; str x1, [x0, #8]; mov x0, x2; ret` | `0xf9400002, 0xf9000401, 0xaa0203e0, 0xd65f03c0` | `(a, a, v)` |

Machine-checked theorems in `support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/kraken_effects_and_parser_opacity_probe.lean` (verified under Lean `v4.34.1` in `1.567s` and `522.9 MB` max RSS, `support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/kraken_effects_and_parser_opacity_probe.eval.json`) establish:

- **`return_value_only_cannot_distinguish`:** Observing only `(s.x0, s.pc)` returns `some (a, 0x2000)` on both `positiveLeafProg` and `wrongSlotLeafProg` for all `(baseAddr, a, v, b)`.
- **`effects_all_accepts_wrong_slot_when_equal`:** When `a == v`, even checking `(s.x0 == a) && (s.slot0 == a) && (s.pc == 0x2000)` under Kraken's default `Effects.All` returns `true` on `wrongSlotLeafProg`, because `slot0` already held `a == v` and `Effects.All` ignores the out-of-footprint write event `require_write_access (baseAddr + 8) 8`.
- **`two_slot_state_discriminator`:** Observing the full 2-slot state `(s.x0, s.slot0, s.slot1)` yields `some (a, v, b)` on `positiveLeafProg` vs. `some (a, a, v)` on `wrongSlotLeafProg`, separating the two programs whenever `v != a` or `v != b`.

#### 4.2 Mach-O `aarch64` Relocation Binding and Non-Overlapping `ARM64_RELOC_ADDEND` (`bind_artifacts.py`)

Because `#[inline(never)]` on an exported `_anneal_call` wrapper is normatively ignored under `[attributes.codegen.inline.ignored]`, `support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/bind_artifacts.py` (SHA-256 `7a659675dc278e57b6ad6121e734984de08cbdd5a15c06b9742c95876776d678`) directly binds the 64-bit Mach-O relocatable object (`MH_OBJECT = 1`) and linked executable (`MH_EXECUTE = 2`):

1. **Exact Symbol & VM-to-File Mapping (`selected_range`, lines 245–280):** Resolves `_anneal_exchange` (16 bytes) and `_anneal_call` in `__TEXT,__text`, checks that no interior symbols or overlapping sections/segments exist, and verifies `section.offset == segment.file_offset + symbol.value - segment.address` (`selected-vm-file-mapping`).
2. **Leaf Byte Identity (`decode_leaf`, lines 288–305):** Enforces byte-for-byte identity between `.o` and `MH_EXECUTE` (`leaf-byte-identity`), zero relocations overlapping the leaf (`leaf-relocation`), and exact bit-field masks for the four AArch64 instructions.
3. **Call-Site `bl` Relocation and Table-Index Adjacency (`object_call_relocation`, lines 317–329):** In `.o`, the 4-byte `bl` instruction at `pc = caller.entry + call_offset` must have zero embedded branch immediate (`word & 0x3ffffff == 0`) and one overlapping `ARM64_RELOC_BRANCH26` (`r_type == 2`, `r_length == 2`, `r_extern == 1`, `r_pcrel == 1`) relocation targeting `leaf.symbol_index`. Critically, in 64-bit Mach-O `CPU_TYPE_ARM64`, an `ARM64_RELOC_ADDEND` (`r_type == 10`) record pairs with the immediately following relocation entry by relocation-table index (`table_index + 1`), regardless of its `r_address` field. `bind_artifacts.py` lines 326–328 reject any preceding `r_type == 10` entry at `table_index - 1` (`paired-call-addend`). As verified in `support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/macho_relocation_controls.eval.json` (control 12, `nonoverlapping-preceding-call-addend`), an `ARM64_RELOC_ADDEND` whose `r_address` points to `caller_offset` (8 bytes before the `bl` instruction) bypasses byte-range overlap filters (`overlapping == False`) but is caught by `paired-call-addend`. All 13 synthetic negative controls pass for both positive and control cells.

#### 4.3 Kraken `8af7806` Recursive `partial def` Opacity vs. Fuel-Bounded Kernel Reduction and `Effects.StrictObserve`

In `leanprover/kraken@8af78062037bc237b341d20252aafd1797c1bcb7`:

- **Kernel Opacity of `Kraken.AArch64.Parser.parse`:** `Parser.parse` (`Kraken/AArch64/Parser/Basic.lean:703`) dispatches through `parseAddr` to `parseConstExpr` (`Basic.lean:138-152`), which is a recursive `partial def`. In Lean 4 (`Lean/Elab/PreDefinition/Main.lean:299-320` and `Lean/Meta/Eqns.lean:142-151`), `addAndCompilePartial` registers a recursive `partial def` in the kernel environment as an opaque declaration (`ConstantInfo.opaqueInfo`) paired with an `unsafe` auxiliary `._unsafe_rec` and generates no unfolding equations (`getEqnsFor?` returns `none`). Consequently, `#eval parseImmPartial ['#', '8']` evaluates in `MetaM` to `some 8`, but kernel `Eq.refl` fails because `parseImmPartial` cannot unfold `parseConstExprPartial`. Replacing `parseConstExprPartial` with a fuel-bounded structural parser `parseConstExprFuel (fuel : Nat)` yields kernel `rfl` proofs (`parseImmFuel_hash8`, `parse_positive_leaf_rfl`, `parse_wrong_slot_leaf_rfl`, `print_parse_roundtrip_positive`) in `support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/kraken_effects_and_parser_opacity_probe.lean`.
- **Permissive `Effects.All` vs. `Effects.StrictObserve`:** In `Kraken/AArch64/Semantics.lean:171-221, 319-327, 980-993` and `Kraken/AArch64/OmniSemantics.lean:13-22`, `MachineData.load` and `MachineData.store` emit `Effects.require_read_access` and `Effects.require_write_access` events, and instruction fetch emits `Effects.require_exec_access`, while `checkSPAlignment` checks alignment only when the base register is `SP`. However, both `Effects.All` and `Executable.eval` strip and ignore all `require_*_access` constructors. Defining `Effects.StrictObserve` over a `FootprintPolicy` (`code: [0x1000, 0x1010)`, `read: [0x4000, 0x4008)`, `write: [0x4000, 0x4008)`) accepts `positiveLeafProg` (`strict_observe_accepts_positive_leaf`), rejects `wrongSlotLeafProg` even when `a = v = b = 42` (`strict_observe_rejects_wrong_slot_even_when_all_values_equal`), and rejects unaligned `x0 = 0x4004` loads that `Effects.All` accepts (`effects_all_accepts_unaligned_x0_access` vs. `strict_observe_rejects_unaligned_x0_access`).

---

### 5. Portable SIMD, Arm NEON `vaddq_u32`, and `#[repr(C)]` Union Representation Controls

**Basis:** `normative` + `source` + `execution` + `derived` (`rust-lang/rust@1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6`, `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb`, and `support/rust-neon-vector-and-union-representation-control-1d81eb4/simd_union.rs`).

1. **SIMD Vector vs. Array Alignment and Non-Power-of-Two Padding:**
   In `library/portable-simd/crates/core_simd/src/vector.rs` (`1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6`, Git blob `55de9dac4637f9842259213ea599bfe0ddfe393f`), `Simd<T, N>` uses a `#[repr(simd)]` representation whose alignment is raised above `[T; N]` and whose array conversion routines explicitly account for trailing padding when `N` is not a power of two. In `support/rust-neon-vector-and-union-representation-control-1d81eb4/simd_union.rs` (executed on `aarch64-apple-darwin`, `support/rust-neon-vector-and-union-representation-control-1d81eb4/execution.json`), `Simd<u32, 4>` has size 16 bytes and alignment 16 bytes, whereas `[u32; 4]` has size 16 bytes and alignment 4 bytes. Equal 4-lane element values therefore do not justify transmuting `&[u32; 4]` to `&Simd<u32, 4>` without an explicit 16-byte alignment proof.
2. **Wrapping Vector Addition vs. Checked Scalar Overflow and Target Features:**
   Both portable `Simd<u32, 4>::add` (`library/portable-simd/crates/core_simd/src/ops.rs`) and Arm NEON `vaddq_u32` (`library/stdarch/crates/core_arch/src/arm_shared/neon/generated.rs:1980-2001`, SHA-256 `bcc351aa3331769468fc886aca610fc61af89ce10915a4f16493ad0f85517482`, marked `#[target_feature(enable = "neon")]`) lower to `simd_add` with lane-wise wrapping modulo $2^{32}$ semantics (`out[i] = (a[i] + b[i]) mod 2^32`). Across all 64 boundary pairs in `simd_union.rs`, scalar `wrapping_add`, portable `Simd<u32, 4>`, and `vaddq_u32` agree, whereas at `u32::MAX + 1` checked scalar addition returns `None` while SIMD addition wraps to `0`. Invoking `vaddq_u32` additionally requires the target-feature precondition `cfg!(target_feature = "neon")` (or runtime feature detection) to avoid undefined behavior under the Rust Reference (`src/behavior-considered-undefined.md`).
3. **`#[repr(C)]` Union Field Reinterpretation and Pattern-Matching Hazards:**
   Under `src/items/unions.md` and `src/type-layout.md` (`rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb`), all fields of a `#[repr(C)]` union start at byte offset 0 and share storage without an active-variant tag. Writing `Word { word: u32 }` and reading `Word.bytes: [u8; 4]` in `simd_union.rs` (size 4, alignment 4) produces `word.to_ne_bytes()` across 8 test values because all 4 bytes are initialized and `[u8; 4]` admits arbitrary initialized bit patterns. By contrast, reading a union field with restricted bit validity (such as `bool` when the underlying byte is not `0` or `1`) is immediate undefined behavior, and matching a union field inside a nested pattern can read that field even when a sibling subpattern fails unless the tag guard is evaluated in an outer match first.

## Boundaries

- **Not Examined:**
  - Physical x86-64 hardware execution (the Linux x86-64 pilot runs were executed under QEMU `7.2.22` user-mode emulation with `-cpu qemu64-v1`) and native `aarch64-apple-darwin` execution of the Mach-O relocation negative controls (which were evaluated as pure-data binary structures via `bind_artifacts.py`).
  - Wider SIMD instruction sets (`AVX2`, `AVX-512`, `SVE`, `SVE2`), floating-point `NaN` propagation, vector-by-value C ABI argument passing, and system registers or page-table updates.
  - Overlapping source/destination memory spans in the 16-byte copy routines or unaligned/out-of-bounds caller pointers in native execution (all negative memory and relocation controls were evaluated strictly as data or Lean models without executing undefined behavior in a native process).
- **Unknown:**
  - Whether future versions of `AeneasVerif/charon` will preserve structured `mir::TerminatorKind::InlineAsm` operands and options in ULLBC/LLBC or translate `MonoItem::GlobalAsm` items.
  - Whether upstream `leanprover/kraken` intends to add a built-in strict footprint interpreter alongside `Effects.All` and `Executable.eval` or refactor `parseConstExpr` from a recursive `partial def` to a structurally terminating definition.
- **Known Not to Apply:**
  - Source-level `#[inline(never)]` does **not** prevent inlining on externally exported `#[no_mangle]` or `#[export_name]` functions (`[attributes.codegen.inline.ignored]`).
  - `rustc` compilation (`--emit=metadata` or full codegen) does **not** validate `asm!` `options(nomem, readonly, preserves_flags, nostack, pure)` contracts (`support/rust-inline-assembly-contracts-2dafab9/compile_only_invalid_contract.rs`).
  - Final return-value or post-state memory equality does **not** establish absence of transient out-of-footprint writes (`final_frame_does_not_imply_trace_safety`), single-access multiplicity (as shown by `zerocopy`'s 17-byte total access width over a 16-byte interval at `-C opt-level=3`), or Kraken footprint/alignment compliance under `Effects.All`.
  - Mach-O relocation filtering by byte-range overlap with a `bl` instruction does **not** detect a preceding non-overlapping `ARM64_RELOC_ADDEND` (`r_type == 10`) entry at `table_index - 1`.
- **Unsupported:**
  - `AeneasVerif/charon` `0.1.210` does not support `global_asm!` items and does not preserve `asm!` operand/option contracts in LLBC.
  - `Lean.Meta.getEqnsFor?` and kernel `rfl`/`decide` reduction do not support unfolding recursive `partial def` declarations such as `Kraken.AArch64.Parser.parseConstExpr`.

## Evidence

| Artifact / Source Path | SHA-256 / Commit Identity | Evidence Role |
| :--- | :--- | :--- |
| `support/rust-assembly-zerocopy-shared-pilot-2026/pilot.rs`, `aarch64.s`, `x86_64.s`, `vectors.rs`, `expected.json`, `CONTRACTS.md` | `pilot.rs`: `1b9466576e315530e54eea9622d102e59ae219177473440c2ebade46fd9e4616`; `aarch64.s`: `ad1d035551286a22b0e189a3ba1aed427154258df6a4fac897a4e842e52aa895`; `x86_64.s`: `f8a609d98c11518606547a7436f76a23a5f06a4058b898cba75143985c7c5e50` | **source** & **execution**: Shared Rust 1.89.0 + assembly + `zerocopy` 0.8.63 fixture and pre-generated oracle vectors. |
| `support/rust-assembly-zerocopy-shared-pilot-2026/runtime-results.json`, `RESULTS-FREEZE.json`, `independent-review.md`, `independent-review.json` | `runtime-results.json`: `2b7e3e1dbbc4637ee22dcbfc68ebc2960bcab1fdc6ddefc0859a33295d9ad1c3` | **execution**: 4-configuration execution receipts (18,468 checks + 9,234 independent replay checks) and 24 data-only stream controls. |
| `support/rust-assembly-zerocopy-shared-pilot-2026/compile-static/function-bindings.json`, `compile-static/STATIC-HANDOFF.md`, `runtime-header-v2-regression.json` | `function-bindings.json`: `320f29c2145b584878667e1fe51bef2189bb9bc65defe60e7cdaa4e2151617a7` | **source**, **execution**, & **derived**: 40 object/ELF function byte bindings, call relocation decoding, `fastcc` scalar promotion, 17-byte vs. 16-byte copy operand widths, and 28 ELF header controls. |
| `support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/boundary.rs`, `bind_artifacts.py`, `macho_relocation_controls.eval.json` | `boundary.rs`: `e6ea8e1c426d4d88c69e20f3753c35806a41fac76e6ea0ad34d2ce509029e21e`; `bind_artifacts.py`: `7a659675dc278e57b6ad6121e734984de08cbdd5a15c06b9742c95876776d678` | **source** & **execution**: Mach-O 64-bit `aarch64` `.o`/executable verifier and 13 synthetic negative relocation controls (`paired-call-addend`). |
| `support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/kraken_effects_and_parser_opacity_probe.lean` & `kraken_effects_and_parser_opacity_probe.eval.json` | `.lean`: `c6086d0cbc3d4ec4337558502df878bee4e06fc3ddf6712cdbc9bc3f30436336`; `.eval.json`: `8489aa64f7b0c46c97074a57d768173c8dfdc69f848ab96ef5c88488a34db9fa` | **execution** & **derived**: Lean `v4.34.1` kernel proofs of `partial def` parser opacity vs. fuel-bounded `rfl` reduction and `Effects.All` vs. `Effects.StrictObserve`. |
| `support/rust-inline-assembly-contracts-2dafab9/InlineContracts.lean`, `compile_only_invalid_contract.rs`, `execution.json` | `rust-lang/rust@b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` | **execution** & **derived**: Lean `v4.34.1` register-allocation/lateout/trace-safety theorems and `rustc` false-option compile-only specimen. |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` & `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` | `mir/syntax.rs` (`07eaa085...`), `translate_bodies.rs` (`c03ca807...`), `ullbc_to_llbc.rs` (`07322359...`), `translate_crate.rs` (`53536c6d...`) | **source**: Lowering of `asm!`, `naked_asm!`, and `global_asm!` through `rustc` MIR and information loss in `Charon` ULLBC/LLBC. |
| `support/rust-neon-vector-and-union-representation-control-1d81eb4/simd_union.rs`, `execution.json`, `source-identities.json` | `simd_union.rs`: `fa0773630c004eb1c85cc3d93b2e4ece77ac5e412e9962c56fdf44fadea295d2`; `rust-lang/rust@1d81eb4ad9cd207e3e638bd32b17ec4fce8412a6` | **source** & **execution**: Portable `Simd<u32, 4>`, Arm NEON `vaddq_u32`, and `#[repr(C)]` union layout and overflow probe. |

## Revalidation

Run the following deterministic checks from the package directory (`reports/rust-inline-assembly-contracts-relocations-and-simd-correspondence/`):

1. **Lean 4.34.1 Mechanizations (Inline Register-Allocation Contracts and Kraken Parser/`Effects` Probe):**
   ```bash
   anneal-lean-run --mode file --concurrency 1 -- \
     elan run leanprover/lean4:v4.34.1 lean -j1 -M768 \
     support/rust-inline-assembly-contracts-2dafab9/InlineContracts.lean

   anneal-lean-run --mode file --concurrency 1 -- \
     elan run leanprover/lean4:v4.34.1 lean -j1 -M768 \
     support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/kraken_effects_and_parser_opacity_probe.lean
   ```
2. **Mach-O `aarch64` Relocation Binding and 13 Negative Controls (`ARM64_RELOC_ADDEND` Adjacency):**
   ```bash
   python3 - <<'PY'
   import struct, sys
   sys.path.insert(0, "support/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge")
   import bind_artifacts as ba

   def make_obj(store_word):
       words = (0xF9400002, store_word, 0xAA0203E0, 0xD65F03C0,
                0xA9BF7BFD, 0x910003FD, 0x94000000, 0xA8C17BFD, 0xD65F03C0)
       text = b"".join(struct.pack("<I", w) for w in words)
       r_bits = 0 | (1 << 24) | (2 << 25) | (1 << 27) | (2 << 28)
       reloc = struct.pack("<iI", 0x18, r_bits)
       reloff, symoff = 0xD0 + len(text), 0xD0 + len(text) + len(reloc)
       strtab = b"\x00_anneal_exchange\x00_anneal_call\x00"
       syms = struct.pack("<IBBHQ", 1, 0x0F, 1, 0, 0) + struct.pack("<IBBHQ", 18, 0x0F, 1, 0, 0x10)
       hdr = struct.pack("<IiiIIIII", 0xFEEDFACF, 0x0100000C, 0, 1, 2, 176, 0, 0)
       seg = struct.pack("<II16sQQQQiiII", 0x19, 152, b"\x00"*16, 0, len(text)+16, 0xCC, len(text)+16, 7, 7, 1, 0)
       sec = struct.pack("<16s16sQQIIIIIIII", b"__text\x00"+b"\x00"*9, b"__TEXT\x00"+b"\x00"*9, 0, len(text), 0xD0, 2, reloff, 1, 0x80000400, 0, 0, 0)
       sym = struct.pack("<IIIIII", 2, 24, symoff, 2, symoff + len(syms), len(strtab))
       return hdr + seg + sec + sym + text + reloc + syms + strtab

   def make_exe(store_word):
       bl_word = 0x94000000 | ((-6) & 0x3FFFFFF)
       words = (0xF9400002, store_word, 0xAA0203E0, 0xD65F03C0,
                0xA9BF7BFD, 0x910003FD, bl_word, 0xA8C17BFD, 0xD65F03C0)
       text = b"".join(struct.pack("<I", w) for w in words)
       symoff, sec_addr = 0xE8 + len(text), 0x1000000E8
       strtab = b"\x00_anneal_exchange\x00_anneal_call\x00"
       syms = struct.pack("<IBBHQ", 1, 0x0F, 1, 0, sec_addr) + struct.pack("<IBBHQ", 18, 0x0F, 1, 0, sec_addr + 0x10)
       stroff = symoff + len(syms)
       total = stroff + len(strtab)
       hdr = struct.pack("<IiiIIIII", 0xFEEDFACF, 0x0100000C, 0, 2, 3, 200, 0, 0)
       seg = struct.pack("<II16sQQQQiiII", 0x19, 152, b"__TEXT\x00"+b"\x00"*9, 0x100000000, total, 0, total, 7, 5, 1, 0)
       sec = struct.pack("<16s16sQQIIIIIIII", b"__text\x00"+b"\x00"*9, b"__TEXT\x00"+b"\x00"*9, sec_addr, len(text), 0xE8, 2, 0, 0, 0x80000400, 0, 0, 0)
       sym = struct.pack("<IIIIII", 2, 24, symoff, 2, stroff, len(strtab))
       main = struct.pack("<IIQQ", 0x80000028, 24, 0xF8, 0)
       return hdr + seg + sec + sym + main + text + syms + strtab

   obj, exe = ba.parse(make_obj(0xF9000001), 1), ba.parse(make_exe(0xF9000001), 2)
   oleaf, ocaller, oword, opc = ba.bind(obj, 20, 8)
   eleaf, ecaller, eword, epc = ba.bind(exe, 20, 8)
   assert ba.pair_identity(oleaf, eleaf, "positive") == [0xF9400002, 0xF9000001, 0xAA0203E0, 0xD65F03C0]
   reloc = ba.object_call_relocation(obj, ocaller, oword, opc, oleaf)
   call = ba.linked_call(eword, epc, eleaf["entry"])
   controls = ba.negative_controls(obj, exe, oleaf, eleaf, ocaller, reloc, call, "positive", None, oword, opc)
   assert len(controls) == 13
   print("Verified 13 Mach-O negative controls successfully.")
   PY
   ```
3. **Shared Pilot Manifest, 20-Byte ELF Header Regression, and SIMD/Union Specimen:**
   - Verify `support/rust-assembly-zerocopy-shared-pilot-2026/package-manifest.json`, `support/rust-assembly-zerocopy-shared-pilot-2026/RESULTS-FREEZE.json`, and run `python3 support/rust-assembly-zerocopy-shared-pilot-2026/regress_runtime_header_v2.py` to check the 28 pure-data 18-byte vs. 20-byte ELF header controls recorded in `support/rust-assembly-zerocopy-shared-pilot-2026/runtime-header-v2-regression.json`.
   - On an AArch64 host with NEON support and a nightly toolchain supporting `#![feature(portable_simd)]`, compile and run `support/rust-neon-vector-and-union-representation-control-1d81eb4/simd_union.rs` with `rustc --edition=2024 -C opt-level=1` and verify that all 64 SIMD/NEON addition cases and 8 union byte-reinterpretation cases exit with status `0`.
   - When updating `AeneasVerif/charon` or `rust-lang/rust`, diff `compiler/rustc_middle/src/mir/syntax.rs`, `charon/src/bin/charon-driver/translate/translate_bodies.rs`, `charon/src/transform/control_flow/ullbc_to_llbc.rs`, and `charon/src/bin/charon-driver/translate/translate_crate.rs` to check whether `InlineAsm` operands/options or `GlobalAsm` items have been added to ULLBC/LLBC.
