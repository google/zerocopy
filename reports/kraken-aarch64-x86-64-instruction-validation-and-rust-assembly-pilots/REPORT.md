# Kraken AArch64 and x86-64 Instruction Validation, Byte-Leaf Resource Adapters, and Rust Assembly Pilots

## Summary

At `AeneasVerif/kraken` commit `8af78062037bc237b341d20252aafd1797c1bcb7` (evaluated under Lean `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, and cross-checked against Rust `1.99.0`, commit `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, LLVM `23.1.1` on `aarch64-apple-darwin`), four complementary investigations establish the relationship between Kraken's formal AArch64/x86-64 semantics, primary architecture manuals, compiled Rust inline/naked assembly artifacts, and cross-foundation assembly proofs (`awslabs/s2n-bignum@4d1356a7470663c752660a59375dc3a9ef548428`):

1. **Three-Way AArch64 Instruction Validation Across 1,290 Register/Flag Cases (`support/kraken-aarch64-selected-instruction-validation-8af7806/`):**
   - Actual Kraken execution (`InstructionEval.lean`), an independent arbitrary-precision Python mathematical oracle (`validate.py`), and native AArch64 inline assembly compiled with `rustc` at `-C opt-level=0` and `-C opt-level=3` (`native.rs`, reading flags via `MRS NZCV`) produce byte-identical `(result, NZCV)` outputs (SHA-256 `9962a3b19b153fd776679718fcb3a7f3aea897902d2c1a6decc8feb46a171c90`) across 1,290 deterministic cases spanning 7 instruction/width forms: `adds x0, x1, x2` (225 cases), `adcs x0, x1, x2` (450 cases), `add w0, w1, w2` (225 cases), `lslv x0, x1, x2` (180 cases), `lslv w0, w1, w2` (180 cases), `rev x0, x1` (15 cases), and `rev w0, w1` (15 cases). Eight deliberately wrong semantic alternatives (ignoring `ADCS` carry-in, clearing output carry or signed overflow, preserving upper 32 bits on `W`-register writes, unmasked 32/64-bit shift counts, and bit-reversal instead of byte-reversal) are each refuted by explicit witness cases (`negative-controls.json`).
2. **Checked AArch64 Byte-Leaf Decoder, Effect-Trace Equality, and Separated-Byte Resource Adapter (`support/kraken-checked-aarch64-byte-leaf-resource-adapter-8af7806/`):**
   - `Adapter.lean` implements a field-based little-endian AArch64 instruction decoder and layout checker in Lean 4, proving `decode_load_iff`, `decode_ret_iff`, `encodeLE_wordLE`, `accepted_iff_canonical`, `certificate_iff`, `actual_effects`, `complete_trace`, `permission_iff`, `zero_writes`, `resource_load`, and `checked_resource_contract` for the 8-byte leaf `00004039c0035fd6` (`ldrb w0, [x0]; ret`). Under a strict permission interpreter and separated byte resource `Eq(v.At base) ⋆ R`, the theorem proves the exact 4-step ordered effect trace (`execute [pc, pc+4)`, `read [X0, X0+1)`, `execute [pc+4, pc+8)`, `return X30`), full `MachineData` framing (only `X0` updated to the zero-extended byte `v`, with `X1`–`X30`, `SP`, `NZCV`, and `dmem` preserved), and zero write requests.
   - `BindingCertificates.lean` binds four compiled slices (`-O0` and `-O3` object `.o` and linked Mach-O executables from `leaf.rs`), and both native builds pass 16,640 valid-reference calls (checksum `9369878136d25c80`), while 8 named instruction mutants, all 2,040 single-byte substitutions, and 12 truncated-file controls are rejected.
3. **AArch64 Rust Inline and Naked Assembly Addition Pilot and Link/Deployment Obligation Taxonomy (`support/kraken-rust-assembly-pilot-8af7806/`):**
   - `KrakenPilot.lean` proves `addBody_correct` (`add x0, x0, x1`) and `addReturn_correct` (`add x0, x0, x1; ret` with full `MachineData` framing and `pc = X30`) using only `{propext, Classical.choice, Quot.sound}`.
   - `pilot.rs` compares pure-Rust `wrapping_add`, register-class `asm!`, and `naked_asm!` (`_naked_add` bytes `0000018bc0035fd6` and `_naked_store` bytes `010000f9c0035fd6`) across 8,292 input pairs plus 256 byte-load and 10 `u64`-store checks at `-O0` and `-O3`. `macho_binding.py` and `upgrade_control.py` bind the `__TEXT,__text` symbol slices and demonstrate that mutating `add` to `sub` in `changed.rs` invalidates the `_naked_add` byte claim while leaving `_naked_store` intact.
4. **Checked x86-64 System V Leaf Return, Stack Separation Frame, Host Embedding, and `s2n-bignum` Cross-Foundation Comparison (`support/kraken-x64-sysv-leaf-return-and-cross-foundation-pilot/`):**
   - `X64Pilot.lean` proves `addBody_correct`, `addReturn_correct`, and the bidirectional characterization `addReturn_iff` for `leaq (%rdi, %rsi, 1), %rax; ret` over an 8-byte separated stack return-address cell `d.dmem =⋆ Eq (returnAddress.At d.regs.rsp.toBitVec) ⋆ R`, proving `RAX = RDI + RSI`, `RSP = initial RSP + 8`, `pc = returnAddress`, and preservation of all other general registers, ZMM registers, flags, and `dmem`.
   - `host_addReturn_iff`, `host_two_step_composition`, and `host_permission_iff` prove a 2-step `step1` embedding inside a 4-directive host (`nop; leaq; ret; nop` at addresses `4096, 4097, 4101, 4102`), refuting wrong return targets (`wrong_return_rejected`), hidden `%rbx` clobbers (`hidden_clobber_rejected`), and 7-byte under-permitted stack regions (`seven_byte_stack_prefix_rejected`).
   - Comparing Kraken X64 (`leaq; ret`), Kraken AArch64 (`AArch64Peer.lean`, `add x0, x0, x1; ret`), and `awslabs/s2n-bignum` (`BIGNUM_ADD_SUBROUTINE_CORRECT` in `x86/proofs/bignum_add.ml:697`, whose 185-byte ELF symbol `bignum_add` matches `bignum_add_mc` with SHA-256 `2ec605ad88338f62739324fed88147729e3a723be4197eb5480d07eee6153216`) isolates how three distinct machine interfaces realize `(a + b) mod 2^64`.

## Applicability

The findings in this report apply to the concrete repositories, toolchains, and architectural references listed in `REPORT.json`:

1. **Kraken Formal ISA Models (`AeneasVerif/kraken@8af78062037bc237b341d20252aafd1797c1bcb7`):**
   - Both `Kraken.AArch64` (`Kraken/AArch64/Syntax.lean`, `Kraken/AArch64/Semantics.lean`, `Kraken/AArch64/OmniSemantics.lean`) and `Kraken.X64` (`Kraken/X64/Syntax.lean`, `Kraken/X64/Semantics.lean`, `Kraken/X64/OmniSemantics.lean`, `Kraken/SeparationMem.lean`) are examined at commit `8af78062037bc237b341d20252aafd1797c1bcb7` (public source archive SHA-256 `b2acfb541396a9cacec36bf4e954b9294ae4272d4d32e61f73c8716cf2de1d60`).
2. **Lean 4 Kernel and Evaluator (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, version `v4.34.1` on `arm64-apple-darwin24.6.0`):**
   - Used to build the 43 Lake targets of `AeneasVerif/kraken` and typecheck/execute `InstructionEval.lean`, `Adapter.lean`, `BindingCertificates.lean`, `KrakenPilot.lean`, `X64Pilot.lean`, `AArch64Peer.lean`, and `HostQuery.lean`. Although Kraken's `lean-toolchain` file requests `nightly`, all proofs and evaluations in this package were executed on Lean `v4.34.1` (and the unchanged `Adapter.lean`, `BindingCertificates.lean`, `AArch64Pilot.lean`, and `X64Pilot.lean` files were also verified to replay cleanly on `4.36.0`).
3. **Rust Compiler and Native Execution Target (`rust-lang/rust@b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, `rustc 1.99.0`, LLVM `23.1.1`, host `aarch64-apple-darwin`, and `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb`):**
   - Used to compile and run the 1,290-case inline-assembly differential harness (`native.rs`), the 16,640-call `naked_asm!` byte-load harness (`leaf.rs`), and the 8,292-pair `asm!` / `naked_asm!` addition/load/store pilot (`pilot.rs`) at `-C opt-level=0` and `-C opt-level=3` with `-C panic=abort`.
4. **Authoritative Arm Documentation, Linker/LTO Specifications, and `s2n-bignum` Reference Subject:**
   - Arm instruction descriptions for `ADDS`/`ADCS` (`https://documentation-service.arm.com/static/68da52dfbd7cab51328c0622`, revision `2025-09_rel`, build `2025-09-23 11:45:10`), `LSLV`/`REV`/`LDRB`/`RET` (`https://documentation-service.arm.com/static/67e40f3398aa3c3b6eea6a85`, revision `aarchmrs v2025-03_rel, pseudocode v2025-03_rel`, build `2025-03-21T17:41`), and the *Armv8-A Instruction Set Architecture* guide (`ARM062-948681440-3280`, `2020-07-03`).
   - LLVM ThinLTO documentation (`https://clang.llvm.org/docs/ThinLTO.html`), LLD linking concepts (`https://lld.llvm.org/NewLLD.html`), RISC-V ELF linker relaxation specification (`https://docs.riscv.org/reference/abi/riscv-elf-linker-relaxation.html`), and `awslabs/s2n-bignum@4d1356a7470663c752660a59375dc3a9ef548428` (`x86/proofs/bignum_add.ml`).

## Findings

### 1. Three-Way AArch64 Instruction Validation Across 1,290 Cases (`support/kraken-aarch64-selected-instruction-validation-8af7806/`)

#### 1.1 Corpus Design, Mathematical Oracle, and Byte-Identical Three-Way Agreement

`support/kraken-aarch64-selected-instruction-validation-8af7806/InstructionEval.lean` elaborates seven AArch64 instruction/width forms through Kraken's `parseAArch64` macro (`support/kraken-aarch64-selected-instruction-validation-8af7806/parsed-programs.log`), producing single-instruction programs at address `0` with declared size `4` (`ADDS_s` with `LSL 0`, `ADCS`, `ADD_s` at `.W32`, `LSLV` at `.W64`/`.W32`, and `REV` at `.W64`/`.W32`):

| Instruction / Width | Cases | Main Discriminating Boundary |
| :--- | ---: | :--- |
| `adds x0, x1, x2` | 225 | 64-bit wrapping result, unsigned carry (`C`), signed overflow (`V`), sign/zero (`N`/`Z`) |
| `adcs x0, x1, x2` | 450 | Both input-carry values (`C_in ∈ {0, 1}`) and all resulting `NZCV` flags |
| `add w0, w1, w2` | 225 | Low-32-bit wrapping sum, upper-32-bit zero-extension of `X0`, and `NZCV` preservation |
| `lslv x0, x1, x2` | 180 | Shift count masked modulo 64 (`x2 mod 64`) and `NZCV` preservation |
| `lslv w0, w1, w2` | 180 | Shift count masked modulo 32 (`w2 mod 32`), upper-32-bit zero-extension, and `NZCV` preservation |
| `rev x0, x1` | 15 | 8-byte endian reversal and `NZCV` preservation |
| `rev w0, w1` | 15 | Low 4-byte endian reversal, upper-32-bit zero-extension, and `NZCV` preservation |

All 1,290 deterministic input tuples are recorded in `support/kraken-aarch64-selected-instruction-validation-8af7806/cases.tsv` using all pairs from 15 explicit 64-bit edge words (zero, small integers, byte/word/sign boundaries, `0x7fffffff_ffffffff`, `0x80000000_00000000`, `0xffffffff_ffffffff`, and two asymmetric byte patterns) and 12 shift counts (`0, 1, 7, 31, 32, 33, 63, 64, 65, 127, 128, 2^64 - 1`).

Three independent evaluators were run over `cases.tsv`:
1. **Independent Mathematical Oracle (`support/kraken-aarch64-selected-instruction-validation-8af7806/validate.py`):** Computes arbitrary-precision unsigned totals and signed two's-complement range checks for `N` (bit 63), `Z` (result == 0), `C` (unsigned sum $\ge 2^{64}$), and `V` (signed sum $\notin [-2^{63}, 2^{63}-1]$), packing `NZCV` as a 4-bit integer `(N << 3) | (Z << 2) | (C << 1) | V`.
2. **Kraken Evaluator (`InstructionEval.lean`):** Consumes exactly one `require_exec_access [0, 4)` effect, requires final `pc = 4`, rejects all read/write/nonmemory/undefined/unaligned effects, and checks equality against the complete initial `MachineData` with only `X0` (initialized to `0xffffffff_ffffffff`) and `NZCV` (initialized to `6` for non-flag instructions) updated.
3. **Native AArch64 Inline Assembly (`support/kraken-aarch64-selected-instruction-validation-8af7806/native.rs`):** Executes actual `adds`, `adcs` (setting input carry via `cmp {carry}, #1`), `add w`, `lslv`, and `rev` followed by `mrs {nzcv}, nzcv` at both `-C opt-level=0` (`native-O0-asm-blocks.s`) and `-C opt-level=3` (`native-O3-asm-blocks.s`). Non-flag instructions use early `out(reg)` so `X0` is pre-filled with `0xffffffff_ffffffff` before instruction execution without aliasing live inputs; `adds`/`adcs` use `lateout(reg)`.

All four output streams—`oracle.tsv`, `kraken.tsv`, `native-O0.tsv`, and `native-O3.tsv`—are byte-for-byte identical across all 1,290 rows, with SHA-256 digest `9962a3b19b153fd776679718fcb3a7f3aea897902d2c1a6decc8feb46a171c90` (`support/kraken-aarch64-selected-instruction-validation-8af7806/results.json`).

Basis: **execution** + **source** + **documentation**.

#### 1.2 Primary Source and Arm Specification Alignment and Eight Semantic Discriminators

Inspecting `Kraken/AArch64/Semantics.lean` at `8af78062037bc237b341d20252aafd1797c1bcb7` alongside the Arm specification entries (`support/kraken-aarch64-selected-instruction-validation-8af7806/primary-document-observations.json`) confirms why the three implementations agree:
- **`Reg64s.setRegOrZr` (`Kraken/AArch64/Semantics.lean:133`):** Zero-extends 32-bit `.W32` writes to 64 bits, matching the Armv8-A ISA guide (Issue 1.1, Sections 7.1 and 9.2).
- **`StatusFlags.adds` and `ADCS` (`Kraken/AArch64/Semantics.lean:417, 599`):** Compute `C` and `V` by comparing the mathematical unsigned and signed sums (including `PSTATE.C` for `ADCS`) against the truncated 64-bit result's unsigned and signed interpretations, matching Arm's September 2025 `ADCS` (p. 18) and `ADDS` shifted-register (p. 28) pseudocode.
- **`LSLV` and `REV` (`Kraken/AArch64/Semantics.lean:769`):** `LSLV` reduces the shift amount modulo register bit-width (`32` or `64`), and `REV` reverses byte order via staged byte/halfword/word exchanges separately for `.W32` and `.W64`, matching Arm's March 2025 `LSLV` (p. 626) and `REV` (p. 758) descriptions.

Eight wrong semantic rules are refuted by explicit cases in `support/kraken-aarch64-selected-instruction-validation-8af7806/negative-controls.json`:

| Wrong Semantic Rule | Concrete Distinguishing Case | Actual Oracle / Kraken / Native Result |
| :--- | :--- | :--- |
| Ignore `ADCS` carry input | `0 + 0`, `C = 1` | `result = 1`, `NZCV = 0` |
| Clear output carry `C` | `1 + (2^64 - 1)` | `result = 0`, `NZCV = 6` (`Z=1, C=1`) |
| Clear signed overflow `V` | `1 + (2^63 - 1)` | `result = 2^63`, `NZCV = 9` (`N=1, V=1`) |
| Preserve old `W` destination upper 32 bits | `add w0, w1, w2` on `0 + 0` with initial `X0 = 2^64 - 1` | `X0 = 0` |
| Unmasked 64-bit shift count | `lslv x0, x1, x2` on `1 << 64` | `X0 = 1` |
| Unmasked 32-bit shift count | `lslv w0, w1, w2` on `1 << 32` | `X0 = 1` |
| Reverse bits instead of 8 bytes | `rev x0, x1` on `1` | `X0 = 2^56` |
| Reverse bits instead of 4 bytes | `rev w0, w1` on `1` | `X0 = 2^24` |

Basis: **source** + **documentation** + **execution** + **derived**.

### 2. Checked AArch64 Byte-Leaf Resource Adapter and Native Mach-O Binding (`support/kraken-checked-aarch64-byte-leaf-resource-adapter-8af7806/`)

#### 2.1 Field-Based Byte Decoding, Complete Effect Trace, and Separated Byte Resource Contract

`support/kraken-checked-aarch64-byte-leaf-resource-adapter-8af7806/Adapter.lean` eliminates assembly-text parsing and external layout trust for a 2-instruction AArch64 leaf (`ldrb w0, [x0]; ret`, canonical bytes `00004039c0035fd6`):
- **Byte Decoder and Canonical Equivalence:** `Adapter.lean` implements a little-endian 32-bit word reader, a field-based instruction decoder recognizing unsigned-offset `LDRB` (`base = X0`, `dest = W0` across all 4,096 12-bit immediate offsets, reviewed against the March 2025 Arm reference pp. 518–519) and `RET X30` (p. 751), and a layout contract checker requiring 4-byte code alignment, non-negative `Int64` start address, and non-wrapping instruction endpoints `< Int64.maxValue`. Theorems `decode_load_iff`, `decode_ret_iff`, `encodeLE_wordLE`, `accepted_iff_canonical`, and `certificate_iff` prove that the zero-offset leaf contract accepts **if and only if** the input byte list is `00004039c0035fd6` and binds the generated Kraken `Executable` with 4-byte instruction sizes.
- **Complete Effect-Tree Equality and Strict Permission Trace:** Theorem `actual_effects` unfolds Kraken's operational semantics and proves exact equality to the complete `Effects` tree:
  ```text
  execute [pc, pc + 4)
  read    [X0, X0 + 1)
  execute [pc + 4, pc + 8)
  return  X30, with X0 = zero-extended loaded byte
  ```
  `complete_trace`, `permission_iff`, `zero_writes`, `actual_load_step`, `actual_ret_step`, and `layout_endpoints` prove that under the stricter permission interpreter, execution requires exactly the two 4-byte execute ranges and the 1-byte read at `[X0, X0 + 1)`, emits zero write requests, and steps from `pc` to `pc + 4` and then to `X30`.
- **Separated Byte-Map Resource Theorem (`checked_resource_contract`):** Using Kraken's `Mem.loadInt_sep` (`resource_load`) and `byte_value` (which handles all `UInt8` values including `v ≥ 128` via unsigned reconstruction), `checked_resource_contract` proves that for any `MachineData` `d`, byte `v : UInt8`, 64-bit address `base`, and disjoint memory frame predicate `R`, if `X0 = base` and `d.dmem` satisfies `Eq(v.At base) ⋆ R`, then the leaf returns to `X30` with `X0 = v.toUInt64`, preserving `X1`–`X30`, `SP`, `NZCV`, and the entire data-memory map `Eq(v.At base) ⋆ R` (`result_preserves_resource`).

All 40 audited declarations across `Adapter.lean` and `BindingCertificates.lean` (`support/kraken-checked-aarch64-byte-leaf-resource-adapter-8af7806/logs/replay-results.json`, `adapter-proof.log`, `binding-proof.log`) depend only on subsets of `{propext, Classical.choice, Quot.sound}` with zero `sorryAx` and zero native-evaluation axioms.

Basis: **source** + **execution** + **documentation**.

#### 2.2 Compiled Mach-O Slices, 16,640 Native Calls, and Exhaustive Mutation Controls

`support/kraken-checked-aarch64-byte-leaf-resource-adapter-8af7806/leaf.rs` defines the `naked_asm!("ldrb w0, [x0]", "ret")` leaf and a safe `&u8` wrapper, compiled with `rustc 1.99.0` at `-O0` and `-O3` into object files (`artifacts/leaf-O0.o`, `artifacts/leaf-O3.o`) and linked executables (`artifacts/leaf-O0`, `artifacts/leaf-O3`).
- `binding.py` (`logs/binding.json`) verifies the thin `arm64` Mach-O headers, section bounds, 4-byte alignment, and absence of relocations overlapping the 8-byte symbol slice, and `BindingCertificates.lean` kernel-checks acceptance of all four concrete imported slices at their recorded addresses.
- Both `-O0` and `-O3` native executables (`logs/native-O0.log`, `logs/native-O3.log`) execute the leaf across all 256 byte values at 65 buffer offsets (`16,640` calls), matching ordinary Rust dereferences with checksum `9369878136d25c80`.
- Negative controls (`validate.py` and `Adapter.lean`) reject:
  1. Every byte list distinct from `00004039c0035fd6` (universal theorem) and arbitrary wrong lengths;
  2. Eight named instruction mutants (wider load, different base register, clobbered destination, offset `1`, different return register, inserted hidden load, inserted clobber, and truncation);
  3. All $8 \times 255 = 2,040$ single-byte substitutions (exhaustively checked by the executable data checker, plus re-imported single-byte file mutations rejected in Lean);
  4. Twelve truncated-file Mach-O importer controls, an unaligned `pc`, and a wrapping code layout;
  5. Refuted specifications for zero-byte readable spans, wrong return register, and wrong `X19` frame preservation.

Basis: **execution** + **source**.

### 3. AArch64 Rust Inline/Naked Addition Pilot and Link/Deployment Obligation Taxonomy (`support/kraken-rust-assembly-pilot-8af7806/`)

#### 3.1 Universal Kraken Addition Proofs vs. 8,292-Pair Native Rust Execution and Upgrade Controls

In `support/kraken-rust-assembly-pilot-8af7806/KrakenPilot.lean` (checked against a clean 43-job `lake build Kraken KrakenAArch64` under Lean `v4.34.1`, logged in `kraken-proof.stdout`), two theorems are proved using only `{propext, Classical.choice, Quot.sound}`:
- `addBody_correct`: For arbitrary `MachineData` and layout, Kraken's parsed `add x0, x0, x1` updates `X0` to the `UInt64` modular sum while leaving modeled memory, `SP`, and status flags unchanged.
- `addReturn_correct`: For parsed `add x0, x0, x1; ret`, the entire resulting `MachineData` record equals the initial record with only `X0` updated (preserving all non-output registers `X1`–`X30`, `SP`, `NZCV`, and `dmem`), and the next instruction pointer equals initial `X30`.

In `support/kraken-rust-assembly-pilot-8af7806/pilot.rs` (compiled to `pilot.ll`, `pilot.s`, `pilot.o`, and `-O0`/`-O3` executables recorded in `native-results.json`), five functions are tested:
1. Pure-Rust `wrapping_add` (`extern "C"`);
2. Inline `asm!("add {out}, {a}, {b}", ...)` with late output;
3. Whole-function `naked_asm!("add x0, x0, x1", "ret")` (`_naked_add`, bytes `0000018bc0035fd6`);
4. Inline `ldrb` byte load on a live initialized byte (256 inputs with surrounding-byte checks);
5. Whole-function `naked_asm!("str x1, [x0]", "ret")` (`_naked_store`, bytes `010000f9c0035fd6`, 10 inputs on an aligned exclusive `u64` slot with surrounding-word checks).

Both `-O0` and `-O3` native runs (`native-0.stdout`, `native-3.stdout`) pass 100 boundary pairs plus 8,192 deterministic generated pairs (`8,292` total). `macho_binding.py` (`binding-results.json`) binds the 8-byte `__TEXT,__text` ranges for `_naked_add` and `_naked_store` across `pilot.o` and both linked executables and rejects 1-byte mutations, 3 truncated inputs, and wrong expected patterns. Furthermore, `upgrade_control.py` (`upgrade-control/changed.rs`, `upgrade-control/changed.o`, `upgrade-control/result.json`) mutates `_naked_add` from `add` to `sub`, recompiles, and verifies that the `_naked_add` byte binding fails while `_naked_store` still passes.

#### 3.2 Compilation, Linking, and Deployment Certificate Obligations and Remaining Bridge Arrows

Synthesizing LLVM's ThinLTO specification, LLD's identical-code folding and base-relocation semantics, and the RISC-V ELF linker relaxation specification with the Mach-O binding experiments yields a six-part taxonomy of what an assembly verification certificate must bind across compilation and linking:

| Transformation / Link Mechanism | Certificate Binding or Proof Obligation |
| :--- | :--- |
| **Symbols and code/data sections** | Bind exact byte range, section permissions/interpretation, entry points, and all code/data referenced by execution. |
| **Relocations, PIC, GOT/PLT, and linker thunks** | Bind resolved targets and environment, or prove a theorem parameterized by admitted relocation values and verify any linker-generated thunk/veneer. |
| **Linker relaxation and instruction-size changes** | Decode and validate layout *after* post-link relaxation, or prove semantic preservation across deleted bytes and shifted branch/data offsets. |
| **LTO, outlining, inlining, and identical-code folding (ICF)** | Enumerate final post-LTO instances and contracts; shared post-ICF code bytes do not uniquely identify a single source call context. |
| **Dynamic interposition and runtime CPU feature dispatch** | Verify every reachable dispatch implementation under its required `target_feature` and ABI domain. |
| **OS loading, ASLR, and live patching** | Establish runtime address/alignment invariants and code immutability for the duration of the verified execution claim. |

Across the end-to-end Rust-to-Kraken verification chain, five distinct bridge arrows must be distinguished rather than conflated into a single "verified assembly" claim:

| Bridge Arrow | Evidence Established in These Pilots | Remaining Unproved Stronger Obligation |
| :--- | :--- | :--- |
| **Rust function $\rightarrow$ emitted machine interface** | Pinned `rustc 1.99.0` source, LLVM IR (`pilot.ll`), assembly (`pilot.s`), and `-O0`/`-O3` object observations | Mechanized compiler/codegen correspondence from Rust AST/MIR to emitted assembly |
| **Kraken text/bytes $\rightarrow$ modeled transition** | Closed Lean proofs (`addBody_correct`, `addReturn_correct`, `checked_resource_contract`) + 1,290-case native differential validation | Universal equivalence theorem between Kraken's semantics and an authoritative Arm ASL/Sail or x86-64 ISA specification |
| **Selected symbol $\rightarrow$ object/linked bytes** | Bounded Mach-O (`macho_binding.py`, `binding.py`) and ELF (`s2n`) slice checkers + checked Lean byte decoder (`Adapter.lean`) + mutation controls | Formally verified Mach-O/ELF parser, relocation resolver, and OS loader model |
| **C / Rust ABI inputs $\rightarrow$ machine entry state** | Reviewed AAPCS64 / System V register conventions, `naked_asm!` rules, and 16,640 + 8,292 native calls | Formal ABI lowering theorem connecting Rust function signatures to initial `MachineState` predicates |
| **Machine execution $\rightarrow$ Rust resource-safe continuation** | Full `MachineData` framing + Kraken `Mem.loadInt_sep` separated byte/word cell witnesses (`Eq(v.At base) ⋆ R`) | Formal bridge from Rust/MiniRust allocation, provenance, and shared/mutable borrow lifetimes to Kraken byte-map resources |

Basis: **documentation** + **execution** + **derived**.

### 4. Checked x86-64 System V Leaf Return, Host Embedding, and `s2n-bignum` Comparison (`support/kraken-x64-sysv-leaf-return-and-cross-foundation-pilot/`)

#### 4.1 Full-Frame x86-64 Stack-Return Theorem and Bidirectional `addReturn_iff`

In `support/kraken-x64-sysv-leaf-return-and-cross-foundation-pilot/X64Pilot.lean` (logged in `X64Pilot.log` and `results.json`), the System V x86-64 addition leaf `leaq (%rdi, %rsi, 1), %rax; ret` (`addReturn`) is verified for arbitrary initial `MachineData` `d` and arbitrary `Layout`:
- `bodyState d` updates only `RAX` to `d.rdi + d.rsi` (`leaq` invokes `setReg` in `Kraken/X64/Semantics.lean:494` without modifying status flags or touching memory).
- `returnState d` updates `RAX` to `d.rdi + d.rsi` and `RSP` to `d.rsp + 8` (`ret` in `Kraken/X64/Semantics.lean:744` loads a 64-bit word `.W64` from `RSP`, branches to those bits, and increments `RSP` by 8).
- Using `Mem.loadInt_sep` (`Kraken/SeparationMem.lean:118`), `addReturn_correct` proves that for any 64-bit `returnAddress : UInt64` and disjoint byte-map predicate `R`:
  ```text
  d.dmem =⋆ Eq (returnAddress.At d.regs.rsp.toBitVec) ⋆ R
    → straightlineStep (layout addReturn) (d, layout.start)
        (fun final => final.data = returnState d
                    ∧ final.pc.toBitVec = returnAddress.toBitVec)
  ```
  Because `final.data = returnState d` is a full structure equality on `MachineData`, every general register except `RAX` and `RSP`, every `ZMM` vector register, all six status flags, and the entire byte map `d.dmem` (including `Eq (returnAddress.At ...) ⋆ R`) are preserved.
- `addReturn_iff` proves the stronger bidirectional characterization: for any postcondition `post`, `straightlineStep (layout addReturn) (d, layout.start) post` holds **if and only if** `post ⟨returnState d, ...⟩` holds at the exact calculated return state.

Basis: **source** + **execution**.

#### 4.2 Fixed-Host Embedding (`step1` Composition), Semantic Negative Controls, and Exact Permission Footprint

`X64Pilot.lean` also embeds the 2-instruction leaf inside a 4-directive host program `fixedHost` (`HostQuery.lean`, `HostQuery.log`) and checks its exact step-by-step and permission behavior:

| Directive Index | Directive | Declared Address | Declared Size (Bytes) |
| :--- | :--- | ---: | ---: |
| `0` | Prefix `nop` | `4096` | `1` |
| `1` | `leaq (%rdi, %rsi, 1), %rax` | `4097` | `4` |
| `2` | `ret` | `4101` | `1` |
| `3` | Suffix `nop` | `4102` | `1` |

- **Host Embedding and Two-Step `step1` Composition:** `fixedHost_program_identity` checks the exact laid-out directives (with zero axioms). `host_addReturn_iff` proves that entering `fixedHost` at `pc = 4097` skips the prefix `nop` at `4096` and exits via `ret` before reaching the suffix `nop` at `4102`. `host_two_step_composition` composes the two individual `step1` transitions (`4097 → 4101` with `bodyState d`, and `4101 → returnAddress` with `returnState d`) via `step_cps` / `Eventually` (`Kraken/OmniSemantics.lean:25`).
- **Kernel-Checked Semantic Refutations:**
  - `wrong_return_rejected` proves that when the stack load succeeds, any postcondition demanding return PC bits $\neq \texttt{returnAddress}$ is false under `straightlineStep`.
  - `clobberReturn` inserts `movq $99, %rbx` before `ret`, and `hidden_clobber_rejected` proves that `clobberReturn` refutes the full-frame postcondition whenever initial `%rbx != 99`, even though `RAX` still holds `RDI + RSI`.
- **Exact Emitted Permission Footprint (`PermissionAll`):** Because default `Kraken.X64.Effects.All` (`Kraken/X64/OmniSemantics.lean:13`) erases permission checks, `X64Pilot.lean` defines `PermissionAll readable writable executable post` and proves `addReturn_permission_iff` and `host_permission_iff`:
  ```text
  PermissionAll readable writable executable post actualEffects
    ↔ executable [start, start + size0)
      ∧ executable [start + size0, start + size0 + size1)
      ∧ readable initialRSP 8
      ∧ post exactFinalState
  ```
  `forbidden_stack_read_rejected`, `forbidden_exec_rejected`, `seven_byte_stack_prefix_rejected`, and `eight_byte_stack_region_positive` prove that 7 permitted stack bytes at `RSP` fail the 8-byte `ret` stack read even when all 8 bytes are mapped in `dmem`, whereas an 8-byte non-wrapping permitted stack region plus the two execute ranges (`[4097, 4101)` and `[4101, 4102)`) suffices.

All 18 X64 semantic theorems in `X64Pilot.lean` and the 2 rechecked AArch64 peer theorems in `AArch64Peer.lean` (`AArch64Peer.log`) have exact axiom closure `{propext, Classical.choice, Quot.sound}`, with zero `sorryAx` and zero `bv_decide` native axioms.

Basis: **source** + **execution**.

#### 4.3 Cross-Foundation Comparison with `awslabs/s2n-bignum` (`BIGNUM_ADD_SUBROUTINE_CORRECT`)

To compare Kraken's X64 and AArch64 addition leaves against an established external assembly verification development (`awslabs/s2n-bignum@4d1356a7470663c752660a59375dc3a9ef548428`), `support/kraken-x64-sysv-leaf-return-and-cross-foundation-pilot/run_pilot.py` and `s2n/object_binding.json` (`s2n/object_binding.log`) inspect `BIGNUM_ADD_SUBROUTINE_CORRECT` (`x86/proofs/bignum_add.ml:697`) and `bignum_add_mc` (`x86/proofs/bignum_add.ml:15`):
- The compiled ELF object (`SHA-256` `777578078e4239a142d2576fdb8ffb1dbe988d03711305092822e1d7cadf0797`) defines a 185-byte `bignum_add` symbol (`SHA-256` `2ec605ad88338f62739324fed88147729e3a723be4197eb5480d07eee6153216`) that is byte-for-byte identical to the 185-byte `bignum_add_mc` proof literal in `bignum_add.ml`, while the ELF importer rejects a 1-byte code patch, a mutated ELF machine header, and a wrong symbol lookup.
- Specializing `BIGNUM_ADD_SUBROUTINE_CORRECT` to single-limb lengths `m = n = p = 1` highlights how the three verified routines compute the same mathematical sum `(a + b) mod 2^64` through distinct machine interfaces:

| Verification Route | Input Representation | Low-64-Bit Sum Location | Return & Resource Mechanism | Verified Evidence in This Package |
| :--- | :--- | :--- | :--- | :--- |
| **Kraken X64 leaf (`X64Pilot.lean`)** | `UInt64` values in `RDI`, `RSI` | Register `RAX` | 8-byte separated cell at `RSP` (`RSP += 8`); full `MachineData` frame | Universal Lean 4 body/return, host-embedding, permission, and refutation theorems |
| **Kraken AArch64 peer (`KrakenPilot.lean` / `AArch64Peer.lean`)** | `UInt64` values in `X0`, `X1` | Register `X0` | Link register `X30` (`pc = X30`); full `MachineData` frame | Universal Lean 4 body/return theorems + 8,292-pair native `-O0`/`-O3` execution + Mach-O binding |
| **`s2n-bignum` (`m = n = p = 1` specialization)** | 1-limb memory buffers + 6 System V ABI arguments | Output memory buffer limb (`RAX` returns carry) | System V stack return + code/buffer non-aliasing premises in HOL Light | Upstream theorem inspection + 185-byte ELF-to-`bignum_add_mc` equality and mutation controls (no HOL Light replay) |

Basis: **source** + **execution** + **derived**.

## Boundaries

- **Known not to apply (finite differential testing vs. universal ISA equivalence):** The 1,290-case three-way AArch64 validation (`support/kraken-aarch64-selected-instruction-validation-8af7806/`), the 16,640-call `ldrb` test (`leaf.rs`), and the 8,292-pair `add` test (`pilot.rs`) establish finite empirical agreement, not a universal per-instruction refinement theorem against a formal Arm ASL/Sail or Intel/AMD x86-64 specification.
- **Known not to apply (Arm Guarded Control Stack and unmodeled architectural state):** Arm's `RET` specification performs a Guarded Control Stack (GCS) record access and pointer update when GCS is enabled and updates branch-type (`BTYPE`) state. Because Kraken's AArch64 `RET` (`Kraken/AArch64/Semantics.lean`) models neither GCS nor FP/SIMD/system registers, the "complete access trace" and "full `MachineData` frame" theorems in `Adapter.lean` and `KrakenPilot.lean` apply only to hardware configurations where GCS is disabled and within Kraken's modeled scalar state.
- **Known not to apply (Kraken byte-map cells vs. Rust/MiniRust provenance and borrow state):** Kraken's separated byte-map witnesses (`Eq(v.At base) ⋆ R` and `Eq(returnAddress.At rsp) ⋆ R`) model concrete `UInt64`-indexed memory bytes; they do not encode MiniRust allocation IDs, pointer provenance, lifetime bounds, or fractional shared-reference (`&u8`) borrow permissions.
- **Not examined:**
  - Formal verification of the Python Mach-O (`macho_binding.py`, `binding.py`) and ELF (`s2n`) importers or OS dynamic loader / ASLR address placement;
  - A verified x86-64 binary decoder/encoder connecting `leaq (%rdi, %rsi, 1), %rax; ret` in `X64Pilot.lean` to assembled machine bytes;
  - Live replay of the HOL Light proof of `BIGNUM_ADD_SUBROUTINE_CORRECT` (prerequisites recorded in `support/kraken-checked-aarch64-byte-leaf-resource-adapter-8af7806/prerequisites.md`, `primary-prerequisites/hol-light-Makefile`, and `primary-prerequisites/s2n-ci.yml`).

## Evidence

All primary-source manifests, Lean proof files, Rust harnesses, compiled Mach-O artifacts, and execution logs are preserved in the four `support/` subdirectories of this package (all observed `2026-10-14`):

1. **`support/kraken-aarch64-selected-instruction-validation-8af7806/`:**
   - `InstructionEval.lean`, `parsed-programs.log`, `cases.tsv`, `oracle.tsv`, `kraken.tsv`, `native-O0.tsv`, `native-O3.tsv`, `smoke.tsv`, `native.rs`, `validate.py`.
   - `native-O0-asm-blocks.s`, `native-O3-asm-blocks.s`, `native-O0-complete.s.gz`, `native-O3-complete.s.gz`, `native-O0-build.log`, `native-O3-build.log`, `lean-version.log`, `rustc-version.log`.
   - `results.json`, `negative-controls.json`, `primary-document-observations.json`, `host-observation.json`, `source-manifest.json`, `package-manifest.json`, `package-validation.json`, `coverage.json`, and `development/` (`README.md`, `first-validation-results.json`, `lean-smoke.log` through `lean-smoke5.log`, `native-O0-first-build.log`).
2. **`support/kraken-checked-aarch64-byte-leaf-resource-adapter-8af7806/`:**
   - `Adapter.lean`, `BindingCertificates.lean`, `Query.lean`, `LayoutQuery.lean`, `ValueQuery.lean`, `leaf.rs`, `binding.py`, `validate.py`, `replay.py`, `prerequisites.md`.
   - `artifacts/leaf-O0`, `artifacts/leaf-O0.o`, `artifacts/leaf-O0.s`, `artifacts/leaf-O3`, `artifacts/leaf-O3.o`, `artifacts/leaf-O3.s`, `primary-prerequisites/hol-light-Makefile`, `primary-prerequisites/s2n-ci.yml`.
   - `source-evidence.json`, `development-status.json`, `package-manifest.json`, `publication-projection.json`, `coverage.json`, and `logs/` (`adapter-proof.log`, `binding-proof.log`, `binding.json`, `replay-results.json`, `replay-commands.json`, `replay-driver.log`, `native-O0.log`, `native-O3.log`, `imported-library-identities.json`, `layout-query.log`, `lean-version.log`, `rust-O0-asm.log`, `rust-O0-link.log`, `rust-O0-obj.log`, `rust-O3-asm.log`, `rust-O3-link.log`, `rust-O3-obj.log`, and `adapter-attempt-01.log` through `adapter-attempt-14.log`).
3. **`support/kraken-rust-assembly-pilot-8af7806/`:**
   - `KrakenPilot.lean`, `kraken-proof.stdout`, `kraken-proof.stderr`, `pilot.rs`, `pilot.ll`, `pilot.s`, `pilot.o`, `macho_binding.py`, `upgrade_control.py`, `revalidate.py`.
   - `results.json`, `native-results.json`, `binding-results.json`, `native-0.stdout`, `native-3.stdout`, `lean-version.stdout`, `rustc-version.stdout`, `source-identities.json`, `kraken-source-file-identities.json`, `kraken-source-observation.json`, `package-manifest.json`, `coverage.json`, and `upgrade-control/` (`changed.rs`, `changed.o`, `compile.stdout`, `compile.stderr`, `result.json`).
4. **`support/kraken-x64-sysv-leaf-return-and-cross-foundation-pilot/`:**
   - `X64Pilot.lean`, `X64Pilot.log`, `AArch64Peer.lean`, `AArch64Peer.log`, `HostQuery.lean`, `HostQuery.log`, `run_pilot.py`.
   - `reused/AArch64Closure.lean`, `reused/AArch64Closure.log`, `reused/X64Closure.lean`, `reused/X64Closure.log`, `reused/cases.json`.
   - `s2n/object_binding.json`, `s2n/object_binding.log`, `results.json`, `source-manifest.json`, `package-manifest.json`, `peer-origin.json`, `development-log-projection.json`, `coverage.json`, and attempt logs (`X64Pilot.attempt1.log` through `X64Pilot.attempt6-host.log.gz`, `X64Pilot.pre-generalization.log`, `X64Pilot.pre-host.log`, `X64Pilot.pre-permissions.log`, `X64Pilot.pre-region.log`).

## Revalidation

Run all commands from this package's root directory (`reports/kraken-aarch64-x86-64-instruction-validation-and-rust-assembly-pilots/`):

1. **Revalidate the 1,290-case three-way AArch64 instruction validation and 8 negative controls:**
   ```bash
   python3 support/kraken-aarch64-selected-instruction-validation-8af7806/validate.py \
     --lean /path/to/lean-4.34.1 \
     --kraken-lib /path/to/kraken-8af7806/.lake/build/lib/lean \
     --rustc /path/to/rustc-1.99.0 \
     --artifact-dir /path/to/scratch/native-build
   ```
2. **Revalidate the AArch64 byte-leaf decoder, separated resource adapter, Mach-O slice bindings, and 16,640 native calls:**
   ```bash
   python3 support/kraken-checked-aarch64-byte-leaf-resource-adapter-8af7806/replay.py \
     --lean /path/to/lean-4.34.1 \
     --rustc /path/to/rustc-1.99.0 \
     --kraken-lib /path/to/kraken-8af7806/.lake/build/lib/lean
   ```
3. **Revalidate the AArch64 `add x0, x0, x1; ret` proof pilot, 8,292-pair native comparison, Mach-O binding, and `add`-to-`sub` upgrade control:**
   ```bash
   python3 support/kraken-rust-assembly-pilot-8af7806/revalidate.py \
     --lean /path/to/lean-4.34.1 \
     --rustc /path/to/rustc-1.99.0 \
     --kraken-lib /path/to/kraken-8af7806/.lake/build/lib/lean
   ```
4. **Revalidate the x86-64 `leaq (%rdi, %rsi, 1), %rax; ret` full-frame return proof, 4-directive host embedding, permission footprint checks, and `s2n-bignum` byte comparison:**
   ```bash
   python3 support/kraken-x64-sysv-leaf-return-and-cross-foundation-pilot/run_pilot.py \
     --lean /path/to/lean-4.34.1 \
     --kraken-lib /path/to/kraken-8af7806/.lake/build/lib/lean
   ```
