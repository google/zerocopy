# Rust Foreign Function Interfaces, ABI Lowering Witnesses, Platform Unwind Metadata, and Machine-Resource Linking

## Summary

Soundly linking Rust source proofs across `extern` foreign declarations, calling-convention boundaries (`extern "C"`, `extern "C-unwind"`, and native `"Rust"`), platform unwind tables (Mach-O Compact Unwind / DWARF `.eh_frame` and Windows x64 COFF `.pdata`/`.xdata`), and machine-code execution requires separating five distinct verification layers that source types and return-value bits conflate:

1. **Foreign Item Declarations vs. Linker Import Identity and Variadic Erasure:**
   In `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), items inside `extern` blocks (`hir::ItemKind::ForeignMod`) have no Rust body (`OwnerNode::body_id` has no foreign-item arm) and separate their Rust `DefId` from their effective linker import symbol (`#[link_name]` in `CodegenFnAttrs.symbol_name` and `#[link_ordinal]` in `link_ordinal`). In `AeneasVerif/charon` (`0.1.210` at `a535e914f74db4fd9e6be7048f4233270d8945c0`), foreign functions translate to `Body::Extern(String)` using the final Rust definition-path segment rather than `#[link_name]` or `#[link_ordinal]`, and `translate_fun_sig` drops `c_variadic: bool` when lowering `TyFnSig` to exported `FunSig`.
2. **Type Layout vs. Function Call ABI (`PassMode`, Hidden `sret`, and Platform Variations):**
   Under the Rust Reference (`src/type-layout.md` and `src/items/external-blocks.md`) and `rustc` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, `compiler/rustc_target/src/callconv/mod.rs` and `compiler/rustc_ty_utils/src/abi.rs`), equal byte size and alignment do not imply identical calling conventions (`support/rust-function-abi-witnesses-b940084/rust-pilot.ll` and `abi_witness.c`): on `aarch64-apple-darwin`, `#[repr(C)] struct Pair { u64, u64 }` lowers to `[2 x i64]` whereas Rust `(u64, u64)` lowers to two `i64` parameters and a `{i64, i64}` return; a 24-byte `#[repr(C)] struct Triple { u64, u64, u64 }` uses a hidden indirect return pointer (`sret([24 x i8])` in `x8`) and an indirect input pointer (`x0`); and `&[u8]` passes pointer plus length with `noundef`, `nonnull`, `readonly`, `align`, and `range` attributes. Across C target triples, the same two-word struct passes in registers on x86-64 SysV (`%rdi/%rsi`) and AArch64 (`x0/x1`), but passes via hidden input and return pointers with XMM vector moves on Windows x86-64 MSVC (`%rcx/%rdx`).
3. **Normal Epilogue Execution vs. Interrupted-Frame Unwind Metadata (DWARF `.eh_frame` and Windows `.pdata`/`.xdata`):**
   Normal function return (`ret`) executes the epilogue instructions directly and never consults unwind tables, whereas stack unwinding recovers caller state from an interrupted mid-body or partial-prologue program counter using platform metadata. In both the native macOS Arm64 `extern "C-unwind"` assembly callback experiment (`support/rust-aarch64-c-unwind-callback-and-metadata-controls-b940084/specimen.rs` and `bounce.s`) and the Windows x64 COFF `.pdata`/`.xdata` experiment (`support/rust-assembly-platform-unwind-contracts-2026/specimen.c`), three metadata-only binary mutations—altering the CFA/frame offset, altering the saved link-register or stack-allocation unwind code, or removing the active FDE / `.pdata` entry—leave 100% of `.text` instructions and normal-return behavior intact while corrupting caller frame recovery during unwinding.
4. **Native AArch64 `extern "C-unwind"` Callback Execution and Live Frame Walking:**
   Executing the 32-byte whole-function assembly bounce (`support/rust-aarch64-c-unwind-callback-and-metadata-controls-b940084/bounce.s`, bound to active DWARF FDE encoding `0x03000014` at `__eh_frame` offset `0x14`) and a matched Rust bounce across four runtime cases (normal return `0x336699cd00336699` and caught typed `ExpectedPanic` payload `0x4534305f554e5744`) verified exact 1-call/1-callback-drop/1-outer-drop ordering (`12`) and live `_Unwind_Backtrace` traversal through the assembly frame's return address (`0x1040348d4`, `start + 20`). Separately, the Rust Reference forbids unwinding out of ordinary `asm!` (`[asm.rules.unwind]`) even when enclosed in an `extern "C-unwind"` function, while permitting unwinding from `global_asm!` functions or `naked_asm!` blocks that emit valid platform unwind directives.
5. **Machine-Resource Linking and Behavioral Equivalence (`ContextBridge.lean`):**
   Connecting an ISA proof (such as Kraken `MachineData` transitions) to Rust/MiniRust semantics requires a relation `R` that tracks allocation liveness, pointer provenance, borrow/aliasing permissions, byte initialization/validity, layout/metadata, and caller continuation invariants beyond raw machine bytes. In `support/rust-machine-resource-linking-and-equivalence/ContextBridge.lean` (checked with zero axioms under Lean `v4.34.1`), `value_equivalence_is_not_context_safety` proves that equal scalar return values can coexist with a corrupted live-borrow flag, `loose_spec_is_not_equivalence` proves that shared satisfaction of a permissive specification does not imply behavioral equivalence, and `context_replacement` factors sound cross-language linking into entry adequacy, prefix safety, behavioral correspondence, and context closure.

## Applicability

This report covers the following upstream compilers, specifications, extractors, and verification frameworks listed in `REPORT.json`:

- **Rust Compiler (`rust-lang/rust`) and Reference (`rust-lang/reference`) Multi-Version Coverage:**
  - **Rust Nightly `nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) and Reference `ad35aca481751a06afeb23820a672b0f3b11a476`:** Inspected for `extern` block HIR/metadata lowering (`hir::ItemKind::ForeignMod`, `#[link_name]`, `#[link_ordinal]`, `c_variadic`) and paired with `AeneasVerif/charon` `0.1.210` (`a535e914f74db4fd9e6be7048f4233270d8945c0`).
  - **Rust 1.99.0 (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, LLVM 23.1.1, `aarch64-apple-darwin`) and Reference `2dafab96d919d6ab2884488e970bf95610ff83eb`:** Used for:
    1. Native compilation and execution of the AArch64 `extern "C-unwind"` whole-function assembly callback bounce (`--edition=2024 -C opt-level=1 -C panic=unwind -C debuginfo=0 -C codegen-units=1 -C force-frame-pointers=yes -C force-unwind-tables=yes`);
    2. Compilation of the safe `extern "C-unwind"` drop-cleanup and `.cfi_personality`/`.cfi_lsda` specimen (`support/rust-assembly-platform-unwind-contracts-2026/cleanup.rs`); and
    3. Inspection and compilation of `callconv::PassMode` and `FnAbi` lowering witnesses (`support/rust-function-abi-witnesses-b940084/rust-pilot.rs`, `-C opt-level=3 -C panic=abort`).
  - **Version-Invariant vs. Version-Specific Behavior:** The normative rules governing `extern` blocks (`[items.extern]`), unwinding ABIs (`[items.fn.extern.unwind]`), prohibition of unwinding from ordinary `asm!` (`[asm.rules.unwind]`), and non-guarantee of native `"Rust"` ABI stability (`[type-layout]`) are invariant across Reference revisions `ad35aca481751a06afeb23820a672b0f3b11a476` and `2dafab96d919d6ab2884488e970bf95610ff83eb`. Specific `FnAbi` LLVM attribute deduction (`arg_attrs_for_rust_scalar`, `fn_abi_adjust_for_deduced_attrs`) and emitted DWARF/LSDA table offsets are specific to `rustc 1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`).
- **Platform ABIs, C Compilers, and Unwind Runtimes:**
  - **Apple macOS Arm64 (`aarch64-apple-darwin`):** MacOSX27.0.sdk headers (`mach-o/compact_unwind_encoding.h`, `unwind.h`, `libunwind.h`, `dlfcn.h`), live `/usr/lib/system/libunwind.dylib` (`_Unwind_Backtrace`), and Apple ARM64 ABI rules (reserved `x18`, 16-byte stack alignment, `x29`/`x30` frame records, and 128-byte red zone).
  - **AAPCS64 (`ARM-software/abi-aa@ec3e2fb69065768aa1caf298813a7808b50bc264`) and SysV x86-64 psABI (`x86-psABIs/x86-64-ABI`).**
  - **Windows x64 (`MicrosoftDocs/cpp-docs@281a0a0eae55fe97f5decd244db18ed5096d4687`):** Version-1 `UNWIND_INFO` (`.xdata`) and `RUNTIME_FUNCTION` (`.pdata`) specifications and cross-target COFF object generation using Apple `clang` 21.0.0 (`clang-2100.3.34.2`, `--target=x86_64-pc-windows-msvc`).
- **Semantic Models and Mechanization Kernel:**
  - **MiniRust (`minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`), Kraken (`AeneasVerif/kraken@8af78062037bc237b341d20252aafd1797c1bcb7`), DimSum (`10.1145/3571220`), and Lean 4.34.1 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):** Used for the machine-to-Rust resource linking factorization and counterexample proofs in `support/rust-machine-resource-linking-and-equivalence/ContextBridge.lean`.

## Findings

### 1. Rust `extern` Foreign Items and `Charon` Extraction Boundaries

**Basis:** `normative` (`rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`) + `source` (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`) + `derived`.

1. **Declarations Without Rust Bodies and Explicit Trust Obligations:**
   Under `src/items/external-blocks.md` (blob `e1704556b5f000c019cd04df63e7e04692454c42`) and `src/items/functions.md` (blob `362b39b5733c385a18e20a928d75f960f1cd427e`), items inside an `extern` block declare functions or statics defined outside the current Rust crate. In `rustc` HIR (`compiler/rustc_hir/src/hir.rs`, blob `59d1b4b5576ee47ea6c994977d40d5a948f139ce`), `ItemKind::ForeignMod { abi, items }` assigns each `ForeignItem` an `OwnerId`, span, and signature, while `OwnerNode::body_id` has no foreign-item arm. Even when a foreign item is marked `safe` inside an `unsafe extern` block (Rust 2024 edition), that qualifier only discharges the syntactic `unsafe` block requirement at Rust call sites—it does not verify the foreign implementation or guarantee that an external static holds a valid bit pattern.
2. **Separation of Rust Item Identity from Linker Import Identity (`#[link_name]` and `#[link_ordinal]`):**
   In `rustc`, `compiler/rustc_metadata/src/foreign_modules.rs` (blob `8a6b2027083d600ab3fbd5c214b92c53cd17b789`) records the module `DefId`, ABI, and member `DefId`s, while `compiler/rustc_codegen_ssa/src/codegen_attrs.rs` (blob `b4626724fd803a3d8bdd021027e7629370b3f6c1`) and `compiler/rustc_metadata/src/native_libs.rs` (blob `b64cb8843ed713f6aa036010aa4a987e045c8eb9`) record `#[link_name]` in `CodegenFnAttrs.symbol_name` and Windows `raw-dylib` ordinals in `link_ordinal`. In `Charon` `0.1.210`, foreign functions translate to `FunDecl` with `Body::Extern(String)` (`charon/src/ast/gast.rs`, blob `23044319a8f763d241912c5d693ed94cf597682f`), but `extern_item_symbol_name` (`charon/src/bin/charon-driver/translate/translate_meta.rs`, blob `187a703dff83687f369f1903c6646aabdff259d3`) computes that string from the final Rust path segment without reading `symbol_name` or `link_ordinal`.
3. **Loss of `c_variadic` in Exported `Charon` `FunSig`:**
   C-variadic declarations (`...`) affect target calling-convention register/stack placement in `rustc`. While `Charon`'s internal hax bridge type `TyFnSig` (`charon/src/bin/charon-driver/hax/types/ty.rs`, blob `470ed2ff4d992efe30f8c4a09a3676111f304003`) carries `c_variadic: bool`, `translate_fun_sig` (`charon/src/bin/charon-driver/translate/translate_types.rs`, blob `35bef6ea79992c65ea934413765fa95f631274e6`) omits `c_variadic` when constructing the exported LLBC `FunSig` (`charon/src/ast/types.rs`, blob `548be29762fdc4f4d1cd652537db6f54065ff6ee`).

---

### 2. Rust Function ABI Lowering (`PassMode` / `FnAbi`) and Cross-Platform Calling-Convention Witnesses

**Basis:** `normative` + `source` + `execution` + `derived` (`rust-lang/rust@b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, `support/rust-function-abi-witnesses-b940084/rust-pilot.rs`, `rust-pilot.ll`, `rust-pilot.s`, `abi_witness.c`, and `results.json`).

#### 2.1 `rustc` `PassMode` Lowering vs. Source Type Layout

In `compiler/rustc_target/src/callconv/mod.rs` and `compiler/rustc_ty_utils/src/abi.rs` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`), `rustc` lowers function signatures into `FnAbi` and per-argument `PassMode` (`Ignore`, `Direct`, `Pair`, `Cast`, `Indirect { attrs, meta_attrs, on_stack }`). Compiling `support/rust-function-abi-witnesses-b940084/rust-pilot.rs` (`rustc --crate-type=lib --emit=llvm-ir,asm,obj -C opt-level=3 -C panic=abort` on `aarch64-apple-darwin`) demonstrates why type size and alignment alone cannot determine the machine call interface:

| Source Type / Signature Shape | Observed LLVM Signature (`rust-pilot.ll`) | Observed `aarch64-apple-darwin` Machine Interface (`rust-pilot.s`) |
| :--- | :--- | :--- |
| `#[repr(C)] struct Pair { a: u64, b: u64 }` (`extern "C"`) | `[2 x i64]` argument and `[2 x i64]` return (`PassMode::Cast`) | Passed and returned in `x0` and `x1`. |
| Rust `(u64, u64)` (`extern "Rust"`) | Two scalar `i64` arguments and `{ i64, i64 }` return (`PassMode::Pair`) | Passed and returned in `x0` and `x1`, but with distinct LLVM IR parameter arity and aggregate structure from `Pair`. |
| `#[repr(C)] struct Triple { a: u64, b: u64, c: u64 }` (`extern "C"`) | Hidden `ptr dead_on_unwind noalias noundef writable sret([24 x i8]) align 8 dereferenceable(24)` output pointer + indirect input pointer (`PassMode::Indirect`) | Caller passes indirect result buffer address in `x8` and input struct address in `x0` (exceeds 16-byte register-return limit). |
| Rust `&[u8]` (`extern "Rust"`) | `ptr noalias noundef nonnull readonly align 1` + `i64 noundef range(i64 0, -9223372036854775807)` (`PassMode::Pair`) | Slice pointer in `x0` and length in `x1`, carrying compiler-deduced validity, aliasing, and length-range attributes (`arg_attrs_for_rust_scalar`). |
| Rust `()` (`extern "Rust"`) | `void` function with zero machine parameters (`PassMode::Ignore`) | Zero registers consumed. |

#### 2.2 Four-Target C Calling-Convention Comparison (`abi_witness.c`)

Compiling `support/rust-function-abi-witnesses-b940084/abi_witness.c` with Apple `clang` 21.0.0 (`clang-2100.3.34.2`) across four target triples (`support/rust-function-abi-witnesses-b940084/x86_64-unknown-linux-gnu.s`, `x86_64-pc-windows-msvc.s`, `aarch64-unknown-linux-gnu.s`, and `arm64-apple-macos14.s`, indexed in `support/rust-function-abi-witnesses-b940084/results.json`) exposes concrete platform divergences across identical C source signatures:

| Function Shape | `x86_64-unknown-linux-gnu` (SysV) | `x86_64-pc-windows-msvc` (Windows x64) | `aarch64-unknown-linux-gnu` (AAPCS64) | `arm64-apple-macos14` (Apple ARM64) |
| :--- | :--- | :--- | :--- | :--- |
| `u64 add(u64, u64)` | `%rdi, %rsi -> %rax` | `%rcx, %rdx -> %rax` (plus 32-byte caller shadow space) | `x0, x1 -> x0` | `x0, x1 -> x0` (`x18` reserved, 128-byte red zone) |
| `Pair swap_pair(Pair)` (16 bytes) | Direct in `%rdi, %rsi -> %rax, %rdx` | Indirect return pointer in `%rcx`, indirect input pointer in `%rdx` (copied via XMM move) | Direct in `x0, x1 -> x0, x1` | Direct in `x0, x1 -> x0, x1` (`Narrow`/variadic stack packing differs from generic AAPCS64) |
| `Triple rotate_triple(Triple)` (24 bytes) | Hidden `sret` pointer in `%rdi`, 24-byte input loaded from stack `8(%rsp)..24(%rsp)` | Indirect return pointer in `%rcx`, indirect input pointer in `%rdx` | Indirect return pointer in `x8`, indirect input pointer in `x0` | Indirect return pointer in `x8`, indirect input pointer in `x0` |

Consequently, a formal assembly entry/return relation `Enter(signature, abi, rust_values, resources, machine_state)` and `Return(...)` must be parameterized by the full target triple, ABI spelling, compiler revision/flags, argument/result `PassMode` placement (including hidden `x8`/`sret` pointers), and platform callee-saved register and stack/red-zone invariants.

---

### 3. Native macOS Arm64 `extern "C-unwind"` Assembly Callback Execution and DWARF FDE Controls

**Basis:** `normative` + `source` + `execution` + `derived` (`support/rust-aarch64-c-unwind-callback-and-metadata-controls-b940084/specimen.rs`, `bounce.s`, `validate.py`, `native-results-and-static-validation.json`, `evidence/metadata-results.json`, and `projection-receipts.json`).

#### 3.1 Whole-Function `global_asm!` Bounce vs. Ordinary `asm!` Unwind Prohibition

Under `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb`, rule `[asm.rules.unwind]` (`src/inline-assembly.md`) unconditionally forbids unwinding out of an ordinary function-scoped `asm!` block—even if the enclosing Rust function is declared `extern "C-unwind"` and the unwind originates from a `C-unwind` callee invoked inside `asm!`. By contrast, defining a standalone function via `global_asm!` (`[asm.scope.global_asm]`) or `#[unsafe(naked)]` (`[asm.naked-rules.unwind]`) and declaring its prototype as `unsafe extern "C-unwind" fn` (`[items.fn.extern.unwind]` in `src/items/functions.md`) permits unwinding across the assembly frame under `-C panic=unwind`, provided the assembly maintains a valid platform frame and unwind metadata.

In `support/rust-aarch64-c-unwind-callback-and-metadata-controls-b940084/specimen.rs` and `support/rust-aarch64-c-unwind-callback-and-metadata-controls-b940084/bounce.s`, the 8-instruction, 32-byte AArch64 bounce function (`stp x29, x30, [sp, #-16]!; mov x29, sp; mov x16, x0; mov x0, x1; blr x16; add x0, x0, #1; ldp x29, x30, [sp], #16; ret`, machine bytes `fd7bbfa9 fd030091 f00300aa e00301aa 00023fd6 00040091 fd7bc1a8 c0035fd6`, SHA-256 `ea698a8dbd4154d20a251e113a12debdbc2ac44fb57a323d87458d8ba1074cf4`) accepts an `extern "C-unwind" fn(u64) -> u64` callback pointer in `x0` and argument `0x1122334455667788` in `x1`.

#### 3.2 Bound Object/Executable Unwind Metadata (`__unwind_info` and `__eh_frame`)

As verified in `support/rust-aarch64-c-unwind-callback-and-metadata-controls-b940084/evidence/metadata-results.json` and `support/rust-aarch64-c-unwind-callback-and-metadata-controls-b940084/evidence/captures/image-eh-frame.stdout`:

| Artifact Property | Observed Value in Linked Mach-O Image |
| :--- | :--- |
| Object (`.o`) SHA-256 & function range | `360faff08c03863e69915ae1d5b6119b3986ae7c5be0ffd5052037e70dcd3128`, VM `[0, 32)` / file `[1288, 1320)` |
| Raw executed image SHA-256 & function range | `39fe9089fd8449dbe783bc1549daa67fc60d221982be1ecdf345c1b4a721cedf`, VM `[0x1000008c0, 0x1000008e0)` / file `[2240, 2272)` |
| Callback return PC (`after blr x16`) | Static VM `0x1000008d4` (`start + 20`); live loaded VM `0x1040348d4` (base `0x104034000 + 0x8d4`) |
| Active `__unwind_info` entry | Function offset range `[0x8c0, 0x8e0)`, regular second-level page (`kind = 2`), encoding `0x03000014` (`UNWIND_ARM64_MODE_DWARF` with FDE offset `0x14`) |
| Selected DWARF FDE in `__eh_frame` | `__eh_frame` offset `0x14` (file offset `260188`, length 52 bytes); CIE DWARF32 v1, `zR`, code align `1`, data align `-8`, RA column `30` |
| Decoded CFA / FP / LR table rows | Offset `0`: `CFA = SP`, `FP/LR = same`; Offset `4`: `CFA = SP + 16`, `FP = [CFA - 16]`, `LR = [CFA - 8]`; Offset `8`: `CFA = X29 + 16`, `FP = [CFA - 16]`, `LR = [CFA - 8]`; Offset `28`: `CFA = SP`, `FP/LR = same` |

#### 3.3 Native Execution Receipts and Non-Executable Metadata Negative Controls

In the native macOS Arm64 execution (`support/rust-aarch64-c-unwind-callback-and-metadata-controls-b940084/evidence/captures/native-positive.stdout` and `native-results-and-static-validation.json`), all four cases passed in `0.097s` with exit code `0`:

| Executed Case | Bounce Outcome | Callback Calls / Callback Drops / Outer Drops | Drop Order (`12` = callback before outer) | Live `_Unwind_Backtrace` Status & Depth |
| :--- | :--- | :--- | :--- | :--- |
| Rust bounce + normal callback | Returned `0x336699cd00336699` | `1 / 1 / 1` | `12` (`0` panic hooks) | Status `5` (`_URC_END_OF_STACK`), 9 PCs |
| Rust bounce + panic callback | Caught `ExpectedPanic` (`0x4534305f554e5744`) | `1 / 1 / 1` | `12` (`1` expected panic hook) | Status `5` (`_URC_END_OF_STACK`), 9 PCs |
| Assembly bounce + normal callback | Returned `0x336699cd00336699` | `1 / 1 / 1` | `12` (`0` panic hooks) | Status `5`, 9 PCs (includes `0x1040348d4` = `start + 20`) |
| Assembly bounce + panic callback | Caught `ExpectedPanic` (`0x4534305f554e5744`) | `1 / 1 / 1` | `12` (`1` expected panic hook) | Status `5`, 9 PCs (includes `0x1040348d4` = `start + 20`) |

Three non-executable binary metadata controls in `support/rust-aarch64-c-unwind-callback-and-metadata-controls-b940084/data-controls/` preserve the exact 32-byte `.text` instructions (so normal `ldp x29, x30, [sp], #16; ret` recovery still computes `SP = 0x1000, FP = 0x3000, PC = 0x8004`), while mutating only `__eh_frame`:
1. **`wrong-cfa-offset.macho-data.bin` (file offset `260222`, CFA offset `16 -> 8`):** Mid-body unwind recovers `SP = S - 8` instead of `S` and reads saved `FP` (`0x3000`) into `LR`.
2. **`wrong-lr-offset.macho-data.bin` (file offset `260226`, factored offset `1 -> 2`, i.e. `-8 -> -16`):** Mid-body unwind recovers `LR = F` (`0x3000`) instead of return address `R` (`0x8004`).
3. **`missing-active-fde.macho-data.bin` (file offset `260188`, FDE length `52 -> 0`):** Active `__unwind_info` DWARF offset `0x14` resolves to a zero-length terminator, causing the metadata verifier (`support/rust-aarch64-c-unwind-callback-and-metadata-controls-b940084/validate.py`) to reject the image.

---

### 4. Windows x64 `.pdata`/`.xdata` Unwind Contracts and Rust Cleanup Tables

**Basis:** `documentation` (`MicrosoftDocs/cpp-docs@281a0a0eae55fe97f5decd244db18ed5096d4687`) + `source` + `execution` + `derived` (`support/rust-assembly-platform-unwind-contracts-2026/specimen.c`, `specimen.s`, `specimen.obj`, `cleanup.rs`, `cleanup.s`, `check_unwind.py`, and `unwind-results.json`).

1. **Windows x64 Prologue/Epilogue Rules and `.pdata`/`.xdata` Decoding:**
   Under Microsoft's x64 exception-handling specification (`docs/build/exception-handling-x64.md` and `docs/build/prolog-and-epilog.md`), `.pdata` holds image-relative `RUNTIME_FUNCTION` triples `(BeginAddress, EndAddress, UnwindInfoAddress)` and `.xdata` holds `UNWIND_INFO` headers and `UNWIND_CODE` arrays ordered in reverse prologue offset order. Compiling `support/rust-assembly-platform-unwind-contracts-2026/specimen.c` with `clang --target=x86_64-pc-windows-msvc -O1 -fno-omit-frame-pointer -funwind-tables` produces a 77-byte `.text` body (SHA-256 `f8cb6d59576072def3548aaf1b5159a9e09561bfda362028efb4d43ffd169d39`) with prologue `push rbp` (offset 1), `sub rsp, 80` (offset 5), `lea rbp, [rsp + 80]` (offset 10) and `.xdata` bytes `010a03550a03059201500000`:
   - `Version = 1`, `Flags = 0`, `SizeOfProlog = 10`, `CountOfCodes = 3`, `FrameRegister = RBP (5)`, `FrameOffset = 80` (`5 * 16`);
   - Unwind codes: offset `10` `UWOP_SET_FPREG`, offset `5` `UWOP_ALLOC_SMALL` (`8 * 9 + 8 = 80` bytes), offset `1` `UWOP_PUSH_NONVOL RBP`.
   - Across five interrupted PC offsets (`0`, `1`, `5`, `10`, and `43` immediately after the `call`), `support/rust-assembly-platform-unwind-contracts-2026/check_unwind.py` recovers the exact caller state (`RIP`, `RBP`, and `RSP = entry_rsp + 8`).
2. **Three COFF Metadata-Only Object Mutations (`support/rust-assembly-platform-unwind-contracts-2026/`):**
   - `mutant-frame-offset-64.obj` (`FrameOffset` changed from `80` to `64`): `.text` and normal epilogue (`add rsp, 80; pop rbp; ret`) are unchanged, but body unwind reads caller state from shifted stack offsets.
   - `mutant-alloc-72.obj` (`UWOP_ALLOC_SMALL` changed from `80` to `72` bytes): `.text` is unchanged, but body unwind pops saved `RBP` as the caller return `RIP` and miscomputes `RSP`.
   - `mutant-missing-pdata.obj` (`.pdata` section renamed to `.gone`): `.text` is unchanged, but missing-table leaf fallback reads a local stack slot at `[RSP]` as the return `RIP`.
3. **Safe Rust `extern "C-unwind"` Landing Pad and LSDA Emission (`cleanup.rs` / `cleanup.s`):**
   Compiling `support/rust-assembly-platform-unwind-contracts-2026/cleanup.rs` (a safe Rust function owning a `Drop` guard around an `extern "C-unwind"` callback call) with `rustc 1.99.0` on `aarch64-apple-darwin` (`-C opt-level=1 -C panic=unwind`) emits `.cfi_personality 155, ___rust_eh_personality`, `.cfi_lsda 16, Lexception0`, a normal drop-and-return path, an exceptional landing pad that runs the `Drop` guard before calling `__Unwind_Resume`, and a `__gcc_except_tab` call-site table (`support/rust-assembly-platform-unwind-contracts-2026/cleanup.s`). This confirms that frame-pointer/SP recovery in `.eh_frame` or `.xdata` is necessary to reach the caller frame, while executing Rust `Drop` destructors and restoring caller borrow invariants additionally depends on personality routine and LSDA call-site semantics.

---

### 5. Linking Machine Proofs to Rust Resources and Behavioral Equivalence (`ContextBridge.lean`)

**Basis:** `source` + `execution` + `derived` (`minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `AeneasVerif/kraken@8af78062037bc237b341d20252aafd1797c1bcb7`, DimSum DOI `10.1145/3571220`, and `support/rust-machine-resource-linking-and-equivalence/ContextBridge.lean`).

#### 5.1 Six Components of the Rust-to-Machine State Relation `R`

Because MiniRust represents memory as `List<AbstractByte>` (`Init(u8, Option<Provenance>) | Uninit`) with Tree Borrows alias tags and `CallId` protectors while Kraken (`Kraken/Mem.lean`) models memory as a partial map from numeric 64-bit addresses to raw bytes, a cross-language linking relation `R(rust_state, machine_state)` cannot be a function that erases provenance, initialization, and borrow tags and later reconstructs them from integer addresses:

| State Relation Component | Information Lost by Raw Machine Bytes | Required Bridge Invariant in `R` |
| :--- | :--- | :--- |
| **Allocation & Liveness** | Numeric address reuse across freed and newly allocated stack/heap blocks | Bijective or injective live allocation-region map preserved across the call. |
| **Provenance & Authority** | Integer address equality does not confer read/write capability | Explicit pointer-derivation provenance map or exposed-provenance policy. |
| **Aliasing & Borrow Tags** | Identical byte contents under incompatible `&mut` / `&` / protector states | Preservation of caller-retained borrow tags and active call protectors. |
| **Initialization & Bit Validity** | Concrete hardware bytes cannot distinguish `Uninit` padding from initialized bytes or invalid `bool`/niche patterns | Per-byte initialization cover and typed bit-validity at every exposed Rust place. |
| **Layout & ABI Metadata** | Raw register words do not distinguish `(u64, u64)`, `Pair`, `&[u8]`, or hidden `sret` | Bound `FnAbi` / `PassMode` placement and wide-pointer metadata witnesses. |
| **Continuation & Unwind Frame** | Return value bits omit callee-saved registers, SP alignment, callback reentrancy, and unwind landing pads | Frame preservation and admissible normal/unwind exit relation. |

#### 5.2 Four Factored Semantic Obligations and Mechanized Counterexamples (`ContextBridge.lean`)

In `support/rust-machine-resource-linking-and-equivalence/ContextBridge.lean` (verified under Lean `v4.34.1` with zero axioms across all seven theorem closures, `support/rust-machine-resource-linking-and-equivalence/context-proof.stdout`), cross-language linking is factored into four obligations—**Entry Adequacy**, **Machine Prefix Safety & Resource Preservation**, **Behavioral Correspondence**, and **Context Closure**—supported by the following machine-checked theorems:

- **`context_replacement`:** Given an execution-reflection relation from machine transitions to source transitions and observation agreement on related states, any machine execution step reflects to a source transition producing the identical external observation.
- **`exact_spec_equivalence` vs. `loose_spec_is_not_equivalence`:** Two deterministic implementations that both satisfy an exact functional specification are pointwise equal (`exact_spec_equivalence`), whereas two implementations that both satisfy a permissive relational predicate (`loose_spec_is_not_equivalence`) can produce distinct observable outputs on the same input.
- **`value_equivalence_is_not_context_safety`:** Exhibits two post-states with identical scalar return value (`7 = 7`) where one preserves the caller's live-borrow resource flag (`borrowLive = true`) and the other invalidates it (`borrowLive = false`), causing the surrounding Rust continuation to fail despite return-value equality.
- **Overflow and Observation Discriminators:** Proves that an 8-bit wrapping assembly addition (`(a + b) mod 256`) and a checked Rust addition (`None` / panic at `256`) agree on in-range inputs but diverge at overflow, demonstrating that behavioral correspondence requires matching failure/overflow contracts (`wrapping_add` vs. checked `+`).

## Boundaries

- **Not Examined:**
  - Native Windows x64 execution or PE loader table registration (the Windows `.pdata`/`.xdata` specimens were cross-compiled with `clang --target=x86_64-pc-windows-msvc` and analyzed via `check_unwind.py`), Windows AArch64 unwind metadata, or `arm64e` pointer-authenticated stack frames.
  - Foreign C++ exception interop (`extern "C-unwind"` catching foreign non-Rust exceptions), POSIX signals, asynchronous interrupts, `longjmp`, or forced unwinding (`_UA_FORCE_UNWIND`).
  - Execution of malformed unwind tables or corrupted stack frames in a live OS process (all negative unwind controls in both Mach-O `.eh_frame` and COFF `.pdata`/`.xdata` were evaluated strictly as non-executable data files).
- **Unknown:**
  - Complete end-to-end mechanized instantiation of `ContextBridge.lean` over the full MiniRust operational semantics and Kraken AArch64 semantics (including multi-instruction partial-prologue/epilogue unwind recovery and `__rust_eh_personality` LSDA interpretation).
- **Known Not to Apply:**
  - Unwinding out of an ordinary function-scoped `asm!` block is **never** valid Rust (`[asm.rules.unwind]`), even inside an `extern "C-unwind"` function.
  - Equal size and alignment of two Rust types do **not** imply identical `FnAbi` / LLVM calling-convention lowering (`Pair` vs. `(u64, u64)`), and SysV x86-64 register conventions do **not** apply to Windows x86-64 MSVC.
  - Passing normal-return (`ret`) tests does **not** validate `.eh_frame`, `__unwind_info`, `.pdata`, or `.xdata` unwind records.
  - `Charon` `0.1.210` `Body::Extern(String)` does **not** reflect `#[link_name]` or `#[link_ordinal]`, and exported `Charon` `FunSig` does **not** distinguish C-variadic declarations from fixed-arity declarations.
- **Unsupported:**
  - Unstable `extern type` declarations are not part of the stable Rust Reference contract examined here.

## Evidence

| Artifact / Source Path | SHA-256 / Commit Identity | Evidence Role |
| :--- | :--- | :--- |
| `support/rust-aarch64-c-unwind-callback-and-metadata-controls-b940084/specimen.rs`, `bounce.s`, `artifacts/specimen.o`, `artifacts/specimen.s` | `specimen.rs`: `d76355f5da03e61bd6a7e13f001c7ab79810c4978fd3865797ed6197fed1c5e1`; `bounce.s`: `5c9ee259c976d4fd7a044a95ef380ad899ac0183370d1b9d8a3872270a9dd1dd`; `specimen.o`: `360faff08c03863e69915ae1d5b6119b3986ae7c5be0ffd5052037e70dcd3128` | **source** & **execution**: Native macOS Arm64 `extern "C-unwind"` assembly callback specimen and compiled artifacts. |
| `support/rust-aarch64-c-unwind-callback-and-metadata-controls-b940084/native-results-and-static-validation.json`, `evidence/metadata-results.json`, `projection-receipts.json`, `validate.py` | Raw executed Mach-O image: `39fe9089fd8449dbe783bc1549daa67fc60d221982be1ecdf345c1b4a721cedf`; projected public data copy: `b3132adac0a809fba51315822a82df64383bc43d1d0483621eee80c145404387` | **execution** & **derived**: Native 4-case unwind/normal execution receipts, `_Unwind_Backtrace` PC walk, and 3 DWARF FDE negative data controls. |
| `support/rust-assembly-platform-unwind-contracts-2026/specimen.c`, `specimen.s`, `specimen.obj`, `cleanup.rs`, `cleanup.s`, `check_unwind.py`, `unwind-results.json` | `.text` (77B): `f8cb6d59576072def3548aaf1b5159a9e09561bfda362028efb4d43ffd169d39`; `MicrosoftDocs/cpp-docs@281a0a0eae55fe97f5decd244db18ed5096d4687` | **documentation**, **source**, & **execution**: Windows x64 `.pdata`/`.xdata` decoder, 5 positive recovery contexts, 3 COFF metadata mutants, and Apple AArch64 Rust LSDA cleanup assembly. |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` & `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` | `foreign_modules.rs` (`8a6b2027...`), `codegen_attrs.rs` (`b4626724...`), `gast.rs` (`23044319...`), `translate_types.rs` (`35bef6ea...`), `translate_meta.rs` (`187a703d...`) | **normative** & **source**: `extern` block representation in `rustc` HIR/codegen vs. `Body::Extern` and `c_variadic` loss in `Charon` `0.1.210`. |
| `support/rust-function-abi-witnesses-b940084/rust-pilot.rs`, `rust-pilot.ll`, `rust-pilot.s`, `abi_witness.c`, `results.json` | `rust-lang/rust@b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` (`callconv/mod.rs`, `abi.rs`); `ARM-software/abi-aa@ec3e2fb69065768aa1caf298813a7808b50bc264` | **normative**, **source**, & **execution**: `PassMode` / `FnAbi` LLVM IR witnesses and 4-target C calling-convention assembly outputs. |
| `support/rust-machine-resource-linking-and-equivalence/ContextBridge.lean`, `execution.json`, `context-proof.stdout` | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `AeneasVerif/kraken@8af78062037bc237b341d20252aafd1797c1bcb7` | **source**, **execution**, & **derived**: Zero-axiom Lean `v4.34.1` proofs of `context_replacement`, `exact_spec_equivalence`, `loose_spec_is_not_equivalence`, and `value_equivalence_is_not_context_safety`. |

## Revalidation

Run the following deterministic checks from the package directory (`reports/rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking/`):

1. **Validate the AArch64 Mach-O `extern "C-unwind"` Code, Active DWARF FDE, Five Recovery Snapshots, and Three Metadata Controls:**
   ```bash
   python3 - <<'PY'
   import os, subprocess, sys
   pkg_sub = "support/rust-aarch64-c-unwind-callback-and-metadata-controls-b940084"
   r = subprocess.run([sys.executable, "validate.py"], cwd=pkg_sub, capture_output=True, text=True)
   assert r.returncode == 0, r.stderr
   print(r.stdout.strip())
   PY
   ```
2. **Validate the Windows x64 COFF `.pdata`/`.xdata` Records, Five Prologue/Body Recovery Points, and Three Object Mutants:**
   ```bash
   python3 - <<'PY'
   import subprocess, sys
   pkg_sub = "support/rust-assembly-platform-unwind-contracts-2026"
   r = subprocess.run([sys.executable, "check_unwind.py"], cwd=pkg_sub, capture_output=True, text=True)
   assert r.returncode == 0, r.stderr
   print(r.stdout.strip())
   PY
   ```
3. **Kernel-Check the Machine-Resource Linking Theorems in `ContextBridge.lean` under Lean `v4.34.1`:**
   ```bash
   anneal-lean-run --mode file --concurrency 1 -- \
     elan run leanprover/lean4:v4.34.1 lean -j1 -M768 \
     support/rust-machine-resource-linking-and-equivalence/ContextBridge.lean
   ```
4. **Revalidate ABI Lowering and `Charon` Foreign-Item Extraction on Toolchain Updates:**
   - Recompile `support/rust-function-abi-witnesses-b940084/rust-pilot.rs` with `rustc --crate-type=lib --emit=llvm-ir,asm,obj -C opt-level=3 -C panic=abort` and `support/rust-function-abi-witnesses-b940084/abi_witness.c` across the four target triples (`x86_64-unknown-linux-gnu`, `x86_64-pc-windows-msvc`, `aarch64-unknown-linux-gnu`, `arm64-apple-macos14`), checking `support/rust-function-abi-witnesses-b940084/results.json`.
   - Diff `charon/src/bin/charon-driver/translate/translate_types.rs` (`translate_fun_sig`) and `translate_meta.rs` (`extern_item_symbol_name`) to check whether `c_variadic` or `#[link_name]` / `#[link_ordinal]` metadata have been added to `Charon` `FunSig` and `Body::Extern`.
