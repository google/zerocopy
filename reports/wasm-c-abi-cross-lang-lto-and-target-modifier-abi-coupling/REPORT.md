# WebAssembly Basic C ABI Alignment, `i686` Cross-Language LTO IR Mismatches, `-Zregparm=3`, and Target-Modifier ABI Coupling

## Summary

Function-call ABIs in `rustc` are coupled not only to target triples and C psABIs, but also to WebAssembly aggregate unwinding fixes, LLVM IR signature representations under cross-language LTO, ABI-altering codegen flags (`-Zregparm=3`, `-Ctarget-feature`), and security target modifiers (`RFC 3716`, `RFC 3980`). Primary inspection of `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and `WebAssembly/tool-conventions@eab11670ee6bbf5d1e9c26feee87493f76e4edbf`, paired with cross-target `rustc` and `clang-19` (`19.1.7`) probes, establishes four main results:

1. **WebAssembly Basic C ABI spec convergence (`PR #162806`, `PR #162826`, legacy removal):**
   - On `wasm32-unknown-unknown` in `rustc 1.102.0-nightly` (`3ef0c22cd`), `-Zwasm-c-abi=legacy` is removed (`rustc_session::options::parse_wasm_c_abi` accepts only `"spec"`, and lint `wasm_c_abi` is registered as removed).
   - `PR #162806` (`af5ab5897b69940263043c8b98f3bed4cc476fec`) replaces `layout.homogeneous_aggregate` in `compiler/rustc_target/src/callconv/wasm.rs` with recursive `singleton_scalar`, passing `union { u32, u32 }` and `union { u32, *const u8 }` indirectly (`sret` + pointer) rather than misclassifying them as `i32` scalars, while still unwrapping single-field `Empty`-augmented unions (`union { Empty, u32 }`) and structs (`struct { Empty, u32 }`) to `i32`—matching `clang-19 --target=wasm32-unknown-unknown` across all six tested C struct/union signatures.
   - `PR #162826` (`f6b5137514497e12c9f275d3fe3f9d4ee9933b0d`) extends `wasm.rs` via `is_aggregate_for_abi` to treat integer-representation enums containing zero-sized fields (e.g., `#[repr(u8)] enum EnumZstField { A(()), B }`) as indirect aggregates (`sret([1 x i8])`), matching Clang C-struct enum lowering while preserving direct integer passing for fieldless `#[repr(u8)] enum { A, B }` and niched pointers (`Option<&i32>`).
2. **`i686` cross-language LTO IR incompatibility (`rustc` `byval` vs. `clang-19` unpacked scalars):**
   - For `#[repr(C)] struct TwoI32(i32, i32)` and `ThreeI32(i32, i32, i32)` on `i686-unknown-linux-gnu`, `rustc 1.102.0-nightly` emits `ptr readonly byval([8 x i8]) align 4` and `ptr readonly byval([12 x i8]) align 4`, whereas `clang-19` unpacks both into scalar IR parameters `(i32 returned %0, i32 %1)` and `(i32 returned %0, i32 %1, i32 %2)`. Both compile to identical stack offsets (`4(%esp)`) in standalone `.o` files, yet disagree at the LLVM IR call/definition boundary under `-Clinker-plugin-lto`.
3. **`-Zregparm=3` 64-bit register omission and target-feature ABI gates:**
   - Under `-Zregparm=3` on `i686-unknown-linux-gnu`, `rustc`'s `fill_inregs` only marks arguments with `size.bits() <= 32` as `inreg` (`x86.rs`). On `take_u64_u32(a: u64, b: u32) -> u32`, `clang-19 -mregparm=3` emits `i64 inreg %0, i32 inreg %1` (passing `a` in `eax:edx` and `b` in `%ecx`: `movl %ecx, %eax`), whereas `rustc -Zregparm=3` emits `i64 %a, i32 inreg %b` (leaving `a` on the stack and putting `b` in `%eax`: `retl`).
   - Meanwhile, on `i686-unknown-linux-gnu` `rustc` enforces `-Ctarget-feature=+sse2` as a hard compilation error (`target feature sse2 must be enabled to ensure that the ABI of the current target can be implemented correctly`), passing `extern "Rust" fn(f64) -> f64` via SSE `<8 x i8>` in `xmm0` against `extern "C"`'s x87 `st(0)` return, while `x86_64-unknown-none` rejects `#[target_feature(enable = "avx")]` with `sse` disabled.
4. **Target modifiers and ABI profile switches (`RFC 3716`, `RFC 3980`):**
   - ABI-affecting codegen flags (such as target features converted via `88120e6e4768ff17776e1bc9448c60c2b1125f74`, `-Zbranch-protection=pac-ret`, `-Zfixed-x18`, and Arm CMSE calling conventions) interact with crate-wide ABI compatibility and call-site lowering; `RFC 3716` (merged) establishes explicit target modifiers checked across crates, while `RFC 3980` (merged) introduces `extern "custom"` for custom-calling-convention naked/assembly boundaries.

## Applicability

- **Examined subjects (`REPORT.json`):** `rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, including merged commits `PR #162806`, `PR #162826`, and `88120e6e4768ff17776e1bc9448c60c2b1125f74`), `WebAssembly/tool-conventions` (`BasicCABI.md` @ `eab11670ee6bbf5d1e9c26feee87493f76e4edbf`), merged RFCs `rust-lang/rfcs` `b0e56dbdca4e1a2d90889cefa6fdfa0179e2dbb2` (RFC #3716) and `8912d815c39b40c361bc53498e51fea1125b9137` (RFC #3980), and `clang-19` (`19.1.7`).
- **Execution scope:** Live `--emit=llvm-ir` and `--emit=asm` probes ran on `rustc 1.102.0-nightly (3ef0c22cd)` and `clang-19` targeting `wasm32-unknown-unknown`, `i686-unknown-linux-gnu`, `x86_64-unknown-linux-gnu`, `x86_64-unknown-none`, and `aarch64-unknown-linux-gnu`. Installed `1.96.0` and `1.100.0` toolchains lack `wasm32-unknown-unknown` `core`, so pre-`#162806` Wasm regression is documented via source history (`PR #162806` / `#162826` diffs) rather than locally executed on `1.96.0`.
- **Relation to existing corpus packages:** Complements without duplicating [`rustc-kcfi-cfi-typeid-xxhash64-reify-shims-and-cross-lang-ud2-soundness`](../rustc-kcfi-cfi-typeid-xxhash64-reify-shims-and-cross-lang-ud2-soundness/REPORT.md), [`rustc-sanitizers-lto-cfi-kcfi-arity-ub-checks-and-ignorelist-soundness`](../rustc-sanitizers-lto-cfi-kcfi-arity-ub-checks-and-ignorelist-soundness/REPORT.md) (full CFI/KCFI type-id hashing, jump tables, and LTO checks), and [`rustc-target-feature-1-1-cross-feature-inlining-boundary-and-simd-abi`](../rustc-target-feature-1-1-cross-feature-inlining-boundary-and-simd-abi/REPORT.md) (x86-64 `#[target_feature]` MIR/LLVM inlining rules).

## Findings

### 1. WebAssembly Basic C ABI (`BasicCABI.md` Alignment, `#162806`, `#162826`, and `externref`)

**Basis:** `normative` (`BasicCABI.md`) + `source` (`wasm.rs`, `options.rs`) + `execution` (`support/probe_wasm_i686_modifiers_abi.py`)

Under `WebAssembly/tool-conventions/BasicCABI.md` (`eab11670ee`):
- Scalars lower directly (`i32`, `i64`, `f32`, `f64`), with integers `< 32` bits promoted to `i32`, `i128`/`f128` returned via hidden pointer (`sret`) and passed as split args or indirect pointers.
- Aggregates (structs and unions of more than one non-empty field, or any non-scalar size) are passed and returned indirectly via linear-memory pointers; only "trivial" single-scalar wrappers (ignoring empty fields) unwrap to their scalar type.

In `rustc`:
1. **Removal of legacy Wasm ABI mode:** `compiler/rustc_session/src/options.rs:2191-2193` defines `parse_wasm_c_abi` as `v == Some("spec")` (invoking `rustc +nightly -Z wasm-c-abi=legacy` fails with `error: incorrect value 'legacy' for unstable option 'wasm-c-abi' - 'spec' was expected`), and `compiler/rustc_lint/src/lib.rs:701` registers `"wasm_c_abi"` as a removed lint (`"the wasm C ABI has been fixed"`).
2. **Union singleton fix (`PR #162806`, `af5ab5897b`) and ZST-enum fix (`PR #162826`, `f6b5137514`):** Prior to `2026-09-15`, `wasm.rs` called `layout.homogeneous_aggregate`, which collapsed `#[repr(C)] union SingleUnionMixed { a: u32, b: *const u8 }` and `union { u32, u32 }` to `i32` (since pointers and `u32` both map to 4-byte `RegKind::Integer` on wasm32) instead of passing them indirectly. Now `singleton_scalar` (`wasm.rs`) returns `None` whenever `layout.fields.count()` contains `>= 2` non-ZST fields, and `is_aggregate_for_abi` checks `variants.iter().all(|x| x.field_offsets.is_empty())` for direct-tagged enums. Live comparison of `rustc +nightly --target=wasm32-unknown-unknown` vs. `clang-19 --target=wasm32-unknown-unknown`:

| Signature Type | `rustc +nightly` (`3ef0c22cd`) LLVM IR | `clang-19` LLVM IR |
| :--- | :--- | :--- |
| `SingleU32(u32)` | `i32 (i32 returned %0)` | `i32 (i32 returned %0)` |
| `WithEmpty { e: Empty, a: u32 }` | `i32 (i32 returned %0)` | `i32 (i32 returned %0)` |
| `SingleUnion { a: u32, b: u32 }` | `void (ptr sret([4 x i8]), ptr %x)` | `void (ptr sret(%union.SingleUnion), ptr byval(...) %1)` |
| `SingleUnionMixed { a: u32, b: *const u8 }` | `void (ptr sret([4 x i8]), ptr %x)` | `void (ptr sret(%union.SingleUnionMixed), ptr byval(...) %1)` |
| `SingleUnionWithEmpty { e: Empty, a: u32 }` | `i32 (i32 returned %0)` | `i32 (i32 returned %0)` |
| `Pair(u32, u32)` | `void (ptr sret([8 x i8]), ptr %x)` | `void (ptr sret(%struct.Pair), ptr byval(...) %1)` |
| `#[repr(u8)] enum EnumZstField { A(()), B }` | `void (ptr sret([1 x i8]), ptr %x)` | *(Rust ZST-field enum treated as aggregate per `PR #162826`)* |

*(Note on `externref` / table-backed Wasm types: `RFC #3987`—unmerged at observation—proposes a `wasm_externref` lang item because WebAssembly reference types cannot reside in linear memory and bypass pointer-based indirect `sret`/memory layout assumptions.)*

### 2. `i686` Cross-Language LTO IR Divergence (`byval` vs. Unpacked Scalars)

**Basis:** `source` + `execution` (`support/probe_wasm_i686_modifiers_abi.py`)

Under System V i386 (`i686-unknown-linux-gnu`), `extern "C"` aggregate parameters pass on the stack in `4`-byte slots. While assembly callers and callees agree on stack slot offsets (`movl 4(%esp), %eax`), `rustc` and `clang-19` emit incompatible LLVM IR function signatures:

- **`TwoI32(i32, i32)` (`take_two`):** `rustc 1.102.0-nightly` emits `define noundef i32 @take_two(ptr noalias nofree noundef readonly byval([8 x i8]) align 4 captures(none) dereferenceable(8) %x)`, whereas `clang-19` emits `define dso_local i32 @take_two(i32 returned %0, i32 %1)`.
- **`ThreeI32(i32, i32, i32)` (`take_three`):** `rustc` emits `ptr ... byval([12 x i8]) align 4 %x`, whereas `clang-19` emits `(i32 returned %0, i32 %1, i32 %2)`.

Because LLVM's inliner and IR type verifier during cross-language LTO (`-Clinker-plugin-lto`) see a `ptr byval` parameter on one side and unpacked scalar `i32` parameters on the other, direct LTO linking/inlining across Rust and Clang C on `i686` triggers IR type mismatches (`rust-lang/rust#143818` / `llvm/llvm-project#102174`) even when non-LTO object linking runs cleanly.

### 3. `-Zregparm=3` 64-Bit Miscompilation, SSE2 Enforcement, and Target Modifiers

**Basis:** `source` (`x86.rs`, `options.rs`, `RFC 3716`, `RFC 3980`) + `execution`

1. **`-Zregparm=3` 64-bit integer omission (`compiler/rustc_target/src/callconv/x86.rs`):** In `fill_inregs` (for `General { reg_count: 3 }`), `rustc` guards register assignment with `size.bits() <= 32`, skipping `64`-bit integers (`u64`/`i64`). Probing `take_u64_u32(a: u64, b: u32) -> u32 { b }` and `take_u32_u64(a: u32, b: u64) -> u32 { a }`:
   - `clang-19 --target=i686-unknown-linux-gnu -mregparm=3` emits `define i32 @take_u64_u32(i64 inreg noundef %0, i32 inreg noundef returned %1)` (`%0` consumes `eax:edx`, leaving `b` in **`%ecx`**, so assembly emits `movl %ecx, %eax; retl`) and `TwoI32` as `(i32 inreg %0, i32 inreg %1)`.
   - `rustc +nightly --target=i686-unknown-linux-gnu -Zregparm=3` emits `define i32 @take_u64_u32(i64 noundef %a, i32 inreg noundef returned %b)` (`%a` stays on the stack without `inreg`, pushing `b` into **`%eax`**, so assembly emits bare `retl`) and keeps `TwoI32` on stack `byval([8 x i8])` (`movl 4(%esp), %eax`). Calling between Clang `-mregparm=3` and Rust `-Zregparm=3` with `u64` or structs immediately reads the wrong register/stack slot.
2. **Hard `sse2` ABI gate on `i686` and `extern "Rust"` vs. `extern "C"` float return:** Compiling `--target=i686-unknown-linux-gnu -Ctarget-feature=-sse,-sse2` aborts in `rustc` (`error: target feature sse2 must be enabled to ensure that the ABI of the current target can be implemented correctly`). With `sse2` enabled, `extern "Rust" fn f64_rust(x: f64) -> f64` lowers to `define noundef <8 x i8> @f64_rust(double noundef %x)` (returning via `xmm0` to avoid x87 signaling-NaN quieting) whereas `extern "C" fn fp_c(x: f64) -> f64` emits `define noundef double @fp_c(double noundef returned %x)` (returning in `st(0)`).
3. **Target modifiers (`RFC 3716`, `88120e6e47`), `extern "custom"` (`RFC 3980`), and security ABI coupling:**
   - Codegen options that change function calling conventions or prologue/ABI invariants—such as ABI-controlling target features (`88120e6e47`), `-Zfixed-x18`, `-Zbranch-protection=pac-ret` (`"sign-return-address"="non-leaf"` + AArch64 ELF pointer-authentication metadata), and Armv8-M CMSE attributes—cannot safely differ silently across compiled crates; `RFC 3716` formalizes "target modifiers" tracked in crate metadata to detect cross-crate ABI conflicts, while `RFC 3980` adds `extern "custom"` for custom-ABI naked/inline assembly entrypoints.
   - As observed directly in `-Zsanitizer=kcfi` (`!kcfi_type !{i32 -1543064580}` vs. `!{i32 -1900376514}`) and `-Zsanitizer=cfi -Clinker-plugin-lto` (`!_ZTSFu3u32S_E` vs. `!_ZTSF5WrapCS_E`), indirect-call CFI metadata enforces an extra signature contract separating `#[repr(C)] struct WrapC(u32)` from both `u32` and `#[repr(transparent)] struct WrapT(u32)` even where target psABI IR signatures coincide (`i32 (i32)`). *(For full KCFI/CFI type-id hashing and LTO jump-table rules, see [`rustc-kcfi-cfi-typeid-xxhash64-reify-shims-and-cross-lang-ud2-soundness`](../rustc-kcfi-cfi-typeid-xxhash64-reify-shims-and-cross-lang-ud2-soundness/REPORT.md).)*

## Boundaries

- **Pre-`PR #162806` Wasm toolchain execution (`unsupported` locally):** `1.96.0` lacks `wasm32-unknown-unknown` `core` locally and forbids `#![no_core]`, so `1.96.0` pre-fix Wasm IR was not executed here; pre-fix behavior is cited from `PR #162806` (`af5ab5897b`) and `PR #162826` (`f6b5137514`) diffs.
- **Unmerged ABI proposals (`unknown` stabilization):** `-Zdefault-c-abi` (`rust-lang/rust#131749`), `RFC #3884` (CMSE), `RFC #3987` (`externref`), and ELF `pauthtest` schema tooling (`rust-lang/rust#148640`/`#159081`) remain unstable/unmerged or target-specific work in progress.
- **Standalone object linking vs. cross-language LTO (`known not to apply` to native-asm `.o` linking):** The `i686` `TwoI32` `byval` vs. `(i32, i32)` divergence triggers UB/errors under LLVM IR LTO (`-Clinker-plugin-lto`), whereas non-LTO native object linking agrees at `[esp+4]`.

## Evidence

- **Primary compiler sources and specifications:**
  - `WebAssembly/tool-conventions@eab11670ee6bbf5d1e9c26feee87493f76e4edbf:BasicCABI.md`.
  - `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`: `compiler/rustc_target/src/callconv/wasm.rs:1-142` (`PR #162806` `af5ab5897b`, `PR #162826` `f6b5137514`), `compiler/rustc_session/src/options.rs:2191-2193` (`parse_wasm_c_abi`), `compiler/rustc_lint/src/lib.rs:701`, and `compiler/rustc_target/src/callconv/x86.rs` (`fill_inregs`).
  - `rust-lang/rust@88120e6e4768ff17776e1bc9448c60c2b1125f74` — ABI-controlling target features as target modifiers.
  - `rust-lang/rfcs@b0e56dbdca4e1a2d90889cefa6fdfa0179e2dbb2` (RFC #3716) and `@8912d815c39b40c361bc53498e51fea1125b9137` (RFC #3980).
- **Observed execution receipts (`2026-11-25`, reproducible via `support/probe_wasm_i686_modifiers_abi.py`):**
  - `rustc +nightly wasm32-unknown-unknown` vs. `clang-19 --target=wasm32-unknown-unknown` IR parity on `SingleU32`, `SingleUnion`, `SingleUnionMixed`, `SingleUnionWithEmpty`, `WithEmpty`, `Pair`, plus `EnumZstField` `sret([1 x i8])` and `-Z wasm-c-abi=legacy` rejection (`rc=1`).
  - `i686` `rustc` `byval([8 x i8])` / `byval([12 x i8])` vs. `clang-19` `(i32, i32)` / `(i32, i32, i32)`; `-Zregparm=3` `take_u64_u32` `retl` vs. `clang-19 -mregparm=3` `movl %ecx, %eax`; `-Ctarget-feature=-sse,-sse2` rejection; and `x86_64-kcfi` / `aarch64-pauth` IR metadata.

## Revalidation

Run the self-contained probe directly from this package directory:

```bash
python3 support/probe_wasm_i686_modifiers_abi.py
```

Check whether: (1) `rustc` and `clang-19` still emit matching `wasm32` signatures for `SingleUnionMixed` and `SingleUnionWithEmpty`, (2) `rustc` `i686` still emits `byval` on `TwoI32` vs. Clang's scalar `(i32, i32)`, and (3) `rustc -Zregparm=3` still emits `retl` rather than `movl %ecx, %eax` on `take_u64_u32`.
