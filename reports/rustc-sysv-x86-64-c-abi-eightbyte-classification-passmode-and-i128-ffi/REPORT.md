# System V x86_64 C-ABI Eightbyte Classification, `PassMode` Lowering, Register-Bank Rollback, and `i128` Alignment

## Summary

On `x86_64-unknown-linux-gnu`, `rustc`'s `extern "C"` ABI lowering in `compiler/rustc_target/src/callconv/x86_64.rs` and `compiler/rustc_codegen_llvm/src/abi.rs` translates System V AMD64 psABI eightbyte classification into LLVM IR signatures via a three-stage pipeline whose edge cases directly govern C-to-Rust FFI compatibility and verified compiler ABI contracts:

1. **Eightbyte join-semilattice and post-merge normalization (`NoClass < Sse < Int < Memory`):** Scalar fields inside aggregates up to `16` bytes (`n <= 2` eightbytes) merge symmetrically per eightbyte (`NoClass` is bottom identity, `Memory` is top absorbing, and `Int` dominates `Sse`), while unaligned non-ZST fields or non-vector aggregates strictly larger than `16` bytes (`n > 2`) unconditionally collapse to `Memory`. In `rust-lang/rust` (`1.98.0-nightly` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `49d734536222bf28bb6d07d885b3a81d145981da`), `Class` encodes `Int < Sse < SseUp` using `Option::min` (isomorphic on `{None, Some Sse, Some Int}` to `{NoClass, Sse, Int}`), whereas `rust-lang/rust` `main` (`058c701055c4b6f60f622d616afc0349911c38c3`) adds `X87`/`X87Up`, explicit `Class::merge` conflict rejection (`(X87|X87Up, Sse|SseUp) => Err(Memory)`), and `extend_integer_width_to(8)` for `bool` returns.
2. **Exact LLVM IR lowering of `PassMode::{Ignore, Direct, Cast, Indirect}` (`PairF32 -> double`, `Arr3U8 -> i24`, `TripleI -> sret/byval`, `I128Struct -> { i64, i64 }` vs. bare `u128 -> noundef i128`):**
   - Zero-sized types (`Empty {}`) remain `PassMode::Ignore`, omitting arguments and returning `void`.
   - `#[repr(C)] struct PairF32 { a: f32, b: f32 }` (`8 B`) classifies eightbyte `0` as `Class::Sse` with `vec_len == 1`; because `size.bytes() == 8 != 4`, `reg_component` (`x86_64.rs:148-152`) emits `Reg::f64()` -> LLVM `double`, whereas Clang (`clang/lib/CodeGen/Targets/X86.cpp:2689-2690`) emits `<2 x float>`. Both pack both `f32` payloads identically into `%xmm0[63:0]` (`abi_pair_f32` compiles to `retq`).
   - Sub-eightbyte integer structs (`Arr3U8([u8; 3])`, `3 B`) emit `Reg { kind: RegKind::Integer, size: 3 B }` -> `i24`, while mixed eightbyte structs (`PairU8F32 { a: u8, b: f32 }`) resolve `Int + Sse = Int` -> `i64` (never `double`), and two-eightbyte structs like `Mixed { a: u8, b: u16, c: f64 }` resolve `(Int, Sse)` -> `{ i64, double }`.
   - Non-vector aggregates `> 16 B` (`TripleI`, `24 B`) or structs with unaligned fields (`UnalignedPacked9`, `9 B`, `#[repr(C, packed)]`) hit `Err(Memory)` -> `sret([N x i8])` on return (consuming `%rdi` first, reducing remaining argument GP budget from `6` to `5`) and `byval([N x i8])` on arguments.
   - `#[repr(C)] struct I128Struct { x: u128 }` lowers to `PassMode::Cast { cast: CastTarget::pair(Reg::i64(), Reg::i64()) }` (`define { i64, i64 }`), whereas bare `u128` and `#[repr(transparent)] struct TransparentU128(u128)` lower to `PassMode::Direct` (`define noundef i128` at `-C opt-level >= 1`). The divergence originates in `compiler/rustc_abi/src/layout.rs:1329-1358`: `#[repr(C)]` sets `inhibit_newtype_abi_optimization() == true`, preventing single-field scalar unpacking so `I128Struct` retains `BackendRepr::Memory` (`is_aggregate() == true`) while bare `u128` and `TransparentU128` have `BackendRepr::Scalar` (`is_aggregate() == false`). Under `i128:128` (`x86_64_unknown_linux_gnu.rs:34`, present since `1.77.0`), both enforce `align = 16`, allocate `(2 GP, 0 XMM)` register slots, and compile identically (`movq %rsi, %rdx; movq %rdi, %rax; retq`), matching `gcc 15.2.0`.
3. **All-or-nothing register-bank exhaustion rollback and backfill:** `compute_abi_info` (`x86_64.rs:199-226`) checks `(int_regs.checked_sub(needed_int), sse_regs.checked_sub(needed_sse))` atomically against `(6 GP, 8 XMM)`. If either bank lacks capacity for **every** eightbyte of an argument, neither `int_regs` nor `sse_regs` is decremented and aggregates fall back wholly to `byval` on the stack, allowing subsequent 1-eightbyte arguments to backfill remaining registers (`%r9`, `%xmm7`, `%xmm0`), verified live in `gcc 15.2.0` <-> `rustc 1.98.0-nightly` execution (`C_RUST_FFI_OK`) and x86-64 assembly.
4. **Pure kernel-checked Lean `v4.34.1` formalization:** [support/SysvX8664EightbyteAbiClassificationSoundness.lean](support/SysvX8664EightbyteAbiClassificationSoundness.lean) (`1,545` total lines, `1,178` code-only lines, `84` theorems, `79` `noncomputable def`s, `487` kernel def constants, `226` kernel theorem constants) mechanizes the semilattice, `PassMode`/LLVM lowering, atomic GP/XMM bank-rollback/conservation, and pure `Nat` bit-exact serialization round-trips in `4,414.29 ms` under `-DwarningAsError=true` with `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial`, and `0` `._unsafe_rec`.

## Applicability

- **Target and ABI scope:** Applies to `x86_64-unknown-linux-gnu` (`pointer_width = 64`, LLVM data layout `"e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"`) for `extern "C"` and `extern "SysV64"` non-variadic fixed signatures over `#[repr(C)]`, `#[repr(C, packed)]`, `#[repr(transparent)]`, and primitive scalar types.
- **Examined upstream revisions and relationships:**
  - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`, `LLVM 22.1.6`) + `gcc (Debian 15.2.0-14) 15.2.0`: **live-executed** in [support/probe_sysv_x86_64_c_abi.py](support/probe_sysv_x86_64_c_abi.py) (`--emit=llvm-ir`, `--emit=asm`, `staticlib` <-> `gcc -O2` round-trip execution in [support/probe_results.json](support/probe_results.json)).
  - `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da`: **source-inspected** snapshot; `compiler/rustc_target/src/callconv/x86_64.rs` (`265` lines) differs from `14210df0e2` solely by changing `BackendRepr::ScalarPair(..)` to `BackendRepr::ScalarPair { .. }`, and `compiler/rustc_abi/src/lib.rs` parses `i128:128` at lines `618-623` (vs. lines `558-563` in `14210df0e2`).
  - `rust-lang/rust@058c701055c4b6f60f622d616afc0349911c38c3` (`main`): **source-inspected** comparison; shares the `NoClass`/`Sse`/`Int`/`Memory` core, `PairF32 -> Reg::f64()`, `TripleI -> sret/byval`, `I128Struct -> { i64, i64 }` vs. `u128 -> i128`, and register-bank rollback behavior, while adding `Class::{X87, X87Up}`, `Class::upper_half`, `Class::merge`, `Primitive::Bool` return 8-bit zext (`x86_64.rs` `328` lines), `IndirectMode::{Pointer, OnStack, AmdgpuKernelArg}`, `PassMode::IndirectUnsized`, and `CastTarget::pad_i32_count: u8` (`callconv/mod.rs` `1,017` lines).
  - `rust-lang/rust@aedd173a2c086e558c2b66d3743b344f977621a7` (`1.77.0`): **source-inspected** target specification confirming `"i128:128"` in `x86_64_unknown_linux_gnu.rs` lines `22-23`.
  - `llvm/llvm-project@9e1b2c3446261ab1a5063f442453510903ca80b8` (`main`): **source-inspected** reference for Clang's `X86_64ABIInfo` (`clang/lib/CodeGen/Targets/X86.cpp`), contrasted directly against `rustc`'s `x86_64.rs` for `PairF32` (`<2 x float>` vs. `double`) and integer promotion.
  - `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: **source-inspected** downstream verification architecture consumer; documents why Anneal's `Miri.ABI.RuntimeTargetDataLayout.default` (`i128Align := ⟨2⟩` = `4` bytes) reflects `rustc_abi::TargetDataLayout::default()` prior to target data-layout parsing and must be specialized to `⟨4⟩` (`16` bytes) for `x86_64-unknown-linux-gnu` FFI obligations.
  - `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`): **live-executed** kernel verification of [support/SysvX8664EightbyteAbiClassificationSoundness.lean](support/SysvX8664EightbyteAbiClassificationSoundness.lean).
- **Non-`extern "C"` Rust ABI distinction:** Claims about `PassMode::Cast` and SysV register-bank exhaustion rollback apply to `adjust_for_foreign_abi` (`callconv/mod.rs:662-674`), NOT `adjust_for_rust_abi` (`callconv/mod.rs:717-848`). Under `extern "Rust"`, `compute_abi_info` in `x86_64.rs` is not called at all (`x86_64` has no match arm in `adjust_for_rust_abi`).

## Findings

### 1. System V AMD64 Eightbyte Classification Semilattice and Upstream `rustc` Realization

`Basis: normative (AMD64 psABI §3.2.3) + source (rust-lang/rust, llvm/llvm-project) + derived (Lean 4 proof)`

#### 1.1 Mathematical Semilattice Structure (`NoClass < Sse < Int < Memory`)

In the System V AMD64 psABI (§3.2.3p2 rule 4) and Clang's reference classifier `X86_64ABIInfo::merge` (`llvm/llvm-project@9e1b2c34`, `clang/lib/CodeGen/Targets/X86.cpp:1990-2020`), merging two eightbyte classifications `(Accum, Field)` over `{NoClass, Sse, Int, Memory}` forms a finite bounded join-semilattice with total chain order `NoClass < Sse < Int < Memory`:

```cpp
// llvm/llvm-project@9e1b2c34 clang/lib/CodeGen/Targets/X86.cpp:2008-2019
if (Accum == Field || Field == NoClass)
  return Accum;
if (Field == Memory)
  return Memory;
if (Accum == NoClass)
  return Field;
if (Accum == Integer || Field == Integer)
  return Integer;
if (Field == X87 || Field == X87Up || Field == ComplexX87 ||
    Accum == X87 || Accum == X87Up)
  return Memory;
return SSE;
```

Because `merge` is commutative, associative, and idempotent with bottom identity `NoClass` and top absorbing element `Memory`, the classification of any eightbyte `k` in an aligned non-`X87` aggregate depends **solely on the set of field classes overlapping eightbyte `k`**, independent of field declaration order (provided layout offsets are fixed). In particular:
- Any `Memory` field forces the entire eightbyte (and, by post-merge rule, the entire aggregate) to `Memory`.
- Any `Int` field (`bool`, `i8..i128`, `u8..u128`, `ptr`) dominates any co-located `Sse` field (`f32`, `f16`) within the same 8-byte word (`mergeClass Int Sse = Int`).
- An eightbyte receives `Sse` if and only if at least one `Sse` field overlaps it and zero `Int` or `Memory` fields overlap it.

#### 1.2 How `rustc` Implements the Lattice and How `1.98.0-nightly` Differs from `main`

In `rust-lang/rust@14210df0e2` (`1.98.0-nightly`) and `rust-lang/rust@49d7345362`, `compiler/rustc_target/src/callconv/x86_64.rs:12-20, 84-95` implements the lattice via `Ord::min` over `Option<Class>` in inverted priority order:

```rust
// rust-lang/rust@14210df0e2 compiler/rustc_target/src/callconv/x86_64.rs:15-20
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Class {
    Int,
    Sse,
    SseUp,
}
// Line 88: *cls = Some(cls.map_or(c, |old| old.min(c)));
```

Here `None` encodes `NoClass`, `Some(Class::Int)` is minimal (`0`), `Some(Class::Sse)` is `1`, `Some(Class::SseUp)` is `2` (used for upper eightbytes of `> 64`-bit SSE/AVX vectors, collapsing to `Class::Sse` for `n <= 2` in lines `115-127`), and `Err(Memory)` short-circuits immediately upon encountering an unaligned non-ZST field (`lines 47-52`) or post-merge size `> 16 B` without a pure `(Sse, SseUp*)` vector (`lines 107-113`).

In `support/SysvX8664EightbyteAbiClassificationSoundness.lean`, theorem `toSysvClass_unify_commutes` proves that mapping `none ↦ NoClass`, `some .Int ↦ Int`, `some .Sse ↦ Sse`, and `some .SseUp ↦ Sse` strictly commutes with `unifyRustOpt` (`cls.map_or(c, |old| old.min(c))`) and `mergeClass`:

```lean
theorem toSysvClass_unify_commutes (old : Option RustClass) (c : RustClass) :
    toSysvClass (unifyRustOpt old c) = mergeClass (toSysvClass old) (toSysvClass (some c))
```

By contrast, `rust-lang/rust@058c701055` (`main`) extends `x86_64.rs:16-40` to five variants (`Int, Sse, SseUp, X87, X87Up`), replacing raw `old.min(c)` with `Class::merge` because `X87`/`X87Up` and `Sse`/`SseUp` are **incomparable** (joining them returns `Err(Memory)` rather than either operand):

```rust
// rust-lang/rust@058c701055 compiler/rustc_target/src/callconv/x86_64.rs:34-40
fn merge(self, other: Self) -> Result<Self, Memory> {
    match (self, other) {
        (Class::X87 | Class::X87Up, Class::Sse | Class::SseUp) => Err(Memory),
        (Class::Sse | Class::SseUp, Class::X87 | Class::X87Up) => Err(Memory),
        _ => Ok(Ord::min(self, other)),
    }
}
```

In `1.98.0-nightly` and `49d7345362`, `classify` (`x86_64.rs:54-58`) handles `Primitive::Int(..) | Primitive::Pointer(_) => Class::Int` and `Primitive::Float(_) => Class::Sse` without checking `Float::X87F80` (since Rust's `f80` support was still being wired in), whereas `main` (`058c701055`) adds `Primitive::Bool`, `Primitive::Float(Float::X87F80) => Class::X87`, `X87Up` post-merge validation (`lines 152-161`), and `if !is_arg && arg.layout.backend_repr.is_bool() { arg.extend_integer_width_to(8); }` (`lines 311-313`). Theorem `mergeRustMain_x87_sse_conflict` in our Lean module mechanizes the `(X87|X87Up, Sse|SseUp)` conflict rejection.

---

### 2. Aggregate Cutoff Rules: Zero-Sized Types (`Ignore`), `16`-Byte Limit (`sret`/`byval`), and Unaligned Fields

`Basis: source (rust-lang/rust) + execution (probe_sysv_x86_64_c_abi.py) + derived (Lean 4 proof)`

Before register assignment, `classify_arg` (`x86_64.rs:100-128`) and `compute_abi_info` (`x86_64.rs:228-264`) enforce three structural cutoff rules:

1. **Zero-Sized Types (`PassMode::Ignore`):** In `ArgAbi::new` (`compiler/rustc_target/src/callconv/mod.rs:388`), `_ if layout.is_zst() => PassMode::Ignore`. Inside `compute_abi_info` (`x86_64.rs:255-263`), both `!fn_abi.ret.is_ignore()` and `if arg.is_ignore() { continue; }` skip `classify_arg` completely. During LLVM signature construction (`compiler/rustc_codegen_llvm/src/abi.rs:362, 376`), a `PassMode::Ignore` return emits `void` and a `PassMode::Ignore` argument is omitted from `llargument_tys` (`define void @abi_empty()`). Mechanized in `zero_size_gives_ignore` and `witness_empty_ignore`.
2. **Eightbyte Ceiling (`n > 2`, i.e., `sizeBytes > 16`) for Non-Vectors:** `classify_arg` sets `n = arg.layout.size.bytes().div_ceil(8) as usize` (`x86_64.rs:100`). For `n > MAX_EIGHTBYTES` (`n > 8`, i.e., `> 64 B`), line `101-103` returns `Err(Memory)`. For `n > 2` (`> 16 B`, proved equivalent to `16 < sz` in Lean theorem `eightbyteCount_gt_two_iff`), lines `107-113` permit registers **only** if `cls[0] == Some(Class::Sse)` and every subsequent eightbyte `cls[1..n]` equals `Some(Class::SseUp)` (i.e., a `256`-bit or `512`-bit SIMD vector). Any non-vector aggregate with `size > 16 B` (such as `#[repr(C)] struct TripleI { a: u64, b: u64, c: u64 }`, `24 B`, `n = 3`) has `cls[0] == Some(Class::Int)` and immediately returns `Err(Memory)`, lowering to:
   - Return (`is_arg == false`, `x86_64.rs:236-240`): `arg.make_indirect()` -> LLVM `ptr ... sret([24 x i8]) align 8` as parameter `0`, decrements `int_regs` from `6` to `5` (`assert_eq!(int_regs, MAX_INT_REGS); int_regs -= 1;`, mechanized in `ret_sret_leaves_5_gp_regs`), and changes LLVM return type to `void`.
   - Argument (`is_arg == true`, `x86_64.rs:233`): `arg.pass_by_stack_offset(None)` -> `PassMode::Indirect { on_stack: true }` with `pointee_align = Some(layout.align.abi)` -> LLVM `ptr ... byval([24 x i8]) align 8` (`abi.rs:517-524`).
   Notice that because `sret` is placed in `%rdi` (`x86_64.rs:255-257` runs BEFORE the argument loop!), `abi_triple_i` passes the `sret` pointer in `%rdi` and copies the `24 B` return value to `(%rdi)` (`movq %rdi, %rax` before `retq`, per SysV ABI §3.2.3p4 Rule 2 requiring `sret` functions to return the hidden pointer in `%rax`!).
3. **Unaligned Non-ZST Fields (`!off.is_aligned(layout.align.abi)`):** Even when total size is `<= 16 B` (e.g., `#[repr(C, packed)] struct UnalignedPacked9 { tag: u8, word: u64 }`, `size = 9 B`, `struct align = 1`), `classify` recurses into field `word: u64` at `off = 1 B` whose field layout has `layout.align.abi = 8 B`. Because `1 % 8 != 0` and `!layout.is_zst()`, `x86_64.rs:47-50` immediately returns `Err(Memory)`. Live probing confirms `rustc 1.98.0-nightly` lowers `abi_unaligned_packed9` to `sret([9 x i8]) align 1` and `byval([9 x i8]) align 1` (mechanized in `unaligned_non_zst_field_forces_memory` and `witness_unalignedPacked9_sret_byval`).

---

### 3. `PassMode::Cast` vs. `PassMode::Direct` Lowering and Exact Type-by-Type Traces

`Basis: source (rust-lang/rust, llvm/llvm-project) + execution (probe_sysv_x86_64_c_abi.py) + derived (Lean 4 proof)`

When `classify_arg` succeeds with `Ok(cls)` for a `<= 16 B` type, `compute_abi_info` (`x86_64.rs:243-251`) branches on `arg.layout.is_aggregate()`:

```rust
// rust-lang/rust@14210df0e2 compiler/rustc_target/src/callconv/x86_64.rs:243-251
Ok(ref cls) => {
    // split into sized chunks passed individually
    if arg.layout.is_aggregate() {
        let size = arg.layout.size;
        arg.cast_to(cast_target(cls, size));
    } else if is_arg || cx.target_spec().is_like_darwin {
        arg.extend_integer_width_to(32);
    }
}
```

#### 3.1 Why `PairF32 { a: f32, b: f32 }` Lowers to LLVM `double` Instead of `<2 x float>`

In `reg_component` (`x86_64.rs:144-156`), an eightbyte classified `Class::Sse` computes `vec_len = 1 + cls[*i + 1..].iter().take_while(|&&c| c == Some(Class::SseUp)).count()`. For `PairF32 { a: f32, b: f32 }` (`size = 8 B`), both `f32` fields lie inside eightbyte `0` (`offset 0` and `offset 4`), yielding `cls = [Some(Class::Sse), None, ...]` and `vec_len == 1`. Crucially, `x86_64.rs:148-152` inspects ONLY `size.bytes()`:

```rust
Some(if vec_len == 1 {
    match size.bytes() {
        4 => Reg::f32(),
        _ => Reg::f64(),
    }
} else { ... })
```

Because `size.bytes() == 8 != 4`, `rustc` picks `Reg::f64()` (`LlvmType` -> `double`, `abi.rs:137`) rather than `<2 x float>`. In contrast, Clang (`llvm/llvm-project@9e1b2c34`, `clang/lib/CodeGen/Targets/X86.cpp:2689-2690`) inspects the AST field types inside `GetSSETypeAtOffset` (`if (T0->isFloatTy() && T1->isFloatTy()) return llvm::FixedVectorType::get(T0, 2);`), emitting `<2 x float>`. At x86-64 machine code generation, both `double` and `<2 x float>` lower to the low `64` bits of `%xmm0` (`%xmm0[63:0]`), leaving bits `[127:64]` unused; our live `rustc -O2 --emit=asm` probe emits a pure `retq` for `abi_pair_f32`, and our live `gcc -O2` FFI call returns `(3.00, 3.75)` without loss. Lean theorem `pairF32_preserves_neg_zero_and_nan` additionally proves bit-exact preservation of non-canonical bit patterns (`-0.0f` = `0x80000000` and qNaN payload `0x7FC01234`) across 64-bit `Reg::f64()` packing.

#### 3.2 `Arr3U8 -> i24`, `PairU8F32 -> i64`, `Mixed -> { i64, double }`, and `S1 -> i64`

- **`Arr3U8 { bytes: [u8; 3] }` (`3 B`, `align 1`):** `cls[0] = Int`. In `reg_component` (`x86_64.rs:142`), `size.bytes() == 3 < 8` selects `Reg { kind: RegKind::Integer, size: Size::from_bytes(3) }`, and `Reg::llvm_type` (`abi.rs:133`: `cx.type_ix(self.size.bits())`) emits `i24` (`define i24 @abi_arr3_u8(i24 returned %0)`). On x86-64, LLVM legalizes `i24` into 32-bit `%edi` / `%eax` (`movl %edi, %eax; retq`).
- **`PairU8F32 { a: u8, b: f32 }` (`8 B`, `align 4`):** `a` (`Int`) at offset `0` and `b` (`Sse`) at offset `4` both fall into eightbyte `0`. The semilattice join `Int ⊔ Sse = Int` overrides `Sse`, selecting `Reg::i64()` (`i64`) in `%rdi`/`%rax` (never `%xmm0`). At `-C opt-level=1`, `rustc` + LLVM emits `define range(i64 0, -4294967040) i64 @abi_pair_u8_f32(i64 %0)` (`-4294967040` signed = `0xFFFF_FFFF_0000_0100` unsigned, reflecting 3 uninitialized padding bytes `[8..32)` cleared by `and i64 %0, -4294967041` inside the lowered function body).
- **`Mixed { a: u8, b: u16, c: f64 }` (`16 B`, `align 8`):** `a` (`0`) and `b` (`2`) classify eightbyte `0` as `Int` (with padding at bytes `1` and `4..7`); `c` (`8`) classifies eightbyte `1` as `Sse`. `cast_target` (`x86_64.rs:161-173`) produces `lo = Reg::i64()` (`size = 16 >= 8`), computes `size - offset = 8`, calls `reg_component` on eightbyte `1` -> `hi = Reg::f64()` (`8 != 4`), and constructs `CastTarget::pair(Reg::i64(), Reg::f64())` -> `{ i64, double }`. Because the first field goes in `%rdi`/`%rax` and the second goes in `%xmm0`, `abi_mixed` compiles to `movq %rdi, %rax; retq`. Lean theorem `mixed_pack_unpack_padding_invariant` proves that arbitrary uninitialized padding bytes at offsets `1, 4, 5, 6, 7` never affect `(a, b, c)`.
- **Complete 15-Function Live LLVM IR and Assembly Matrix (`rustc 1.98.0-nightly` + `gcc 15.2.0`):**

| Function (`extern "C"`) | Size / Align | `BackendRepr` / `is_aggregate()` | Eightbytes (`eb0, eb1`) | `PassMode` (`x86_64.rs`) | Observed LLVM IR (`-C opt-level=1`) | Observed `rustc` x86-64 Asm (`-C opt-level=2`) | Live `gcc -O2` Round-Trip Output |
| :--- | :---: | :--- | :--- | :--- | :--- | :--- | :--- |
| `abi_empty(Empty)` | `0 B / 1` | `Memory` / ZST | `Ignore` | `Ignore` | `define void @abi_empty()` | `retq` | Passed (`void`) |
| `abi_s1(S1)` | `8 B / 8` | `Memory` / `true` | `(Int, NoClass)` | `Cast(i64)` | `define i64 @abi_s1(i64 returned %0)` | `movq %rdi, %rax; retq` | `0x1122334455667788` |
| `abi_pair_i(PairI)` | `16 B / 8` | `Memory` / `true` | `(Int, Int)` | `Cast({i64, i64})` | `define { i64, i64 } @abi_pair_i({ i64, i64 } returned %0)` | Alias `= abi_i128_struct` (`MergeFunctions`) | `PairI=(101,202)` |
| `abi_triple_i(TripleI)` | `24 B / 8` | `Memory` / `true` | `Memory` (`n=3`) | Ret `Indirect` (`sret`), Arg `Indirect(on_stack)` (`byval`) | `define void @abi_triple_i(ptr ... sret([24 x i8]) align 8 %_0, ptr ... byval([24 x i8]) align 8 %x)` | `movq %rdi, %rax` + `16(%rdi)`/`(%rdi)` from `8(%rsp)..24(%rsp)` | `TripleI=(11,22,33)` |
| `abi_pair_f32(PairF32)` | `8 B / 4` | `Memory` / `true` | `(Sse, NoClass)` | `Cast(f64)` | `define double @abi_pair_f32(double %0)` | `retq` (`%xmm0[63:0]`) | `PairF32=(3.00,3.75)` |
| `abi_mixed(Mixed)` | `16 B / 8` | `Memory` / `true` | `(Int, Sse)` | `Cast({i64, f64})` | `define { i64, double } @abi_mixed({ i64, double } returned %0)` | `movq %rdi, %rax; retq` (`%xmm0` preserved) | `Mixed=(0xff12,7.50)` |
| `abi_arr3_u8(Arr3U8)` | `3 B / 1` | `Memory` / `true` | `(Int, NoClass)` | `Cast(i24)` | `define i24 @abi_arr3_u8(i24 returned %0)` | `movl %edi, %eax; retq` | `Arr3=(30,21,10)` |
| `abi_i128_struct(I128Struct)` | `16 B / 16` | `Memory` / `true` | `(Int, Int)` | `Cast({i64, i64})` | `define { i64, i64 } @abi_i128_struct({ i64, i64 } returned %0)` | `movq %rsi, %rdx; movq %rdi, %rax; retq` | `I128S=(0x123456789abcdef, 0xfedcba9876543211)` |
| `abi_bare_u128(u128)` | `16 B / 16` | `Scalar` / `false` | `(Int, Int)` | `Direct(NoUndef)` | `define noundef i128 @abi_bare_u128(i128 noundef returned %x)` | `movq %rsi, %rdx; movq %rdi, %rax; retq` | `BareU128_lo=0xfedcba9876543215` |
| `abi_transparent_u128(TransparentU128)` | `16 B / 16` | `Scalar` / `false` | `(Int, Int)` | `Direct(NoUndef)` | `define noundef i128 @abi_transparent_u128(i128 noundef returned %x)` | Alias `= abi_bare_u128` (`MergeFunctions`) | `TransU128_lo=0xfedcba9876543217` |
| `abi_pair_u8_f32(PairU8F32)` | `8 B / 4` | `Memory` / `true` | `(Int, NoClass)` | `Cast(i64)` | `define range(i64 0, -4294967040) i64 @abi_pair_u8_f32(i64 %0)` | `movabsq $-4294967041, %rax; andq %rdi, %rax; retq` | `PairU8F32=(7,2.75)` |
| `abi_unaligned_packed9(UnalignedPacked9)` | `9 B / 1` | `Memory` / `true` | `Memory` (unaligned `u64` at `+1`) | `sret([9 x i8])` + `byval([9 x i8]) align 1` | `define void @abi_unaligned_packed9(ptr ... sret([9 x i8]) align 1 %_0, ptr ... byval([9 x i8]) align 1 %x)` | `movq %rdi, %rax` + copy from `8(%rsp)` | `Packed9=(0x56,0x102030405060718)` |
| `abi_gp_exhaust_rollback` | `5×u64 + PairI + u64` | `PairI` aggregate | `(Int, Int)` rollback | `PairI -> Indirect(on_stack)` + `u64 -> %r9` | `... ptr ... byval([16 x i8]) align 8 %pair_overflow, i64 noundef %backfill_r9` | `%r9` read into `%rax`, `pair_overflow` at `8(%rsp), 16(%rsp)` | `GpRollback=139715` |
| `abi_xmm_exhaust_rollback` | `7×f64 + PairF64 + f64` | `PairF64` aggregate | `(Sse, Sse)` rollback | `PairF64 -> Indirect(on_stack)` + `f64 -> %xmm7` | `... ptr ... byval([16 x i8]) align 8 %fpair_overflow, double noundef %backfill_xmm7` | `fpair_overflow` at `8(%rsp), 16(%rsp)`, `%xmm7` added | `XmmRollback=4653.00` |
| `abi_mixed_gp_exhaust_rollback` | `6×u64 + Mixed + f64` | `Mixed` aggregate | `(Int, Sse)` rollback | `Mixed -> Indirect(on_stack)` + `f64 -> %xmm0` | `... ptr ... byval([16 x i8]) align 8 %mixed_overflow, double noundef %backfill_xmm0` | `mixed_overflow` at `16(%rsp)`, `backfill_xmm0` in `%xmm0` | `MixedRollback=2456.00` |

Note on `-C opt-level=0` vs. `-C opt-level >= 1` attributes: in `compiler/rustc_codegen_llvm/src/abi.rs:75-96`, `get_attrs` applies `OPTIMIZATION_ATTRIBUTES` (`NoAlias`, `NonNull`, `ReadOnly`, `NoUndef`, `Writable`) and `CAPTURES_ATTRIBUTES` only when `cx.sess().opts.optimize != config::OptLevel::No` (or `SanitizerSet::MEMORY` for `NoUndef`). Thus compiling `abi_bare_u128` at `-C opt-level=0` emits `define i128 @abi_bare_u128(i128 %x)` (without `noundef`), whereas `-C opt-level >= 1` emits `define noundef i128 @abi_bare_u128(i128 noundef returned %x)`. At `-C opt-level=2` over identical identity bodies `{ x }`, LLVM's `MergeFunctions` pass folds `abi_pair_i` into a direct symbol alias `abi_pair_i = abi_i128_struct` and `abi_transparent_u128` into `abi_transparent_u128 = abi_bare_u128`, empirically confirming binary codegen equivalence between the pairs!

#### 3.3 `LlvmType for CastTarget` and `PassMode::Cast` Spill-and-Reload Lowering (`abi.rs:170-208, 247-277`)

Once `x86_64::cast_target` constructs a `CastTarget`, `rustc_codegen_llvm` translates it into an LLVM IR signature type via `impl LlvmType for CastTarget` (`compiler/rustc_codegen_llvm/src/abi.rs:170-208`):

```rust
// rust-lang/rust@14210df0e2 compiler/rustc_codegen_llvm/src/abi.rs:188-207
// Simplify to a single unit or an array if there's no prefix.
// This produces the same layout, but using a simpler type.
if self.prefix.iter().all(|x| x.is_none()) {
    // We can't do this if is_consecutive is set and the unit would get
    // split on the target. Currently, this is only relevant for i128
    // registers.
    if rest_count == 1 && (!self.rest.is_consecutive || self.rest.unit != Reg::i128()) {
        return rest_ll_unit;
    }

    return cx.type_array(rest_ll_unit, rest_count);
}

// Generate a struct type with the prefix and the "rest" arguments.
let prefix_args =
    self.prefix.iter().flat_map(|option_reg| option_reg.map(|reg| reg.llvm_type(cx)));
let rest_args = (0..rest_count).map(|_| rest_ll_unit);
let args: Vec<_> = prefix_args.chain(rest_args).collect();
cx.type_struct(&args, false)
```

Notice how each probed case maps directly through those two branches:
- **`S1`, `Arr3U8`, `PairU8F32`, `PairF32` (`CastTarget::from(unit)`):** `prefix` is `[None; 8]` and `rest_count == 1`, hitting the early-return simplification at line `195` (`rest_ll_unit` = `i64`, `i24`, `i64`, and `double`).
- **`PairI`, `I128Struct`, `Mixed` (`CastTarget::pair(lo, hi)`):** `prefix[0] = Some(lo)` causes `prefix.iter().all(|x| x.is_none())` to return `false`, falling through to line `206` (`cx.type_struct(&args, false)` -> `{ i64, i64 }` or `{ i64, double }`).

Inside function prologues and call sites, `ArgAbiExt::store` (`abi.rs:247-277`) converts between the LLVM `CastTarget` representation and the Rust `PlaceRef` representation by spilling to a temporary stack `alloca` (`scratch_size = cast.size(bx)`, `scratch_align = cast.align(bx)`), calling `store_cast`, and copying only `copy_bytes = cmp::min(cast.unaligned_size(bx).bytes(), self.layout.size.bytes())` bytes into `dst`. When optimizations are enabled (`-C opt-level >= 1`), LLVM scalarizes those temporary `alloca`s (`sroa` / `mem2reg`) into pure register instructions (`movl %edi, %eax; retq` for `Arr3U8`, `andq %rdi, %rax` for `PairU8F32`, `retq` for `PairF32`), whereas for `TripleI` (`24 B`, `PassMode::Indirect`) the callee performs an actual `sret` memory store while preserving `%rdi` in `%rax`:

```asm
abi_triple_i:
    movq    %rdi, %rax          # SysV §3.2.3p4: sret pointer must also return in %rax
    movq    24(%rsp), %rcx      # third eightbyte from caller's byval stack slot [rsp+8..rsp+32)
    movq    %rcx, 16(%rdi)
    movaps  8(%rsp), %xmm0      # first two eightbytes copied as 16B SSE move
    movups  %xmm0, (%rdi)
    retq
```

---

### 4. Why `I128Struct` Lowers to `PassMode::Cast { i64, i64 }` While Bare `u128` Lowers to `PassMode::Direct i128`, and Both Match `gcc 15.2.0` (`align = 16`)

`Basis: source (rust-lang/rust, joshlf/anneal) + execution (probe_sysv_x86_64_c_abi.py) + derived (Lean 4 proof)`

#### 4.1 The `inhibit_newtype_abi_optimization()` Pivot in `rustc_abi`

Every type's `PassMode` divergence between `#[repr(C)] struct I128Struct { x: u128 }` (`{ i64, i64 }`), `#[repr(C)] struct S1 { x: u64 }` (`i64` without `noundef`), and bare `u128` / `#[repr(transparent)] struct TransparentU128(u128)` (`noundef i128`) traces to `LayoutCalculator::univariant_biased` in `compiler/rustc_abi/src/layout.rs:1327-1359` (`rust-lang/rust@14210df0e2`):

```rust
// compiler/rustc_abi/src/layout.rs:1329, 1344-1351
let optimize_abi = !repr.inhibit_newtype_abi_optimization();
...
match field.backend_repr {
    // For plain scalars, or vectors of them, we can't unpack
    // newtypes for `#[repr(C)]`, as that affects C ABIs.
    BackendRepr::Scalar(_) | BackendRepr::SimdVector { .. }
        if optimize_abi =>
    {
        abi = field.backend_repr;
    }
```

In `compiler/rustc_abi/src/lib.rs:213-215`, `inhibit_newtype_abi_optimization` checks `self.flags.intersects(ReprFlags::ABI_UNOPTIMIZABLE)` (set by `#[repr(C)]`!). Consequently:
1. **`I128Struct` and `S1` (`#[repr(C)]`):** `optimize_abi == false`, so `abi` stays `BackendRepr::Memory { sized: true }`. In `LayoutData::is_aggregate()` (`compiler/rustc_abi/src/lib.rs:2161-2168`), `BackendRepr::Memory { .. } => true`. Thus `x86_64.rs:245` enters `if arg.layout.is_aggregate()`, calling `arg.cast_to(cast_target(cls, size))`. For `I128Struct`, `classify_arg` fills `cls[0..=1]` with `Class::Int`, and `cast_target` builds `CastTarget::pair(Reg::i64(), Reg::i64())` -> `{ i64, i64 }` (dropping `Scalar::NoUndef` because `CastTarget::attrs` defaults to empty `ArgAttributes::new()`, `callconv/mod.rs:289`).
2. **Bare `u128` and `TransparentU128`:** Both have `BackendRepr::Scalar(Scalar::Initialized { value: Int(I128, false), ... })`, for which `is_aggregate() == false`. Thus `ArgAbi::new` initializes `PassMode::Direct(NoUndef)` (`callconv/mod.rs:389`), and `x86_64.rs:245-250` skips `cast_to` and runs `arg.extend_integer_width_to(32)` (a no-op since `128 >= 32`), emitting `noundef i128`.
3. **Why LLVM and `gcc` Still Agree at Machine Code Level (`%rdi:%rsi` and `%rax:%rdx`):** For `PassMode::Cast { i64, i64 }`, LLVM's `CC_X86_64_C` (`llvm/llvm-project@9e1b2c34`, `llvm/lib/Target/X86/X86CallingConv.td:561`) assigns the two `i64` components to consecutive GP registers (`RDI`, `RSI`), and `RetCC_X86_64_C` -> `RetCC_X86Common` (`X86CallingConv.td:255, 366-379`) returns them in `[RAX, RDX]`. For `PassMode::Direct i128`, `CC_X86_64_C` (`X86CallingConv.td:556-559`) splits legalized `i128` into two `i64` pieces bound by `CCIfConsecutiveRegs<CCCustom<"CC_X86_64_I128">>` ("`i128` can be either passed in two `i64` registers, or on the stack, but not split across register and stack"), again landing in `%rdi`/`%rsi` and `%rax`/`%rdx`. Note also the safeguard in `compiler/rustc_codegen_llvm/src/abi.rs:191-195`: `CastTarget::llvm_type` refuses to collapse `rest_count == 1` when `self.rest.is_consecutive && self.rest.unit == Reg::i128()`. On `x86_64-unknown-linux-gnu`, both `abi_i128_struct` and `abi_bare_u128` emit identical assembly (`movq %rsi, %rdx; movq %rdi, %rax; retq`), proved equivalent in Lean theorems `witness_i128Struct_vs_bare_u128_and_transparent` and `i128_split_join_roundtrip` / `i128_join_split_roundtrip`.

#### 4.2 `i128:128` Data Layout Parsing and the `joshlf/anneal` `RuntimeTargetDataLayout` Seam

In `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs:33-34` (unchanged across `1.77.0@aedd173a`, `1.98.0-nightly@14210df0`, `49d7345362`, and `main@058c7010`):

```rust
data_layout:
    "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128".into(),
```

Wait—notice what happens if a consumer reads `TargetDataLayout::default()` WITHOUT parsing that string! In `compiler/rustc_abi/src/lib.rs:297-327` (`14210df0e2`), `TargetDataLayout::default()` sets:
```rust
i64_align: align(32),
i128_align: align(32), // 4 bytes!
```
Only `TargetDataLayout::parse_from_llvm_datalayout_string` (`rustc_abi/src/lib.rs:558-563` in `14210df0e2`; lines `618-623` in `49d7345362`; lines `633-638` in `058c7010`) overrides `dl.i128_align` to `Align::from_bits(128)` (`16` bytes) when `i128:128` is parsed:

```rust
if bits >= i128_align_src && bits <= 128 {
    // Default alignment for i128 is decided by taking the alignment of
    // largest-sized i{64..=128}.
    i128_align_src = bits;
    dl.i128_align = a;
}
```

Our live `abi_layout_metrics` execution confirms `rs_u128_size=16`, `rs_u128_align=16`, `rs_i128s_size=16`, `rs_i128s_align=16`, matching GCC 15.2.0 `sizeof(unsigned __int128) == 16` and `_Alignof(unsigned __int128) == 16`.

**Anneal Integration Seam (`joshlf/anneal@c131b320ee`):** In `trusted/correspondence/Trusted/Correspondence.lean:862`, Anneal instantiates `runtimeTarget := Miri.ABI.RuntimeTargetDataLayout.default`, defined in `vendor/lean-miri/Miri/ABI/RuntimeLayout.lean:114-121` with `base := ⟨.big, .w64⟩` and `i128Align := ⟨2⟩` (`2^2 = 4` bytes, mirroring `rustc_abi::TargetDataLayout::default()`!). Therefore, any future Anneal `x86_64-unknown-linux-gnu` `FnAbi` / `repr(C)` layout correspondence module MUST supply an explicit target-parsed `RuntimeTargetDataLayout` with `endian := .little` and `i128Align := ⟨4⟩` (`16` bytes) rather than `RuntimeTargetDataLayout.default`; using the unparsed default would miscompute `#[repr(C)]` struct padding before `u128` fields and fail alignment checks (`!off.is_aligned(layout.align.abi)` in `x86_64.rs:47`) on valid `16`-byte-aligned SysV `u128` structs!

---

### 5. All-or-Nothing Register-Bank Exhaustion Rollback (`6` GP + `8` XMM) and Stack Alignment Interaction

`Basis: normative (AMD64 psABI §3.2.3p3) + source (rust-lang/rust, llvm/llvm-project) + execution (probe_sysv_x86_64_c_abi.py) + derived (Lean 4 proof)`

System V AMD64 ABI §3.2.3p3 forbids splitting a single argument partly into registers and partly onto the stack:
> "If there are no registers available for any eightbyte of an argument, the whole argument is passed on the stack. If registers have already been assigned for some eightbytes of such an argument, the assignments get reverted."

Both Clang (`X86_64ABIInfo::computeInfo`, `X86.cpp:3300-3307`) and `rustc` (`compute_abi_info`, `x86_64.rs:199-226`) enforce this transactionally:

```rust
// rust-lang/rust@14210df0e2 compiler/rustc_target/src/callconv/x86_64.rs:210-224
match (int_regs.checked_sub(needed_int), sse_regs.checked_sub(needed_sse)) {
    (Some(left_int), Some(left_sse)) => {
        int_regs = left_int;
        sse_regs = left_sse;
    }
    _ => {
        if arg.layout.is_aggregate() {
            cls_or_mem = Err(Memory);
        }
    }
}
```

Three subtle consequences are verified both in Lean (`assignArg_all_or_nothing_gp_insufficient`, `assignArg_all_or_nothing_xmm_insufficient`, `assignArg_no_partial_split_two_eb`, `assignArgList_gp_conservation`) and live in our `gcc -O2` <-> `rustc` executable:

1. **GP Exhaustion & `%r9` Backfill (`abi_gp_exhaust_rollback`):** After 5 `u64` args (`%rdi..%r8`), `int_regs == 1` (`%r9` free). `PairI` needs `needed_int == 2`; `1usize.checked_sub(2)` is `None`, so `PairI` rolls back completely to `byval([16 x i8]) align 8` (stack `8(%rsp), 16(%rsp)`), `int_regs` remains `1`, and the 7th parameter `backfill_r9: u64` occupies `%r9` (`addq %r9, %rax`, verified output `GpRollback=139715`).
2. **XMM Exhaustion & `%xmm7` Backfill (`abi_xmm_exhaust_rollback`):** After 7 `f64` args (`%xmm0..%xmm6`), `sse_regs == 1` (`%xmm7` free). `PairF64` needs `needed_sse == 2`; it rolls back to `byval([16 x i8]) align 8` (`8(%rsp), 16(%rsp)`), and `backfill_xmm7: f64` occupies `%xmm7` (`addsd %xmm7, %xmm0`, verified output `XmmRollback=4653.00`).
3. **Cross-Bank Atomic Rollback (`abi_mixed_gp_exhaust_rollback`):** After 6 `u64` args (`%rdi..%r9`), `(int_regs, sse_regs) == (0, 8)`. `Mixed { a: u8, b: u16, c: f64 }` needs `(1 GP, 1 XMM)`. Because `int_regs.checked_sub(1)` is `None`, `Mixed` rolls back BOTH eightbytes to `byval([16 x i8]) align 8` WITHOUT consuming `%xmm0`; `backfill_xmm0: f64` then occupies `%xmm0` (`MixedRollback=2456.00`).
4. **Immediate vs. Aggregate Asymmetric `PassMode` on Overflow (`x86_64.rs:216-222`):** Notice the `if arg.layout.is_aggregate()` guard! When a scalar immediate such as `u128` (`BackendRepr::Scalar`) or `u64` overflows the remaining register budget, `rustc` keeps `PassMode::Direct` (`i128` / `i64`) instead of switching to `byval`, relying on LLVM's X86 backend (`CC_X86_64_I128` at `X86CallingConv.td:556-559` and `CCAssignToStack<8, 8>` at line `595`) to enforce stack placement without partial splitting (`u128` aligned `16 B`). For `#[repr(C)]` aggregates (`PairI`, `I128Struct`, `Mixed`), `rustc` explicitly converts to `PassMode::Indirect { on_stack: true }` (`byval([N x i8]) align A`), preventing LLVM IR struct-splitting from straddling register/stack boundaries.

Verbatim `rustc -O2 --emit=asm` sequences captured in [support/probe_results.json](support/probe_results.json) directly confirm stack offsets `8(%rsp)` / `16(%rsp)` alongside backfilled `%r9`, `%xmm7`, and `%xmm0`:

```asm
abi_gp_exhaust_rollback:          # args: r1..r5 (%rdi,%rsi,%rdx,%rcx,%r8), PairI (stack), backfill (%r9)
    addq    %rdi, %rsi
    leaq    (%rdx,%rcx), %rax
    addq    %rsi, %rax
    addq    %r8, %rax
    addq    %r9, %rax             # %r9 backfilled AFTER PairI rolled back!
    addq    8(%rsp), %rax         # pair_overflow.a at rsp+8
    addq    16(%rsp), %rax        # pair_overflow.b at rsp+16
    retq

abi_xmm_exhaust_rollback:         # args: x0..x6 (%xmm0..%xmm6), PairF64 (stack), backfill (%xmm7)
    addsd   %xmm1, %xmm0
    ...
    addsd   %xmm6, %xmm0
    addsd   8(%rsp), %xmm0        # fpair_overflow.a at rsp+8
    addsd   16(%rsp), %xmm0       # fpair_overflow.b at rsp+16
    addsd   %xmm7, %xmm0          # %xmm7 backfilled AFTER PairF64 rolled back!
    retq

abi_mixed_gp_exhaust_rollback:    # args: g1..g6 (%rdi..%r9 -> int_regs=0, sse_regs=8), Mixed (stack), backfill (%xmm0)
    ...                           # sums g1..g6 into %r8, converts to %xmm1/%xmm2
    addsd   16(%rsp), %xmm2       # mixed_overflow.c at stack rsp+16 (NOT %xmm0!)
    addsd   %xmm2, %xmm0          # backfill_xmm0 untouched in %xmm0!
    retq
```

---

### 6. Mechanized Lean `v4.34.1` Formalization Summary

`Basis: derived (SysvX8664EightbyteAbiClassificationSoundness.lean) + execution (lean -DwarningAsError=true + MetaM audit)`

[support/SysvX8664EightbyteAbiClassificationSoundness.lean](support/SysvX8664EightbyteAbiClassificationSoundness.lean) formalizes all four core areas in `1,545` total lines (`1,350` non-blank lines; `1,178` code-only lines excluding comments/whitespace; `25` `inductive`/`structure` declarations, `79` `noncomputable def`s, `84` explicit `theorem`s) verified standalone under Lean `v4.34.1`:

| Section | Core Definitions | Key Kernel-Checked Theorems |
| :--- | :--- | :--- |
| **1. Semilattice & Rust Lattice Match** | `Class`, `mergeClass`, `classLe`, `RustClass`, `unifyRustOpt`, `toSysvClass`, `RustMainClass`, `mergeRustMain`, `mergeList` | `mergeClass_comm`, `mergeClass_assoc`, `mergeClass_idem`, `mergeClass_lub`, `mergeClass_eq_right_iff_le`, `toSysvClass_unify_commutes`, `mergeRustMain_x87_sse_conflict`, `mergeList_memory_absorbs`, `mergeList_int_dominates`, `mergeList_swap_head` |
| **2. Layout, Cutoffs & Alignment** | `PrimKind`, `ReprAttr`, `BackendRepr`, `FieldDesc`, `AbiStructDesc`, `eightbyteCount`, `spansEightbyte`, `fieldAligned`, `classifyType` | `eightbyteCount_gt_two_iff`, `zero_size_gives_ignore`, `size_over_16B_non_vector_gives_memory`, `unaligned_non_zst_field_forces_memory`, `classifyEightbyte_aligned_int_dominates`, `scalar_128_spans_both_eightbytes` |
| **3. `PassMode` & LLVM Signature** | `RegKind`, `CastTarget`, `PassMode`, `LlvmSigTy`, `effectiveIsAggregate`, `regComponent`, `castTargetOf`, `lowerClassifiedMode`, `passModeToLlvm` | Exact LLVM IR lowering for all `12` probed types (`witness_empty_ignore`, `witness_pairF32_cast_f64_double`, `witness_arr3U8_cast_i24`, `witness_mixed_cast_i64_f64`, `witness_pairU8F32_int_dominates_to_i64`, `witness_tripleI_sret_byval`, `witness_unalignedPacked9_sret_byval`, `witness_i128Struct_vs_bare_u128_and_transparent`) |
| **4. Register-Bank Rollback** | `GPReg`, `XMMReg`, `RegBudget`, `assignReturnAbi`, `assignArg`, `assignArgList`, `assignFnAbi` | `ret_sret_leaves_5_gp_regs`, `assignArg_all_or_nothing_gp_insufficient`, `assignArg_all_or_nothing_xmm_insufficient`, `assignArg_budget_monotone`, `assignArg_conserves_registers`, `assignArg_no_partial_split_two_eb`, `assignArgList_gp_conservation`, `witness_gp_exhaust_rollback_and_backfill_r9`, `witness_xmm_exhaust_rollback_and_backfill_xmm7`, `witness_mixed_gp_exhaust_rollback_and_backfill_xmm0` |
| **5. Bit-Exact Round-Trips** | `Byte3`, `PairF32Bits`, `Byte8`, `MixedMem`, `PairIBits`, `TripleIBits`, `splitU128ToPairI64`, `joinPairI64ToU128` | `arr3U8_pack_unpack_roundtrip`, `pairF32_pack_unpack_roundtrip`, `pairF32_preserves_neg_zero_and_nan`, `byte8_pack_unpack_roundtrip`, `mixed_pack_unpack_padding_invariant`, `pairI_pack_unpack_roundtrip`, `i128_split_join_roundtrip`, `i128_join_split_roundtrip`, `tripleI_stack_pack_unpack_roundtrip` |

Kernel purity and Anneal `TrustedBoundary` alignment (`joshlf/anneal@c131b320ee`, `trusted/audit/TrustedBoundary.lean`): every `def` in [support/SysvX8664EightbyteAbiClassificationSoundness.lean](support/SysvX8664EightbyteAbiClassificationSoundness.lean) uses `noncomputable def` without `noncomputable section` or `deriving` clauses on recursive inductives, preventing the Lean compiler from synthesizing `._unsafe_rec` auxiliary constants (`unsafeRecs=0`, `partials=0`, `unsafes=0`). Proof obligations similarly avoid `Classical.choice`-inducing Mathlib/Std lemmas: notably, `i128_split_join_roundtrip` proves `val / 2^64 < 2^64` for `val < 2^128` via `(Nat.div_lt_iff_lt_mul hp64_pos).mpr hmul` rather than `Nat.div_lt_of_lt_mul` (which transiently pulls `Classical.choice` in Lean `v4.34.1` via `Nat.lt_div_mul_add` / decidability helpers), keeping all `226` local theorems strictly within `{propext, Quot.sound}`.

## Boundaries

- **known not to apply — Non-`x86_64-unknown-linux-gnu` targets and ABIs:** Windows x64, Darwin x86-64 (`target_spec().is_like_darwin` return integer extension branch at `x86_64.rs:248`), 32-bit x86, AArch64, and Rust's native ABI (`FnAbi::adjust_for_rust_abi` in `callconv/mod.rs:717-848`) use distinct lowering rules and are outside this report's claims.
- **not examined — C variadic (`c_variadic = true`, `%al` XMM register count, `__va_list_tag`):** All live probes and Lean theorems cover fixed-arity `extern "C"` functions; C variadic `%al` setup (`AMD64-ABI 3.5.7`), unnamed AVX vector stack rules (`is_named_arg`), and `va_arg` spill-area stepping were not executed or mechanized here.
- **not examined — Live `clang` and `x87` `f80` / `AVX-512` `512`-bit vector execution:** Neither `clang` nor an `f80` Rust/C execution harness was run on the Capsule host (`clang` was not installed on the execution environment); Clang `X86_64ABIInfo` behavior (`<2 x float>` for `PairF32`, `Class::merge`) and `rust-lang/rust` `main` `X87`/`X87Up` / `bool` return changes (`058c701055`) were verified by direct source inspection rather than compiled execution.
- **not examined — Unsized and `SimdVector` (`BackendRepr::SimdVector`) arguments:** Unsized arguments return early at `x86_64.rs:187-191`, and explicit SIMD types > `16 B` (`__m256`/`__m512`, `Class::SseUp`) or `pass_indirectly_in_non_rustic_abis` structs (`x86_64.rs:192-196`) were not exercised in [support/probe_sysv_x86_64_c_abi.py](support/probe_sysv_x86_64_c_abi.py) and are modeled abstractly via `isVector` in Lean.
- **unknown — GCC `15.2.0` internal GIMPLE/RTL passes:** Live ABI compatibility with `gcc 15.2.0` was verified by compiling, linking, inspecting `-O2 -S` caller assembly, and executing the round-trip test binary (`C_RUST_FFI_OK`); GCC's own C frontend source (`gcc/config/i386/i386.cc`) was not inspected.

## Evidence

- **Primary source repositories and commits (all 40-hex SHAs resolved via GitHub API and inspected directly on `2026-11-24`):**
  - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`, `LLVM 22.1.6`):
    - `compiler/rustc_target/src/callconv/x86_64.rs:12-265` (`Class`, `classify_arg`, `reg_component`, `cast_target`, `compute_abi_info`)
    - `compiler/rustc_target/src/callconv/mod.rs:38-74, 265-362, 380-525, 629-715` (`PassMode`, `CastTarget`, `ArgAbi::{new, make_indirect, pass_by_stack_offset, extend_integer_width_to, cast_to}`, `FnAbi::adjust_for_foreign_abi`)
    - `compiler/rustc_codegen_llvm/src/abi.rs:41-107, 126-208, 225-282, 350-595` (`OPTIMIZATION_ATTRIBUTES`, `get_attrs`, `LlvmType`, `ArgAbiExt::store`, `FnAbiExt::llvm_type`, `apply_attrs_llfn`)
    - `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs:33-34` (`"i128:128"` in `Target::data_layout`)
    - `compiler/rustc_abi/src/lib.rs:213-215, 295-327, 436-577, 2161-2168` (`inhibit_newtype_abi_optimization`, `TargetDataLayout::default` `i128_align: align(32)`, `parse_from_llvm_datalayout_string` `i128` rule at lines `558-563`, `LayoutData::is_aggregate`)
    - `compiler/rustc_abi/src/layout.rs:1327-1359` (`LayoutCalculator::univariant_biased`, forbidding `#[repr(C)]` single-field scalar unpacking)
  - `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da`:
    - `compiler/rustc_target/src/callconv/x86_64.rs:15-265` and `compiler/rustc_abi/src/lib.rs:618-623` (`i128_align` parsing).
  - `rust-lang/rust@058c701055c4b6f60f622d616afc0349911c38c3` (`main`):
    - `compiler/rustc_target/src/callconv/x86_64.rs:16-41, 68-81, 109-163, 166-212, 217-328` (`Class::{X87, X87Up}`, `Class::merge`, `extend_integer_width_to(8)` on `bool` returns)
    - `compiler/rustc_target/src/callconv/mod.rs:39-92` (`IndirectMode`, `PassMode::IndirectUnsized`, `CastTarget::pad_i32_count: u8`)
    - `compiler/rustc_codegen_llvm/src/abi.rs:580-814` (`IndirectMode::OnStack` -> `byval`).
  - `rust-lang/rust@aedd173a2c086e558c2b66d3743b344f977621a7` (`1.77.0`):
    - `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs:22-23` (`"i128:128"` baseline).
  - `llvm/llvm-project@9e1b2c3446261ab1a5063f442453510903ca80b8` (`main`):
    - `clang/lib/CodeGen/Targets/X86.cpp:1338-1430, 1990-2020, 2022-2411, 2660-2832, 2834-3109, 3214-3309` (`X86_64ABIInfo::{merge, classify, GetSSETypeAtOffset, GetINTEGERTypeAtOffset, classifyReturnType, classifyArgumentType, computeInfo}`)
    - `llvm/lib/Target/X86/X86CallingConv.td:240-260, 366-379, 523-611` (`RetCC_X86Common`, `RetCC_X86_64_C`, `CC_X86_64_C` `CCIfConsecutiveRegs<CCCustom<"CC_X86_64_I128">>`).
  - `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
    - `trusted/lean/Trusted/MirAst.lean:77-92, 888-913` (`noncomputable def` convention, `pointerWidthBits = 64`)
    - `trusted/correspondence/Trusted/Correspondence.lean:862` (`runtimeTarget := Miri.ABI.RuntimeTargetDataLayout.default`)
    - `vendor/lean-miri/Miri/ABI/RuntimeLayout.lean:114-121` (`i128Align := ⟨2⟩` = `4 B`) and `Miri/ABI/Align.lean:29-38` (`pow2 : Nat`)
    - `trusted/audit/TrustedBoundary.lean:14-122` (`TrustedBoundary` kernel purity and axiom isolation).
- **Live compiler and FFI execution artifacts (`2026-11-24`):**
  - Runnable probe: [support/probe_sysv_x86_64_c_abi.py](support/probe_sysv_x86_64_c_abi.py)
  - Captured outputs: [support/probe_results.json](support/probe_results.json) (verifying `rustc 1.98.0-nightly` + `LLVM 22.1.6` IR at `-C opt-level=1`, x86-64 asm at `-C opt-level=2`, `gcc 15.2.0 -O2` caller asm, and live round-trip stdout `C_RUST_FFI_OK ... rs_size=16 rs_align=16 c_align=16`).
- **Kernel-checked Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) artifact (`2026-11-24`):**
  - Formalization: [support/SysvX8664EightbyteAbiClassificationSoundness.lean](support/SysvX8664EightbyteAbiClassificationSoundness.lean) (`1,545` total lines, `1,350` non-blank lines, `1,178` code-only lines, `84` theorems, `79` `noncomputable def`s).
  - Kernel check passed (`rc=0`, `4,414.29 ms`) under `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.
  - MetaM environment audit across all `487` `.defnInfo` and `226` `.thmInfo` module constants confirmed `unsafeRecs=0`, `partials=0`, `unsafes=0`, `badAxioms=0` (`125` empty-axiom constants, `101` `[propext]`, `1` `[Quot.sound]`, `0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`).

## Revalidation

1. **Re-run the live `rustc` + `gcc` LLVM IR, assembly, and FFI execution probe (executes in an isolated temporary directory without modifying the repository):**
   ```sh
   python3 -B support/probe_sysv_x86_64_c_abi.py
   ```
   Pass gate: exits `0`, prints `C_RUST_FFI_OK ... rs_size=16 rs_align=16 c_align=16 packed9_sz=9 packed9_al=1`, and prints `VERIFIED 15 LLVM IR functions`.

2. **Re-verify the kernel-checked Lean `v4.34.1` formalization with warnings treated as errors and async elaboration disabled:**
   ```sh
   LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
     "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
     -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/SysvX8664EightbyteAbiClassificationSoundness.lean
   ```
   Pass gate: exits `0` with zero diagnostics.

3. **Check whether upstream `rust-lang/rust` changed SysV classification or `PassMode` lowering relative to the pinned commits (`14210df0e2` / `058c701055`):**
   ```sh
   gh api repos/rust-lang/rust/commits/HEAD --jq .sha
   ```
   Then diff `compiler/rustc_target/src/callconv/x86_64.rs`, `compiler/rustc_target/src/callconv/mod.rs`, `compiler/rustc_codegen_llvm/src/abi.rs`, `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs`, and `compiler/rustc_abi/src/layout.rs` against `058c701055c4b6f60f622d616afc0349911c38c3` (`main`), and rerun `probe_sysv_x86_64_c_abi.py` on the new `rustc` toolchain.
