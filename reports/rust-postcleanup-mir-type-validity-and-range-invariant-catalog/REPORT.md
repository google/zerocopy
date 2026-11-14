# Complete Catalog and Formal Semantics of `Runtime(PostCleanup)` MIR Type-Validity and Layout-Range Invariants

Created: 2026-11-14
Updated: 2026-11-14

## Summary

Every typed `Place` read, `Operand` evaluation, function entry parameter, and intrinsic assumption at `Runtime(PostCleanup)` MIR carries normative type-validity and layout-range invariants that a proof-producing compiler (`MiniSSA` + `HybridTrace`) can exploit to eliminate bounds checks, overflow checks, and dead enum branches. By auditing `compiler/rustc_ty_utils/src/layout.rs`, `compiler/rustc_const_eval/src/interpret/validity.rs`, `compiler/rustc_ty_utils/src/abi.rs`, and `compiler/rustc_codegen_llvm/src/abi.rs` in `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), and executing a 24-case validity and LLVM IR emission probe ([`support/verify_mir_type_validity_catalog.py`](support/verify_mir_type_validity_catalog.py), [`support/mir_type_validity_rules.json`](support/mir_type_validity_rules.json)), we establish four governing results:

1. **Exhaustive 16-Rule Type-Validity Deduction Environment ($\Gamma_{\text{valid}}$) (`VAL-01`–`VAL-16`):**
   - Every `TyKind` and `BackendRepr` (`Scalar`, `ScalarPair`, `Vector`, `Memory`) at `Runtime(PostCleanup)` MIR maps to an exact quantifier-free bitvector/integer predicate in [`support/mir_type_validity_rules.json`](support/mir_type_validity_rules.json), verified across all 24 boundary cases (`ALL_24_VALIDITY_CASES_PASSED`).
2. **Three Soundness Traps That Any Validity-Seeded Optimizer Must Guard Against:**
   - **Trap 1 — ZST Slice Lengths (`VAL-08` vs. `VAL-09`):** For `&[T]`, `&mut [T]`, and `Box<[T]>`, the allocation byte-size bound is $\text{len} \cdot \text{sizeof}(T) \le \texttt{isize::MAX}$ (`2^{63}-1` on 64-bit). When $\text{sizeof}(T) \ge 1$, this implies $\text{len} \le \lfloor \texttt{isize::MAX} / \text{sizeof}(T) \rfloor$. However, when $\text{sizeof}(T) = 0$ (e.g., `&[()]`), $\text{len} \cdot 0 = 0 \le \texttt{isize::MAX}$ holds for **all** $\text{len} \le \texttt{usize::MAX}$ (`slice::from_raw_parts(NonNull::<()>::dangling().as_ptr(), usize::MAX)` is 100% sound in safe/Miri Rust, `case09_zst_slice_len_usize_max_sound`). Any rule deducing $\text{len} \le \texttt{isize::MAX}$ **must** check the side condition $\text{sizeof}(T) \ge 1$.
   - **Trap 2 — Raw Slice Pointers `*const [T]` / `*mut [T]` (`VAL-11`):** Unlike `&[T]` and `Box<[T]>`, constructing a raw slice pointer via `ptr::slice_from_raw_parts(ptr::null::<u8>(), usize::MAX)` is completely valid at value creation even when $\text{sizeof}(T) \ge 1$ (`case10_raw_slice_ptr_usize_max_sound`). Neither $\text{ptr} \ne 0$ nor $\text{len} \le \texttt{isize::MAX}$ holds for `*const [T]` / `*mut [T]` until the pointer is dereferenced or reborrowed into `&[T]` / `&mut [T]`.
   - **Trap 3 — Multi-Dataful-Variant Enum Niche Fallbacks (`VAL-14`):** `rustc`'s `TagEncoding::Niche` applies **only** when at most one variant has non-zero size (`dataful_variant`). Thus `Option<Result<BoundedPatU8, ()>>` (`BoundedPatU8` in `10..=250`) compresses into `1` byte (`case05_nested_option_result_niche`), whereas `Result<BoundedPatU8, bool>` has two 1-byte dataful variants (`Ok(u8)` and `Err(bool)`) and falls back to `TagEncoding::Direct` (`2` bytes). Similarly, `Result<NonZeroU32, bool>` requires `2` extra states (`Err(false)` and `Err(true)`), overflowing `NonZeroU32`'s single niche at `0` and expanding to `8` bytes (`ScalarPair`).
3. **Pattern Types (`ty::Pat`) and Wrapping `WrappingRange` (`start > end`) in `rustc 1.99.1`:**
   - In `compiler/rustc_ty_utils/src/layout.rs:244-411`, `rustc 1.99.1` models `NonZero<T>` and bounded scalar niches via `ty::Pat(ty, ty::PatternKind)`. While `PatternKind::Range { start, end }` enforces `start <= end` (`layout.rs:263-284`), `PatternKind::Or(patterns)` (`layout.rs:312-400`) joins two signed ranges meeting at the signed overflow boundary (`iN::MIN..=first_end | second_start..=iN::MAX`, such as `NonZero<i8>` or `pattern_type!(i8 is -128..=-10 | 10..=127)`) into an unsigned **wrapping `WrappingRange { start: second.0, end: first.1 }`** where `start > end` (`246..=137` in unsigned `u8`), denoting the disjunction $v_{\text{u}} \ge S_{\text{u}} \lor v_{\text{u}} \le E_{\text{u}}$ (`case06_wrapping_valid_range_or_pattern`).
4. **Why `rustc 1.99.1` Fails to Communicate Slice Length Ranges to LLVM in 3 of 4 Contexts:**
   - In `compiler/rustc_ty_utils/src/layout.rs:504`, the metadata scalar `scalar_b` of wide pointers (`ty::Slice(_) | ty::Str`) is initialized with `WrappingRange::full(size)` (`0..=usize::MAX`) to avoid query cycles during layout computation.
   - To compensate, `compiler/rustc_codegen_llvm/src/abi.rs:558-580` contains an ad-hoc override that attaches `range(i64 0, isize::MAX / elem_size + 1)` **only** to direct `PassMode::Pair` function parameters matching `ty::Ref(_, pointee_ty, _)` where `*pointee_ty.kind() == ty::Slice(element_ty)`.
   - As verified in the emitted LLVM 23.1.1 IR (`support/mir_type_validity_rules.json`), `rustc 1.99.1` **omits** the slice-length `range` attribute/metadata on:
     1. **`&str` parameters** (`@take_str`: `*pointee_ty.kind()` is `ty::Str`, not `ty::Slice`, so `%s.1` has no `range` attribute!);
     2. **`Box<[T]>` parameters** (`@take_box_slice`: `*arg.layout.ty.kind()` is `ty::Adt`, not `ty::Ref`, so `%1` has no `range` attribute!); and
     3. **All memory loads of `&[T]` / `&mut [T]` / `&str`** (`@load_slice_from_memory`: `%_2.1 = load i64, ptr %0, align 8, !noundef !5` has no `!range` metadata because `layout.rs:504` left `scalar_b.valid_range` full!).

## Applicability

- **Extends:** `rustc-mir-construct-semantics-miri-minirust-and-codegen`, `rust-validity-initialization-padding-and-transmute-semantics`, `rustc-layout-computation-target-datalayouts-and-parametricity`, `rustc-llvm-ir-attributes-metadata-and-cross-path-obligations`
- **Subjects:**
  - **Rust Compiler (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.99.1`)**: `compiler/rustc_ty_utils/src/{layout.rs,abi.rs}`, `compiler/rustc_const_eval/src/interpret/validity.rs`, `compiler/rustc_codegen_ssa/src/mir/operand.rs`, and `compiler/rustc_codegen_llvm/src/abi.rs`.
  - **The Rust Reference (`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`)**: `src/behavior-considered-undefined.md` and `src/type-layout.md`.
  - **LLVM (`rust-lang/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, `23.1.1`)**: Parameter `range(...)` attributes and load `!range` metadata.

## Findings

### 1. Complete Catalog of `Runtime(PostCleanup)` MIR Type-Validity Rules ($\Gamma_{\text{valid}}$)

`Basis: normative + source + execution (support/mir_type_validity_rules.json, support/verify_mir_type_validity_catalog.py)`

Table 1 summarizes the 16 deduction rules in $\Gamma_{\text{valid}}$ (`VAL-01`–`VAL-16`) that hold whenever a typed `Place` or `Operand` is live and initialized in `Runtime(PostCleanup)` MIR:

| Rule ID | `TyKind` / MIR Construct | `BackendRepr` | Exact $\Gamma_{\text{valid}}$ Bitvector / Integer Predicate ($W$-bit Pointer Width) | Mandatory Soundness Side Conditions | Emitted by `rustc 1.99.1` to LLVM 23.1.1? |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`VAL-01`** | `TyKind::Bool` | `Scalar(Int(I8, false), 0..=1)` | $0 \le v \le 1$ | Initialized byte | **Yes** (`i1 noundef` / `range(i8 0, 2)`) |
| **`VAL-02`** | `TyKind::Char` | `Scalar(Int(I32, false), 0..=0x10FFFF)` | $(0 \le v \le \text{0xD7FF}) \lor (\text{0xE000} \le v \le \text{0x10FFFF})$ | Surrogate gap $\text{0xD800}..\text{0xDFFF}$ excluded by Rust validity (`validity.rs`) | **Partial** (`range(i32 0, 1114112)` hull only) |
| **`VAL-03`** | `TyKind::Int` / `TyKind::Uint` | `Scalar(Int(N, s), 0..=2^N-1)` | $\text{init}(v) \land 0 \le v_{\text{u}} \le 2^N - 1$ | Every byte initialized (`noundef`) | **Yes** (`iN noundef`) |
| **`VAL-04`** | `NonZero<uN>` / `ty::Pat(uN, Range(S, E))` | `Scalar(Int(N, false), S..=E)` | $S \le v_{\text{u}} \le E$ ($1 \le v_{\text{u}} \le 2^N - 1$ for `NonZero`) | $S \le E$ (`layout.rs:248-295`) | **Yes** (`range(iN 1, 0)`) |
| **`VAL-05`** | `NonZero<iN>` / `ty::Pat(iN, Or)` | `Scalar(Int(N, true), WrappingRange(S_u, E_u))` | $v_{\text{u}} \ge S_{\text{u}} \lor v_{\text{u}} \le E_{\text{u}}$ (when $S_{\text{u}} > E_{\text{u}}$) | Unsigned wrap-around across $2^N \equiv 0$ (`layout.rs:355-391`) | **Yes** (`range(iN S_u, (E_u+1) mod 2^N)`) |
| **`VAL-06`** | `TyKind::Never` (`!`) & Uninhabited ADTs | `Memory` (`is_uninhabited() == true`) | $\bot$ (`False`) | Immediate UB on any reachable typed value production | **Yes** (`unreachable`) |
| **`VAL-07`** | `&T`, `&mut T`, `Box<T>` (`T: Sized`) | `Scalar(Pointer, 1..=2^W-1)` | $\text{addr}(p) \ge \text{align}(T) \ge 1 \land \text{addr}(p) \bmod \text{align}(T) = 0 \land \text{addr}(p) + \text{size}(T) \le 2^W - 1 \land \text{size}(T) \le \texttt{isize::MAX}$ | Holds even for ZSTs ($\text{size}(T) = 0 \implies \text{addr}(p) \ge \text{align}(T)$) | **Yes** (`nonnull align A dereferenceable(S)`) |
| **`VAL-08`** | `&[T]`, `&mut [T]`, `Box<[T]>` ($\text{sizeof}(T) \ge 1$) | `ScalarPair(Pointer, Int(usize))` | $\text{addr}(p) \ge \text{align}(T) \land \text{addr}(p) \bmod \text{align}(T) = 0 \land \text{len} \le \lfloor \texttt{isize::MAX} / \text{sizeof}(T) \rfloor \land \text{addr}(p) + \text{len} \cdot \text{sizeof}(T) \le 2^W - 1$ | **Requires $\text{sizeof}(T) \ge 1$** (`elem_size != Size::ZERO`) | **Partial** (emitted ONLY on direct `&[T]` params; **missed** on `Box<[T]>` and memory loads!) |
| **`VAL-09`** | `&[ZST]`, `&mut [ZST]`, `Box<[ZST]>` ($\text{sizeof}(T) = 0$) | `ScalarPair(Pointer, Int(usize))` | $\text{addr}(p) \ge \text{align}(T) \land \text{addr}(p) \bmod \text{align}(T) = 0 \land 0 \le \text{len} \le 2^W - 1$ | $\text{sizeof}(T) = 0 \implies \text{len}$ can legally equal $\texttt{usize::MAX}$ (`case09`) | **Yes** (no `range` on `len`) |
| **`VAL-10`** | `&str`, `&mut str`, `Box<str>` | `ScalarPair(Pointer, Int(usize))` | $\text{addr}(p) \ge 1 \land \text{len} \le \texttt{isize::MAX} \land \text{addr}(p) + \text{len} \le 2^W - 1$ | UTF-8 byte validity + $\text{sizeof}(\texttt{u8}) = 1$ | **No (`Missed` in `abi.rs:561`!)** |
| **`VAL-11`** | `*const [T]`, `*mut [T]` (raw slice ptr) | `ScalarPair(Pointer, Int(usize))` | $\text{init}(p) \land \text{init}(\text{len}) \land 0 \le \text{len} \le 2^W - 1$ | Raw pointer may be null/unaligned with $\text{len} = \texttt{usize::MAX}$ (`case10`) | **Yes** (`ptr noundef, i64 noundef`) |
| **`VAL-12`** | `&dyn Trait`, `&mut dyn Trait`, `Box<dyn Trait>` | `ScalarPair(Pointer, Pointer)` | $\text{addr}(p) \ge \text{align}(\text{vtable}) \ge 1 \land \text{addr}(v) \ge \text{align}(\texttt{usize}) \land \text{size}(\text{vtable}) \le \texttt{isize::MAX}$ | Vtable slot 1 holds size $\le \texttt{isize::MAX}$; slot 2 holds power-of-two align | **Yes** (`nonnull` on both pointers) |
| **`VAL-13`** | Enum (`TagEncoding::Direct`) | `Scalar` / `ScalarPair` / `Memory` | $\text{tag} \in [\text{lo}, \text{hi}] \land \text{fields\_valid}(\text{variant}(\text{tag}))$ | Discriminant hull stored in `tag_scalar.valid_range` | **Yes** (`!range` on discriminant load) |
| **`VAL-14`** | Enum (`TagEncoding::Niche`) | `Scalar` / `ScalarPair` | $v \in \text{hull}(\text{valid\_range}(\text{dataful}) \cup \text{niches})$ | Requires at most 1 non-ZST variant (`case05`) | **Yes** (when `!is_always_valid`) |
| **`VAL-15`** | `MaybeUninit<T>` & `union` | `Scalar::Union` / `Memory` | $\top$ (`True`: uninitialized bytes permitted; niches suppressed, `case14`) | Never assume `noundef`, `nonnull`, or `valid_range` | **Yes** (attributes omitted) |
| **`VAL-16`** | `Intrinsic::Assume(b)` & `*Unchecked` BinOps | Operational statement / rvalue | $b = \texttt{true}$; no unsigned/signed overflow on `AddUnchecked`/`SubUnchecked`/`MulUnchecked`; $\text{shift} < N$ on `ShlUnchecked`/`ShrUnchecked` | Immediate UB if violated on reachable path | **Yes** (`@llvm.assume`, `nuw`/`nsw`) |

---

### 2. Empirical Proof of the `rustc 1.99.1` Slice-Length Range Emission Gap

`Basis: source + execution (compiler/rustc_codegen_llvm/src/abi.rs:554-582, compiler/rustc_ty_utils/src/layout.rs:504, support/verify_mir_type_validity_catalog.py)`

In `compiler/rustc_codegen_llvm/src/abi.rs:558-580`, `rustc 1.99.1` computes slice length range attributes using the following pattern match:

```rust
let scalar_b = if let rustc_abi::Primitive::Int(int, false) = primitive_b
    && let ty::Ref(_, pointee_ty, _) = *arg.layout.ty.kind()
    && let ty::Slice(element_ty) = *pointee_ty.kind()
    && let elem_size = cx.layout_of(element_ty).size
    && elem_size != rustc_abi::Size::ZERO
{
    let isize_max = int.signed_max() as u64;
    rustc_abi::Scalar::Initialized {
        value: primitive_b,
        valid_range: rustc_abi::WrappingRange {
            start: 0,
            end: u128::from(isize_max / elem_size.bytes()),
        },
    }
} else {
    scalar_b
};
```

Compiling [`support/verify_mir_type_validity_catalog.py`](support/verify_mir_type_validity_catalog.py) with `rustc +1.99.1-x86_64-unknown-linux-gnu -Copt-level=3 --emit=llvm-ir` exposes the exact LLVM IR signatures emitted across all six slice/string forms:

```llvm
; 1. &[u8] parameter -> HAS range(i64 0, -9223372036854775808) [0..2^63]
define noundef range(i64 0, -9223372036854775808) i64 @take_u8_slice(
    ptr noalias nofree noundef nonnull readonly captures(none) %s.0,
    i64 noundef returned range(i64 0, -9223372036854775808) %s.1)

; 2. &[u64] parameter -> HAS range(i64 0, 1152921504606846976) [0..2^60]
define noundef range(i64 0, 1152921504606846976) i64 @take_u64_slice(
    ptr noalias nofree noundef nonnull readonly align 8 captures(none) %s.0,
    i64 noundef returned range(i64 0, 1152921504606846976) %s.1)

; 3. &str parameter -> MISSED! (%s.1 lacks range(i64 0, -9223372036854775808))
define noundef i64 @take_str(
    ptr noalias nofree noundef nonnull readonly captures(none) %s.0,
    i64 noundef returned %s.1)

; 4. Box<[u8]> parameter -> MISSED! (%1 lacks range(i64 0, -9223372036854775808))
define noundef i64 @take_box_slice(
    ptr noalias noundef nonnull captures(address) %0,
    i64 noundef returned %1)

; 5. Loading &[u8] from a struct field in memory -> MISSED! (%_2.1 lacks !range metadata)
define noundef i64 @load_slice_from_memory(
    ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(16) %h) {
start:
  %0 = getelementptr inbounds nuw i8, ptr %h, i64 8
  %_2.1 = load i64, ptr %0, align 8, !noundef !5
  ret i64 %_2.1
}
```

In `MiniSSA`, seeding $\Gamma_{\text{valid}}$ directly from the `Runtime(PostCleanup)` MIR `TyKind` at every function parameter, local assignment, `UnOp::PtrMetadata`, and typed memory load uniformly attaches $0 \le \text{len} \le \lfloor \texttt{isize::MAX} / \text{sizeof}(T) \rfloor$ across `&[T]`, `&mut [T]`, `Box<[T]>`, `Rc<[T]>`, `Arc<[T]>`, and `&str` (whenever $\text{sizeof}(T) \ge 1$), closing all three `rustc 1.99.1` emission gaps.

## Boundaries

1. **Custom Smart Pointers Wrapping Raw Slice Pointers (`known not to apply` without library invariant):**
   - While `&[T]`, `&mut [T]`, `Box<[T]>`, and `&str` have language-level validity guarantees (`VAL-08`, `VAL-10`), user-defined structs containing `*const [T]` or `NonNull<[T]>` (including the internal fields of `Rc<[T]>` / `Arc<[T]>` when accessed as raw pointers rather than dereferenced to `&[T]`) only acquire $\text{len} \le \lfloor \texttt{isize::MAX} / \text{sizeof}(T) \rfloor$ when converted to `&[T]` or annotated with an explicit `#[anneal_spec]` / `pattern_type!` invariant.
2. **Pointee Validity of References Behind Unused `UnsafeCell` (`unknown` in normative Reference edge cases):**
   - As documented in `rust-validity-initialization-padding-and-transmute-semantics`, $\Gamma_{\text{valid}}$ assumes pointer alignment, non-nullness, and allocation bounds (`dereferenceable(size(T))`) immediately upon reference creation (`VAL-07`, `VAL-08`), which is 100% sound in Miri and LLVM (`nonnull align A dereferenceable(S)`), without assuming recursive bit-validity of un-loaded pointee bytes inside `UnsafeCell<MaybeUninit<U>>`.

## Evidence

1. **Automated 24-Case Validity Probe and LLVM IR Inspector:**
   - [`support/verify_mir_type_validity_catalog.py`](support/verify_mir_type_validity_catalog.py)
2. **Machine-Readable Catalog (`VAL-01`–`VAL-16`):**
   - [`support/mir_type_validity_rules.json`](support/mir_type_validity_rules.json)
3. **Primary Source Coordinates in `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`:**
   - `compiler/rustc_ty_utils/src/layout.rs:244-540` (`ty::Pat`, `WrappingRange`, `ty::Bool`, `ty::Char`, `ty::Slice`, `ty::Str`)
   - `compiler/rustc_const_eval/src/interpret/validity.rs:1007-1580` (`ValidityVisitor`)
   - `compiler/rustc_codegen_llvm/src/abi.rs:470-585` (`apply_range_attr` and `PassMode::Pair` slice length range emission)

## Revalidation

Run the 24-case probe and LLVM IR attribute extractor:

```bash
python3 reports/rust-postcleanup-mir-type-validity-and-range-invariant-catalog/support/verify_mir_type_validity_catalog.py
```
