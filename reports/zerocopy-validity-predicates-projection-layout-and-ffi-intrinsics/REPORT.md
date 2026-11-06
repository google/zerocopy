# Zerocopy validity predicates, pointer projection, layout geometry, and FFI/intrinsic boundaries

## Summary

Across `google/zerocopy` `origin/main` revisions `41f5b37afe7060fd9fe08c00b200672cd76d77b9` (crate version `0.8.59`) and `8fb35253fbc703cb2cd0997f4efcda76cf9062b6` (crate version `0.8.63`), `zerocopy`'s soundness and verification boundary spans four coupled layers:

1. **Type-level FFI function-pointer representations (`Option<extern "C" fn(...)>`):** Production `zerocopy/src` declares no `extern "C" { ... }` foreign blocks, native `#[link]`/`#[link_name]` attributes, `core::ffi`/`std::ffi` types, or `libc` symbols. Its sole FFI-facing primitive is the ABI-qualified function-pointer type constructor (`Option<extern "C" fn(...) -> ...>` and `Option<unsafe extern "C" fn(...) -> ...>`), for which `zerocopy/src/impls.rs` and `zerocopy/src/util/macros.rs` generate `FromZeros`, a zero-only `TryFromBytes` validation predicate (`pointer::is_zeroed`), and `Immutable` by relying on Rust's `core::option` null-pointer optimization guarantee that an all-zero representation denotes `None`.
2. **Compiler-intrinsic reachability through stable `core` wrappers:** Although `zerocopy/src` contains no direct `core::intrinsics` or `rust-intrinsic` imports, its unsafe memory, layout, pointer-metadata, and arithmetic paths lower through stable or inherent `core` wrappers at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly`, pinned by `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`) directly to compiler intrinsics: `transmute`, `unreachable`, `copy_nonoverlapping`, `copy`, `write_bytes`, `read_via_copy`, `write_via_move`, `offset`, `ptr_offset_from`, `unchecked_add`/`unchecked_sub`/`unchecked_mul`, `size_of`/`align_of`, `size_of_val`/`align_of_val`, `ptr_metadata`, and `aggregate_raw_ptr`. Two negative distinctions prevent false mappings: `crate::util::transmute_unchecked` is a local `#[repr(C)]` union plus `ManuallyDrop` helper rather than `core::intrinsics::transmute_unchecked`, and `core::ptr::read_unaligned` lowers through `copy_nonoverlapping` into `MaybeUninit<T>` plus `assume_init` rather than a separate compiler intrinsic.
3. **Pointer invariants, field projection, mutation-compatible transmutation, and layout geometry:** `Ptr<'a, T, I>` carries a three-parameter invariant tuple `I = (Aliasing, Alignment, Validity)` over a live allocation-derived byte range. Field projection (`HasField`, `ProjectField`, `Ptr::project`, `project_transmute_unchecked`) shrinks a referent footprint and transfers selected invariants without deriving access permission from pure address geometry. Fallible pointer transmutation (`TryTransmuteFromPtr`, `MutationCompatible`) is directional and requires validity preservation across all permitted source and destination mutations. Slice splitting (`PtrInner::split_at_unchecked`) guarantees non-overlap only when the left dynamically sized type (DST) has no trailing padding. Pure unbounded-`Nat` Lean geometry models (`Rust.Memory` and `Rust.Layout`, inlined below) separate numerical footprint inclusion (`FitsInAllocation`) and slice-DST alignment rounding (`reprCSliceDstSize_aligned`, `roundUpToAlign_ge`) from physical allocation liveness, target word bounds, and access authority. A native `aarch64-apple-darwin` compiler probe confirms that forming a reference `&packet.value` to an unaligned `#[repr(C, packed)]` `u32` field fails with `E0793`, whereas `(&raw const packet.value).read_unaligned()` succeeds and prints `value=12345678`.
4. **Captured Charon ULLBC/LLBC and Aeneas Lean pass certificates for scalar validity:** Compiling `zerocopy`'s scalar validity predicates (`bool_encoding`, `nonzero_encoding`, `read_byte`) through the legacy Anneal `alpha24` toolchain (`Charon 0.1.210`, `rustc 1.98.0-nightly@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `Lean 4.30.0-rc2@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) yields identical 5-operation raw ULLBC and structured LLBC instruction sequences (`StorageLive(2)`, `Copy(2, 1)`, `LessMove(0, 2, 2#u8)`, `StorageDead(2)`, `Return`) for `bool_encoding`. Kernel-checked Lean theorems in `ImportedBool.lean` and `CapturedProofs.lean` prove equivalence between raw ULLBC and structured LLBC (`captured_raw_final`), equivalence between the imported operational state machine and the emitted Aeneas `bool_encoding` function (`imported_emitted`), exact acceptance of `0` and `1` across all `U8` inputs (`raw_domain`, `bool_all`), non-zero acceptance on `Usize` (`nonzero_all`), and local-store frame preservation outside locals `0, 1, 2` (`frame_preserved`).

## Applicability

This report synthesizes source analysis, compiler-contract verification, native layout probes, and Charon/Aeneas/Lean translation captures across two `google/zerocopy` `origin/main` revisions and their paired Rust, Charon, Aeneas, and Lean toolchains:

- **`google/zerocopy` multi-version coverage (`41f5b37afe70` and `8fb35253fbc7`):**
  - `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`0.8.59`) and `google/zerocopy@8fb35253fbc703cb2cd0997f4efcda76cf9062b6` (`0.8.63`).
  - **Shared across both revisions:** `zerocopy/src/impls.rs` (blob `4df786fd2104854e1fa259a63c29cd8781f8a404`), `zerocopy/src/util/macros.rs` (blob `21b9891088c5a07571f789d8d48b8d24395cfaac`), `zerocopy/src/pointer/invariant.rs` (blob `e798feb4f1f0c90d9f048afc75791f4614fe59a5`), `zerocopy/src/pointer/transmute.rs` (blob `7aabb149def839a3775cf939355061dad1b2c839`), `zerocopy/src/util/macro_util.rs` (blob `f374a089f414614ea81764ae1ee078af05d27109`), `zerocopy/zerocopy-derive/src/derive/known_layout.rs` (blob `8ff7d809defecfa9f7fde0944de9fa60eb1678f2`), and `zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs` (blob `5be26ba9fccb4d52cc1dffa850b840f241b7994c`) are byte-for-byte identical between `41f5b37afe70` and `8fb35253fbc7`. Consequently, all findings regarding optional `extern "C" fn` traits, `Ptr` invariant lattice declarations (`Aliasing`, `Alignment`, `Validity`), `TryTransmuteFromPtr`/`MutationCompatible`, and `KnownLayout`/`TryFromBytes` proc-macro derive generation apply identically to both revisions.
  - **Version-specific evolution (`41f5b37afe70` vs. `8fb35253fbc7`):** The FFI and compiler-intrinsic inventories were anchored at `41f5b37afe70` (`zerocopy/src/lib.rs` blob `944f177c0b0bf66ebd136e5f21ae1b4c2bde48b5`, `zerocopy/src/pointer/ptr.rs` blob `dcf47b29ddd2059f409301fb2f4b86ee4917f569`, `zerocopy/src/pointer/inner.rs` blob `023df07d045243e0a2924de1d4db2826d2770bb4`), whereas the `Ptr` projection and `SplitAt` layout boundary audit tracks the expanded slice-DST and `Ptr` implementation present at `8fb35253fbc7` (`zerocopy/src/pointer/ptr.rs` blob `2a492171d6e87394667acca510a9a551138827f1`, `zerocopy/src/split_at.rs` blob `7f15e4f585d2c27b7f9c4cfbf51cd11c28b611e7`, and `zerocopy/src/layout.rs`).
- **Rust compiler and normative Reference revisions:**
  - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly`, selected by `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` version `0.1.210`) paired with `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` for the FFI and compiler-intrinsic inventories.
  - `rust-lang/rust@d8ef4f3fe7031514cbd7d056b7b058814987ecec` paired with `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb` for standard-library pointer/cell contracts (`library/core/src/ptr/mod.rs`, `library/core/src/cell.rs`) and normative layout/UB rules (`src/type-layout.md`, `src/behavior-considered-undefined.md`).
  - `rust-lang/rust@b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` (rustc `1.99.0`, LLVM `23.1.1`, host `aarch64-apple-darwin`, edition 2021, default debug profile) for the native packed-struct reference-formation versus `read_unaligned` execution probes.
- **Charon, Aeneas, and Lean translation and certificate-checking boundary:**
  - Official legacy Anneal `alpha24` macOS `aarch64` archive (`anneal-toolchain-macos-aarch64.tar.zst`, SHA-256 `b4e0a5b420eb441e37564c365f06c215f61a3b825fc3df37293da7c3010d2b81`), bundling `Charon 0.1.210`, `rustc 1.98.0-nightly@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`aarch64-apple-darwin`), Aeneas binary SHA-256 `244397c4178329f2b8ab48240cd19dafd6511efb6c4e78be6345011ca8786f8e`, and `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).
  - `leanprover/lean4@a39eab69e1eee9ad38f4efe507907b1026a77808` identifies the upstream Lean kernel nested-inductive parameter validation fix in `src/kernel/inductive.cpp` (released in Lean `4.32.2`) that separates unpatched `v4.30.0-rc2` / `v4.31.0` kernel checking from fixed kernels.
- **Source-inventory scope boundaries:**
  - "Used by `zerocopy`" means representations, `core` wrappers, or contracts on which production code in `zerocopy/src` (and `zerocopy-derive/src` where noted) directly relies. Vendored dependencies under `zerocopy/vendor`, workspace development tools, and test-only foreign declarations are excluded from the production crate primitive surface.

## Findings

### 1. FFI-Facing Primitive Surface at `google/zerocopy` (`41f5b37afe70` and `8fb35253fbc7`)

#### 1.1 Production `zerocopy` has a type-level FFI surface, not a native symbol-import surface

A repository-scoped search over `zerocopy/src` (and `zerocopy-derive/src`) for `extern "C"` matches exactly two production files: `zerocopy/src/impls.rs` and `zerocopy/src/util/macros.rs`. Both occurrences construct or implement traits for ABI-qualified function-pointer **types**, not foreign function or static item declarations.

The same scoped search over `zerocopy/src` and `zerocopy-derive/src` found:
- zero `extern {` or `extern "C" {` foreign blocks;
- zero `#[link]` or `#[link_name]` attributes;
- zero `libc::`, `core::ffi`, or `std::ffi` paths;
- zero C scalar/string aliases such as `c_void`, `c_char`, or `CStr`; and
- zero `extern "system"`, `extern "C-unwind"`, or `extern "cdecl"` production type constructors.

`zerocopy/Cargo.toml` declares no normal `libc` dependency; its only ordinary dependency is optional `zerocopy-derive` (plus a disabled target dependency pinning the matching derive version), while remaining entries are development dependencies. Vendored crates under `zerocopy/vendor` contain foreign declarations, but they belong to separate Cargo compilation subjects rather than `zerocopy/src`.

Basis: **source** + **derived** from bounded negative source search (`support/zerocopy-ffi-primitives-main-41f5b37/ffi-surface.json`, `support/zerocopy-ffi-primitives-main-41f5b37/source-map.json`).

#### 1.2 Optional C-ABI function-pointer trait implementations and the all-zero `None` guarantee

In `zerocopy/src/util/macros.rs` (blob `21b9891088c5a07571f789d8d48b8d24395cfaac`), the `opt_extern_c_fn!` and `opt_unsafe_extern_c_fn!` macros feed `unsafe_impl_for_power_set` to instantiate signatures over arity subsets for:

```rust
Option<extern "C" fn(...) -> ...>
Option<unsafe extern "C" fn(...) -> ...>
```

In `zerocopy/src/impls.rs` (blob `4df786fd2104854e1fa259a63c29cd8781f8a404`, lines 310–386), `zerocopy` uses those constructors to implement:
- `FromZeros` for `Option<extern "C" fn(...) -> ...>` and `Option<unsafe extern "C" fn(...) -> ...>`;
- `TryFromBytes` for both families using `pointer::is_zeroed` as the candidate byte-validation predicate; and
- `Immutable` for both families.

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`library/core/src/option.rs`, blob `a490a26aa0ff3b3b56bb1f5a3c2a74109cbc839d`, lines 116–155), `core::option` guarantees that for qualifying function-pointer types `T` (including `fn` and `extern "C" fn`, unsafe variants, and arbitrary argument/return signatures), `Option<T>` has the same size, alignment, and function-call ABI as `T`, transmuting an all-zero byte array into `Option<T>` is sound and produces `None`, and `None` converts back to all-zero bytes.

This explains `zerocopy`'s design boundary:
1. All-zero bytes have a guaranteed valid interpretation as `None`, justifying `FromZeros`.
2. `TryFromBytes::is_bit_valid` safely accepts the all-zero representation via `pointer::is_zeroed` without claiming that arbitrary non-zero bit patterns denote valid callable function pointers.
3. In `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (`src/types/function-pointer.md`, blob `08dfbbf235d752de592f4bdf79efa3d355c58eb8`; `src/items/functions.md`, blob `362b39b5733c385a18e20a672b0f3b11a476`), `unsafe` and `extern "ABI"` are orthogonal type qualifiers on bare function pointers. Even when no foreign symbol is imported, a verifier must preserve four distinct dimensions:
   - **Type identity:** `fn` vs. `Option<fn>`, argument/return types, and safe vs. `unsafe` qualifier;
   - **ABI identity:** `"C"` calling convention vs. default Rust calling convention;
   - **Representation/niche validity:** zero bytes denote `None`, while arbitrary non-zero byte patterns are rejected by `zerocopy`'s zero-only `TryFromBytes` predicate; and
   - **Indirect-call obligation:** invoking a `Some` pointer must respect both its ABI and its safety qualifier.

Although `core::option` states its null-pointer optimization guarantee for ABI-qualified function pointers generally, `zerocopy`'s macro invocations only instantiate traits for default Rust ABI and `"C"` ABI function pointers. Test aliases in `zerocopy/src/impls.rs` (`ECFnManyArgs = extern "C" fn(...) -> ...`, suppressing `improper_ctypes_definitions`) test trait derivation on the type representation without performing runtime FFI calls.

Basis: **normative** + **documentation** + **source** + **derived**.

---

### 2. Compiler Intrinsics Reached via Stable `core` Wrappers (`nightly`)

#### 2.1 Wrapper-to-intrinsic lowering inventory

`zerocopy/src` contains no textual import of `core::intrinsics`, `std::intrinsics`, or `extern "rust-intrinsic"`. However, at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly`, pinned by `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`), the stable and inherent `core` functions invoked by `zerocopy/src` lower directly to `#[rustc_intrinsic]` declarations in `library/core/src/intrinsics/mod.rs` (blob `78d7314c58110b49839894a0f69377f4ee0d1204`):

| Zerocopy-facing operation | Pinned `core` implementation (`14210df0e27c`) | Representative `zerocopy/src` use (`41f5b37afe70`) | Configuration note |
| --- | --- | --- | --- |
| `mem::transmute` | `core::mem` (`62c612e7ba2a`, lines 66–68) re-exports `intrinsics::transmute` (`#[rustc_intrinsic]`, lines 838–857) | Exported `transmute!` and `try_transmute!` (`src/macros.rs:60–210, 610–665`); `Unalign<T>` reference conversion (`src/wrappers.rs:230–260`); ZST dangling-pointer construction (`src/util/mod.rs:425–455`) | Ordinary source, with some call sites feature-specific |
| `hint::unreachable_unchecked` | `core::hint` (`90326e649058`, lines 101–113) checks debug contract, then calls `intrinsics::unreachable` (lines 380–400) | Impossible `AlignmentError<_, Unaligned>` conversion (`src/error.rs:345–375`); impossible `FromBytes` alignment branches (`src/lib.rs:5415–5580`); impossible `KnownLayout` size branch (`src/pointer/mod.rs:365–400`); `NumExt` polyfills (`src/util/mod.rs:721–800`) | Ordinary source; also used by old-toolchain numeric polyfills |
| `ptr::copy_nonoverlapping` | `core::ptr` (`ff2c18d685b6`, lines 430–552) calls `intrinsics::copy_nonoverlapping` (lines 3019–3050) | `TryFromBytes` candidate initialization (`src/lib.rs:3535–3590`); `util::copy_unchecked` (`src/util/mod.rs:270–390`) | Ordinary source |
| Raw-pointer `copy_to` / `ptr::copy` | `const_ptr.rs` (`5cbbebf9f478`, lines 1222–1253) / `mut_ptr.rs` (`53ef7f754d20`, lines 1314–1385) call `intrinsics::copy` | Overlapping element shift in `FromZeros::extend_vec_zeroed` / `insert_vec_zeroed` (`src/lib.rs:3990–4080`) | `alloc` feature |
| Raw-pointer `write_bytes` | `mut_ptr.rs` (`53ef7f754d20`, lines 1427–1438) calls `intrinsics::write_bytes` (lines 3019–3050) | Zero-filling newly opened vector slots (`src/lib.rs:3990–4080`) | `alloc` feature |
| `ptr::read` | `core::ptr` (`ff2c18d685b6`, lines 1690–1820) calls implementation intrinsic `intrinsics::read_via_copy` (lines 2200–2217) | `Ref::read` (`src/ref.rs:750–805`); `Unalign<T>` mutation helper (`src/wrappers.rs:350–400`) | Ordinary source; emits typed MIR load |
| `ptr::write` | `core::ptr` (`ff2c18d685b6`, lines 1910–1935) calls implementation intrinsic `intrinsics::write_via_move` (lines 2200–2217) | `Ref::write` (`src/ref.rs:750–805`); `Unalign<T>` write-back guard (`src/wrappers.rs:350–400`) | Ordinary source; emits typed MIR move |
| `ptr::read_unaligned` | `core::ptr` (`ff2c18d685b6`, lines 1690–1820) copies bytes via `copy_nonoverlapping` into `MaybeUninit<T>` and calls `assume_init` | Fallible transmute support in `src/util/macro_util.rs:536–585` | Ordinary source; **not** a separate intrinsic at this pin |
| Raw-pointer `add` / `offset` | `const_ptr.rs` (`5cbbebf9f478`, lines 340–405, 820–885) calls `intrinsics::offset` (lines 892–916) | `ByteSlice` splitting (`src/byte_slice.rs:245–310`); `PtrInner` projections (`src/pointer/inner.rs:340–425`); vector insertion (`src/lib.rs:3990–4080`) | Ordinary source and `alloc` |
| Raw-pointer `offset_from` / `byte_offset_from` | `const_ptr.rs` (`5cbbebf9f478`, lines 608–637) calls `intrinsics::ptr_offset_from` (lines 2269–2278) | Macro field byte-offset calculation (`src/util/macro_util.rs:213`) | Ordinary source |
| `usize::unchecked_add` / `unchecked_sub` / `unchecked_mul` | Inherent integer methods lower to `intrinsics::unchecked_add`, `unchecked_sub`, `unchecked_mul` (lines 1986–2011) | Cast-metadata arithmetic (`src/layout.rs:1025–1070`); DST padding/size calculation (`src/util/mod.rs:565–595`); slice-length subtraction (`src/ref.rs:360–395`, `src/byte_slice.rs:245–310`, `src/pointer/inner.rs:340–425`) | Ordinary source on `nightly`; older compilers use `NumExt` polyfill |
| `size_of` / `align_of` | `intrinsics::size_of` and `intrinsics::align_of` (lines 2777–2800) | Pervasive static layout checks and calculations | Ordinary source |
| `size_of_val_raw` / `align_of_val_raw` | `intrinsics::size_of_val` and `intrinsics::align_of_val` (lines 2850–2874) | Dynamic layout/metadata machinery and `cfg(miri)` alignment promises | Configuration-dependent |
| `ptr::from_raw_parts{,_mut}` and `ptr::metadata` | `metadata.rs` (`1eeadf1217b5`, lines 3–6, 90–134) calls `intrinsics::aggregate_raw_ptr` and `intrinsics::ptr_metadata` (lines 3002–3017) | Raw slice pointer assembly (`src/lib.rs:6020–6115`, `src/byte_slice.rs:245–310`, `src/pointer/inner.rs:340–425`, `src/pointer/mod.rs:365–400`) and `KnownLayout` metadata plumbing | Ordinary source |

Basis: **source** + **derived** (`support/zerocopy-rust-intrinsics/intrinsic-surface.json`, `support/zerocopy-rust-intrinsics/source-map.json`).

#### 2.2 Critical disambiguations for MIR/LLBC translation

1. **Compile-time vs. runtime `mem::transmute`, and local `transmute_unchecked`:**
   - `transmute!` invokes `core::mem::transmute` at runtime, relying on the compiler intrinsic's static size-equality check.
   - `try_transmute!` places `core::mem::transmute(e)` inside an unexecuted `if false` branch so rustc enforces static size equality during type checking while the executed branch reads through `read_unaligned` (`src/macros.rs:610–665`).
   - `crate::util::transmute_unchecked<Src, Dst>` (`src/util/mod.rs:270–390`) is **not** `core::intrinsics::transmute_unchecked`; it statically asserts equal sizes and projects through a `#[repr(C)]` union of `ManuallyDrop<Src>` and `ManuallyDrop<Dst>`.
2. **Typed MIR loads/moves (`read_via_copy` and `write_via_move`) vs. byte copies:**
   - `ptr::read` and `ptr::write` deliberately lower through `read_via_copy` and `write_via_move` so MIR preserves typed load and move semantics rather than untyped byte copies. By contrast, `ptr::read_unaligned` lowers through `copy_nonoverlapping` into a local `MaybeUninit<T>` followed by `assume_init`.
3. **Configuration-split unchecked arithmetic (`nightly` inherent methods vs. `NumExt`):**
   - On `nightly`, `usize::unchecked_add`, `unchecked_sub`, and `unchecked_mul` resolve to inherent integer methods backed by the unchecked arithmetic intrinsics. On older compilers where `NumExt` (`src/util/mod.rs:721–800`) is selected, the same method calls expand to `checked_*` followed by `hint::unreachable_unchecked()` on `None`.

Basis: **source** + **derived**.

---

### 3. Pointer Invariants, Field Projections, Mutation-Compatible Transmutation, and Layout Geometry

#### 3.1 `Ptr<'a, T, I>` resource invariant vs. pure address-range geometry (`Rust.Memory`)

In `zerocopy/src/pointer/ptr.rs` (blob `2a492171d6e87394667acca510a9a551138827f1`, struct `Ptr` and `Ptr::from_inner` safety contract starting at line 33) and `zerocopy/src/pointer/invariant.rs` (blob `e798feb4f1f0c90d9f048afc75791f4614fe59a5`, trait `Invariants` and lattice markers around lines 56–113 and 231–237), `Ptr<'a, T, I>` encapsulates a private `PtrInner<'a, T>` together with three invariant dimensions `I = (I::Aliasing, I::Alignment, I::Validity)`:
- **Allocation and provenance base (`PtrInner`):** Non-zero-sized referents must derive from a single live allocation, lie entirely within its bounds, and remain valid for `'a`.
- **Aliasing (`Shared` vs. `Exclusive`):** `Shared` enforces shared-reference aliasing rules and permits interior mutation only through `UnsafeCell` according to library invariants; `Exclusive` enforces mutable-reference exclusivity.
- **Alignment (`Unaligned` vs. `Aligned`):** `Aligned` guarantees that the referent pointer satisfies `align_of::<T>()`.
- **Validity (`Uninit`, `Initialized`, `BitValid`, `Valid` / `Safe`):** `Initialized` requires all bytes in `T`'s footprint to be initialized; bit-validity/safety invariants additionally constrain the byte values to valid representations of `T`. Note an observed local documentation tension in `zerocopy/src/pointer/invariant.rs`: `Validity`'s trait safety contract (lines 56–69) states that the admitted set depends only on `T`'s language-level bit validity, whereas the prose documentation on `Valid` / `Safe` (lines 231–237) mentions library safety invariants alongside bit validity while its implementation comment again cites bit validity alone. Any formal substitution law that equates `Valid` across types with identical bit validity must account for whether custom library invariants are admitted.

To model the purely geometric aspect of allocation containment in Lean 4 without conflating geometry with liveness or dereference authority, the standalone `Rust.Memory` formalization (`anneal/lean/Rust/Memory.lean`, git blob `6f29babfd4f6b42c98bc460a907d69a3044026ed`, SHA-256 `f2616c9ce32b1ff339d84904fc543e8a2af1e80a812341383fc30fd2266302c9`) defines:

```lean
import Std.Tactic

namespace Rust

structure Allocation where
  base : Nat
  size : Nat
  addresses : Nat → Prop
  bounds : ∀ a, addresses a → base ≤ a ∧ a < base + size

structure Referent where
  address : Nat
  size : Nat
  addresses : Nat → Prop
  bounds : ∀ a, addresses a → address ≤ a ∧ a < address + size

abbrev Referent.IsContiguous (r : Referent) : Prop :=
  ∀ a, r.address ≤ a ∧ a < r.address + r.size → r.addresses a

abbrev FitsInAllocation (r : Referent) (a : Allocation) : Prop :=
  (∀ ⦃addr⦄, r.addresses addr → a.addresses addr) ∧
  a.base ≤ r.address ∧ r.address + r.size ≤ a.base + a.size

theorem FitsInAllocation.address_bounds_alloc (r : Referent) (a : Allocation)
    (h : FitsInAllocation r a) (addr : Nat) (ha : r.addresses addr) :
    addr < a.base + a.size :=
  a.address_lt_end addr (h.left ha)

end Rust
```

Because an empty (zero-sized) referent has no member addresses (`r.addresses addr` is vacuously false), set inclusion `∀ addr, r.addresses addr → a.addresses addr` does not constrain `r.address` for a ZST. `FitsInAllocation` therefore conjoins explicit endpoint bounds `a.base ≤ r.address ∧ r.address + r.size ≤ a.base + a.size`. Even with endpoint bounds and `Referent.IsContiguous`, `FitsInAllocation` is purely numerical over unbounded `Nat`: it does not establish storage existence, temporal liveness, byte initialization, machine-word address bounds, pointer provenance, or read/write access permission.

Basis: **source** + **derived** (`support/zerocopy-projection-validation-and-layout-cce761ad/source-evidence.json`, `support/zerocopy-projection-validation-and-layout-cce761ad/coverage.json`).

#### 3.2 Field projection (`HasField`, `ProjectField`, `Ptr::project`, `project_transmute_unchecked`)

In `zerocopy/src/lib.rs` (lines 1376–1458) and `zerocopy/src/pointer/ptr.rs` (lines 495–562 and 906–934):
- `HasField<Field, VariantId, FieldId>` guarantees that the projected field's byte range is a non-strict subset of the parent referent's byte range and preserves pointer provenance, but does **not** guarantee alignment (since a field of a `#[repr(packed)]` struct may be unaligned).
- `ProjectField` maps the parent invariant tuple to a projected tuple retaining the aliasing dimension, subject to a conditional law requiring `is_projectable` to succeed for the projected tag. `Ptr::project` reborrows the tag, checks `is_projectable`, computes the inner projection, and constructs the child `Ptr`.
- `project_transmute_unchecked` consumes the parent `Ptr` and returns an `Unaligned` projected `Ptr`. Its safety contract requires validity compatibility, mutation compatibility, and shared-aliasing coexistence soundness. Because a parent type may maintain a relational safety invariant coupling the projected child's bytes to sibling bytes outside the child's footprint, shrinking a footprint is not sufficient on its own to make child mutations sound when the parent is later recovered; parent restoration must re-establish the full parent invariant across the entire parent footprint.

Basis: **source** + **derived**.

#### 3.3 Directional and mutation-sensitive pointer transmutation (`TryTransmuteFromPtr`, `MutationCompatible`)

In `zerocopy/src/pointer/transmute.rs` (blob `7aabb149def839a3775cf939355061dad1b2c839`, trait contracts starting around line 85), `TryTransmuteFromPtr` and `MutationCompatible` govern view conversions between a source pointer `Ptr<'a, Src, IS>` and destination pointer `Ptr<'a, Dst, ID>`:
- Equal byte size and equal base address are insufficient for sound pointer transmutation.
- **Bidirectional mutation preservation:** Destination validity must survive any mutation still permitted through reachable source aliases, and source validity must survive any mutation permitted through the destination pointer.
- `MutationCompatible` discharges this obligation either by restricting aliasing/read capabilities (for example, exclusive access suspends the source pointer during the destination's lifetime, or `Shared` + `Immutable` forbids interior mutation on both sides) or by requiring mutual bit-validity implications (`TransmuteFrom` in both directions) combined with `SharedCompatible` (`UnsafeCell` layout agreement). One-way initial bit validity (`Dst: TryFromBytes` succeeding on a snapshot) does not permit shared mutable coexistence if a subsequent write through `Src` can invalidate `Dst` while `Dst` remains live.

Basis: **source** + **derived**.

#### 3.4 Runtime validation stability (`TryFromBytes::is_bit_valid` / `is_safe`, `Ptr::try_into_valid`)

In `zerocopy/src/lib.rs` (lines 1965–1997), `zerocopy/src/pointer/ptr.rs` (lines 787–825), and `zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs` (blob `5be26ba9fccb4d52cc1dffa850b840f241b7994c`, lines 32–126 and 154–195):
- `TryFromBytes::is_bit_valid` (and the experimental `is_safe` extension) takes a `Ptr<'_, Self, (Shared, _, Initialized)>` candidate and returns `true` only when the referent bytes satisfy `Self`'s validity invariant.
- `zerocopy-derive` validates struct fields sequentially through field projections and wraps any user-supplied invariant expression in an immediately invoked closure so an early `return true` inside user code cannot skip subsequent field validations. For enums, the generated validator checks the discriminant first and then validates the active variant's fields, rejecting representations without a well-defined `#[repr(C)]` or primitive discriminant layout.
- For unions (`try_from_bytes.rs:280–310`), the generated validator evaluates a disjunction over field validators (each isolated in its own closure). However, `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb` (`src/behavior-considered-undefined.md:144–145`) notes that general union bit-validity rules in Rust remain partially undecided beyond safe field construction and zero-sized fields.
- **Validation-to-use stability:** Validating a `Shared` candidate proves that the bytes were valid at the check point. Upgrading the pointer to `BitValid` / `Valid` requires that no concurrent or interleaved interior mutation (`UnsafeCell`) can overwrite the validated bytes before the consumer reads them—hence `TryFromBytes` validation on shared references requires `Immutable` (or an exclusive borrow that prevents competing writes).

Basis: **source** + **normative** + **derived**.

#### 3.5 Slice splitting (`PtrInner::split_at_unchecked`), packed DST layout (`Rust.Layout`), and the native packed-field probe

1. **Trailing padding in `PtrInner::split_at_unchecked` (`zerocopy/src/pointer/inner.rs:278–325`, `zerocopy/src/split_at.rs`):**
   - `split_at_unchecked` splits a slice-DST pointer into a left prefix DST (with shorter slice metadata) and a right trailing slice. Its safety contract explicitly notes that the left and right byte footprints are disjoint **only when the left DST has no trailing padding**; if the left prefix type's alignment introduces final padding after its shortened trailing slice, that final padding overlaps the beginning of the right slice.
   - For `Ptr<[T]>::iter` (`zerocopy/src/pointer/ptr.rs:1300–1336`), `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb` (`src/type-layout.md:74–85`) guarantees that array/slice elements have stride equal to `size_of::<T>()`, so non-ZST elements occupy disjoint byte ranges while ZST elements (`size_of::<T>() == 0`) occupy empty footprints that still retain non-null, alignment, and lifetime obligations.
2. **Packed/DST layout geometry (`KnownLayout` and `Rust.Layout`):**
   - In `zerocopy/src/lib.rs` (lines 748–770) and `zerocopy/zerocopy-derive/src/derive/known_layout.rs` (blob `8ff7d809defecfa9f7fde0944de9fa60eb1678f2`, lines 99–120 and 188–228), `KnownLayout::MaybeUninit` preserves the exact layout and pointer metadata of `Self` while admitting uninitialized bytes at all positions; for `#[repr(C)]` structs, `zerocopy-derive` preserves field order, explicit alignment, and packing modifiers, wrapping the trailing potentially unsized field in `ManuallyDrop`.
   - The standalone Lean 4 layout arithmetic formalization (`anneal/lean/Rust/Layout.lean`, git blob `a380c01ca752d3cf4e8fa5ed73a82813ea03aa3d`, SHA-256 `be6a923a4c4a993a0d9cccf5c6b76978043abb8b52b4611246d5486e1fc0f5db`) defines:

```lean
import Std.Tactic

namespace Rust

def IsAlignment (n : Nat) : Prop :=
  0 < n ∧ ∃ (k : Nat), n = 2^k

@[simp] theorem alignment_one : IsAlignment 1 := ⟨by decide, 0, by rfl⟩

structure Layout where
  size : Nat
  align : Nat
  isAlignment : IsAlignment align
  sizeAligned : align ∣ size

abbrev roundUpToAlign (val align : Nat) : Nat :=
  ((val + align - 1) / align) * align

theorem roundUpToAlign_ge (val align : Nat) (h : 0 < align) :
  val ≤ roundUpToAlign val align := by
  dsimp [roundUpToAlign]
  have h1 : ((val + align - 1) / align) * align + (val + align - 1) % align = val + align - 1 := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod _ _
  have h2 : (val + align - 1) % align < align := Nat.mod_lt _ h
  omega

theorem roundUpToAlign_aligned (val align : Nat) : align ∣ roundUpToAlign val align :=
  ⟨_, Nat.mul_comm _ _⟩

structure SliceDstLayout where
  trailingOffset : Nat
  elementSize : Nat
  align : Nat
  isAlignment : IsAlignment align

abbrev reprCSliceDstSize (info : SliceDstLayout) (elemCount : Nat) : Nat :=
  roundUpToAlign (info.trailingOffset + elemCount * info.elementSize) info.align

theorem reprCSliceDstSize_aligned (info : SliceDstLayout) (elemCount : Nat) :
    info.align ∣ reprCSliceDstSize info elemCount :=
  roundUpToAlign_aligned _ _

end Rust
```

   - `Rust.Layout` proves that `roundUpToAlign` is non-decreasing for positive alignments (`roundUpToAlign_ge`) and always yields a multiple of `align` (`reprCSliceDstSize_aligned`). Because it operates over unbounded `Nat`, a verification consumer must separately prove `usize`/`isize` non-overflow and bind the `SliceDstLayout` parameters to an actual `KnownLayout` trait dictionary.
3. **Native execution probe for `#[repr(C, packed)]` reference formation vs. `read_unaligned`:**
   - Using `rust-lang/rust@b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` (`rustc 1.99.0`, `aarch64-apple-darwin`), `support/zerocopy-projection-validation-and-layout-cce761ad/packed_bad.rs` attempts to form a shared reference `&packet.value` to the `u32` field of `#[repr(C, packed)] struct Packet { tag: u8, value: u32 }` and is rejected at compile time with error `E0793` (unaligned reference to packed field).
   - By contrast, `support/zerocopy-projection-validation-and-layout-cce761ad/packed_good.rs` takes a raw pointer `let pointer = &raw const packet.value;` and executes `unsafe { pointer.read_unaligned() }`, compiling cleanly (exit `0`) and printing `value=12345678` (`support/zerocopy-projection-validation-and-layout-cce761ad/probe-results.json`).

Basis: **source** + **normative** + **execution** + **derived**.

---

### 4. Captured Charon ULLBC/LLBC and Aeneas Lean Pass Certificate for Scalar Validity (`alpha24`)

#### 4.1 Production scalar validity predicates and stage artifact capture

The scalar validity predicates in `support/zerocopy-validity-real-pass-certificate-alpha24/validity.rs` (SHA-256 `b13d798f9bd7fc10f72256f5467d14deeaccd7e3dcb9247ee3f13944804eca76`, byte-identical to `zerocopy/src/util/validity/mod.rs`) keep candidate values in their raw integer domain (`u8` for `bool`, `usize` for `NonZeroUsize`) until validation completes:

```rust
#[inline]
pub(crate) fn bool_encoding(byte: u8) -> bool {
    byte < 2
}

#[inline]
pub(crate) fn nonzero_encoding(n: usize) -> bool {
    n != 0
}

#[inline]
#[allow(clippy::indexing_slicing)]
pub(crate) fn read_byte(bytes: &[u8], index: usize) -> u8 {
    bytes[index]
}
```

Wrapped in `support/zerocopy-validity-real-pass-certificate-alpha24/lib.rs` (`zerocopy_probe`), this module was extracted using the official legacy Anneal `alpha24` macOS `aarch64` bundle (`Charon 0.1.210`, `rustc 1.98.0-nightly@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, Aeneas SHA-256 `244397c4178329f2b8ab48240cd19dafd6511efb6c4e78be6345011ca8786f8e`). Both `charon --preset=raw-mir --ullbc` (`support/zerocopy-validity-real-pass-certificate-alpha24/captured-raw.ullbc`) and `charon --preset=aeneas` (`support/zerocopy-validity-real-pass-certificate-alpha24/captured-aeneas.llbc`) were invoked with `--extract-promoted-mir`, `--no-dedup-serialized-ast`, and `--error-on-warnings`, exiting `0` with `has_errors: false` (`support/zerocopy-validity-real-pass-certificate-alpha24/capture-results.json`).

In both `support/zerocopy-validity-real-pass-certificate-alpha24/selected-bool-raw.ullbc.json` and `support/zerocopy-validity-real-pass-certificate-alpha24/selected-bool-aeneas.llbc.json`, function ID `3` (`zerocopy_probe::util::validity::bool_encoding`) has three locals (`_0: bool` return slot, `_1: u8` argument, `_2: u8` temporary) and an identical 5-step operation list:
1. `StorageLive(_2)`
2. `Assign(_2, Copy(_1))`
3. `Assign(_0, BinOp(Lt, Move(_2), Const(2 : u8)))`
4. `StorageDead(_2)`
5. `Return`

Aeneas translates the LLBC into `support/zerocopy-validity-real-pass-certificate-alpha24/CapturedModule.lean` (exiting `0`), emitting six pure Lean 4 definitions in the `Result` monad (`util.validity.bool_encoding`, `bool_api`, `util.validity.nonzero_encoding`, `nonzero_api`, `util.validity.read_byte`, `byte_api`).

Basis: **source** + **execution** (`support/zerocopy-validity-real-pass-certificate-alpha24/aeneas-results.json`, `support/zerocopy-validity-real-pass-certificate-alpha24/artifact-identities.json`).

#### 4.2 Kernel-checked ULLBC-to-LLBC-to-Lean pass certificate and frame preservation

Two Lean 4 verification units checked with the bundled Lean `4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) certify the extracted definitions and operational state machine:

1. **Emitted specification proofs (`support/zerocopy-validity-real-pass-certificate-alpha24/CapturedProofs.lean`):**
   - `ZerocopyCapture.bool_all` proves that for every `byte : U8`, `zerocopy_probe.util.validity.bool_encoding byte = ok (decide (byte.val = 0 ∨ byte.val = 1))`.
   - `ZerocopyCapture.nonzero_all` proves that for every `n : Usize`, `zerocopy_probe.util.validity.nonzero_encoding n = ok (decide (n.val ≠ 0))`.
2. **Operational ULLBC/LLBC state certificate (`support/zerocopy-validity-real-pass-certificate-alpha24/ImportedBool.lean`):**
   - Defines an explicit local-store state machine `State` (`locals : Nat → Option Value`, `live : Nat → Bool`, `events : List String`) and instruction semantics `exec : Op → State → Option State` where `copy` requires both source and destination locals to be live and source initialized, and `lessMove` consumes the temporary (`setValue s src none`), writes the `Bool` comparison result to `dst`, and appends `"lt-move"` to `events`.
   - `captured_raw_final` proves `run rawOps s = run structuredOps s` (`rfl`).
   - `imported_emitted` proves that from any valid entry state `entry byte oldReturn oldTemp tempLive frame frameLive events` (where local `0` and `1` are live, local `1` holds `some (.byte byte)`, and locals `j ≥ 3` hold arbitrary `frame j` / `frameLive j`), executing `rawOps` and projecting local `0` via `result` equals `some (zerocopy_probe.util.validity.bool_encoding byte)`.
   - `raw_domain` chains `imported_emitted` and `ZerocopyCapture.bool_all` to prove exact acceptance of `byte.val = 0 ∨ byte.val = 1` across all 256 `U8` inputs.
   - `frame_preserved` proves that for every local index `j` with `j ≠ 0`, `j ≠ 1`, and `j ≠ 2`, `out.locals j = frame j ∧ out.live j = frameLive j`.

All six `#print axioms` checks in `support/zerocopy-validity-real-pass-certificate-alpha24/CapturedProofs.stdout` and `support/zerocopy-validity-real-pass-certificate-alpha24/ImportedBool.stdout` report only standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero `sorryAx` or `lean.ofReduceBool` (`support/zerocopy-validity-real-pass-certificate-alpha24/proof-results.json`, `support/zerocopy-validity-real-pass-certificate-alpha24/imported-bool-results.json`).

Basis: **source** + **execution** + **derived**.

## Boundaries

- **No source-level native foreign imports in `zerocopy/src`, but vendored crates are separate subjects:** The negative FFI search (`support/zerocopy-ffi-primitives-main-41f5b37/ffi-surface.json`) applies to `zerocopy/src` and `zerocopy-derive/src`. Vendored crates under `zerocopy/vendor` contain `extern "C"` blocks and must be inventoried separately if compiled into a verification target.
- **Zero-only function-pointer byte validation (`known not to apply` to non-zero bit patterns):** `zerocopy`'s `TryFromBytes` implementation for `Option<extern "C" fn(...)>` only accepts all-zero bytes (`None`). Neither `zerocopy` nor Rust's `core::option` documentation guarantees that arbitrary non-zero byte patterns form valid callable function pointers.
- **No compiled MIR/LLBC intrinsic census across all feature combinations (`not examined`):** Section 2 maps `zerocopy/src` calls to `core` intrinsics by source inspection at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`; it does not execute a whole-crate monomorphized MIR dump across every Cargo feature flag.
- **Pure geometry does not establish access authority (`known not to apply`):** Neither `Rust.Memory.FitsInAllocation` nor `Rust.Layout.reprCSliceDstSize_aligned` proves allocation liveness, initialization, provenance, or permission to dereference. Similarly, `PtrInner::split_at_unchecked` does **not** guarantee disjoint byte ranges when the left DST has trailing alignment padding.
- **Unions, portable SIMD, and full crate-wide invariant closure (`unknown` / `not examined`):** General Rust union bit-validity rules remain underspecified in the Rust Reference (`src/behavior-considered-undefined.md:144–145`), and the local documentation tension on `Valid` / `Safe` in `zerocopy/src/pointer/invariant.rs` (bit validity vs. library safety invariants) remains an **unknown** interpretation until reconciled. Portable SIMD target-feature intrinsics and whole-crate public API escape closure were **not examined**.
- **Translation frontend trust and Lean `4.30.0-rc2` kernel boundary (`unsupported` / conditional):** The `ImportedBool.lean` certificate proves equivalence after JSON-to-Lean reification for the 4-instruction scalar grammar (`StorageLive`, `Copy`, `LessMove`, `StorageDead`); it does not verify rustc MIR lowering, Charon's JSON serializer, raw pointer dereferences, loops, or function calls. Furthermore, `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) predates the nested-inductive parameter validation fix in `src/kernel/inductive.cpp` (`leanprover/lean4@a39eab69e1eee9ad38f4efe507907b1026a77808`, released in `v4.32.2`), so adversarial producer acceptance requires a patched kernel even though the owned non-nested proofs here use no exploit.

## Evidence

- **FFI primitive inventory (acquired 2026-09-27):**
  - `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (and identical blobs at `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`): `zerocopy/src/impls.rs` (blob `4df786fd2104854e1fa259a63c29cd8781f8a404`, lines 310–386), `zerocopy/src/util/macros.rs` (blob `21b9891088c5a07571f789d8d48b8d24395cfaac`), `zerocopy/Cargo.toml` (blob `4d98fb3f96784bbff0c5c7cb72b800b3a65ed765`).
  - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`: `library/core/src/option.rs` (blob `a490a26aa0ff3b3b56bb1f5a3c2a74109cbc839d`, lines 116–155).
  - `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`: `src/types/function-pointer.md` (blob `08dfbbf235d752de592f4bdf79efa3d355c58eb8`), `src/items/functions.md` (blob `362b39b5733c385a18e20a928d75f960f1cd427e`).
  - Preserved search matrix and source map: `support/zerocopy-ffi-primitives-main-41f5b37/ffi-surface.json` and `support/zerocopy-ffi-primitives-main-41f5b37/source-map.json`.
- **Compiler-intrinsic reachability inventory (acquired 2026-09-27):**
  - `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`: `zerocopy/src/macros.rs` (`2b5a66929f54`), `zerocopy/src/util/mod.rs` (`50454af00ccf`), `zerocopy/src/lib.rs` (`944f177c0b0b`), `zerocopy/src/ref.rs` (`dd0816327ba2`), `zerocopy/src/wrappers.rs` (`2d4ff5515918`), `zerocopy/src/util/macro_util.rs` (`f374a089f414`), `zerocopy/src/byte_slice.rs` (`3b70ecc2481a`), `zerocopy/src/pointer/inner.rs` (`023df07d0452`), `zerocopy/src/pointer/mod.rs` (`03b17bf0786e`), `zerocopy/src/layout.rs` (`d58786d637cf`), `zerocopy/src/error.rs` (`afdbc0382916`).
  - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`: `library/core/src/intrinsics/mod.rs` (`78d7314c5811`), `library/core/src/mem/mod.rs` (`62c612e7ba2a`), `library/core/src/hint.rs` (`90326e649058`), `library/core/src/ptr/mod.rs` (`ff2c18d685b6`), `library/core/src/ptr/const_ptr.rs` (`5cbbebf9f478`), `library/core/src/ptr/mut_ptr.rs` (`53ef7f754d20`), `library/core/src/ptr/metadata.rs` (`1eeadf1217b5`).
  - `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`: `rust-toolchain` (`4e348edab20d6bd5b195e758afe20f9d8258a3e1`).
  - Preserved mapping tables: `support/zerocopy-rust-intrinsics/intrinsic-surface.json` and `support/zerocopy-rust-intrinsics/source-map.json`.
- **Pointer projection, validation, layout geometry, and packed probe (acquired 2026-10-14):**
  - `google/zerocopy@8fb35253fbc703cb2cd0997f4efcda76cf9062b6`: `zerocopy/src/pointer/ptr.rs` (`2a492171d6e87394667acca510a9a551138827f1`), `zerocopy/src/pointer/invariant.rs` (`e798feb4f1f0c90d9f048afc75791f4614fe59a5`), `zerocopy/src/pointer/transmute.rs` (`7aabb149def839a3775cf939355061dad1b2c839`), `zerocopy/src/split_at.rs` (`7f15e4f585d2c27b7f9c4cfbf51cd11c28b611e7`), `zerocopy/zerocopy-derive/src/derive/known_layout.rs` (`8ff7d809defecfa9f7fde0944de9fa60eb1678f2`), `zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs` (`5be26ba9fccb4d52cc1dffa850b840f241b7994c`), plus the inlined `Rust.Memory` (`6f29babfd4f6b42c98bc460a907d69a3044026ed`) and `Rust.Layout` (`a380c01ca752d3cf4e8fa5ed73a82813ea03aa3d`) modules.
  - `rust-lang/rust@d8ef4f3fe7031514cbd7d056b7b058814987ecec` (`library/core/src/cell.rs`, `library/core/src/ptr/mod.rs`) and `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb` (`src/type-layout.md`, `src/behavior-considered-undefined.md`).
  - Preserved packed-field probe and metadata: `support/zerocopy-projection-validation-and-layout-cce761ad/packed_bad.rs`, `support/zerocopy-projection-validation-and-layout-cce761ad/packed_good.rs`, `support/zerocopy-projection-validation-and-layout-cce761ad/probe-results.json`, `support/zerocopy-projection-validation-and-layout-cce761ad/source-evidence.json`, and `support/zerocopy-projection-validation-and-layout-cce761ad/coverage.json`.
- **Charon/Aeneas/Lean scalar-validity pass certificate (acquired 2026-10-14):**
  - Preserved source, stage exports, Lean proofs, and logs under `support/zerocopy-validity-real-pass-certificate-alpha24/`: `validity.rs`, `lib.rs`, `captured-raw.ullbc`, `captured-aeneas.llbc`, `selected-bool-raw.ullbc.json`, `selected-bool-aeneas.llbc.json`, `CapturedModule.lean`, `CapturedModule.stdout`, `CapturedModule.stderr`, `CapturedProofs.lean`, `CapturedProofs.stdout`, `CapturedProofs.stderr`, `ImportedBool.lean`, `ImportedBool.stdout`, `ImportedBool.stderr`, `aeneas.stdout`, `aeneas.stderr`, `aeneas-run.stdout`, `aeneas-run.stderr`, `capture-results.json`, `aeneas-results.json`, `proof-results.json`, `imported-bool-results.json`, `artifact-identities.json`, `tool-identities.json`, `observation-normalization.json`, and `revalidate.py`.

## Revalidation

1. **FFI and intrinsic surface diff:** On a newer `google/zerocopy` revision, scan `zerocopy/src` and `zerocopy-derive/src` for `extern "`, foreign blocks, `#[link`, `core::ffi`, `std::ffi`, `libc::`, and `core::intrinsics`, and diff `zerocopy/src/impls.rs`, `zerocopy/src/util/macros.rs`, and the wrapper call sites in `support/zerocopy-rust-intrinsics/intrinsic-surface.json`. On a newer Rust toolchain pin, diff the `library/core/src/{intrinsics,mem,hint,ptr}` wrapper definitions to verify whether `ptr::read`, `ptr::write`, `ptr::read_unaligned`, pointer arithmetic, metadata operations, and unchecked integer arithmetic still lower to the same intrinsics.
2. **Projection, validation, and packed-field probe:** Diff `zerocopy/src/pointer/{ptr,invariant,transmute,inner}.rs` and `zerocopy/zerocopy-derive/src/derive/{known_layout,try_from_bytes}.rs` together; verify parent suspension/restoration and validation-to-use immutability bounds. Re-run `rustc support/zerocopy-projection-validation-and-layout-cce761ad/packed_bad.rs` (expecting `E0793`) and `rustc support/zerocopy-projection-validation-and-layout-cce761ad/packed_good.rs` (expecting `value=12345678`).
3. **Scalar validity ULLBC/LLBC/Lean pass certificate:** Run `python3 support/zerocopy-validity-real-pass-certificate-alpha24/revalidate.py` (or recompile `CapturedModule.lean`, `CapturedProofs.lean`, and `ImportedBool.lean` against the bundled Aeneas Lean backend), confirming exit status `0`, exact 5-instruction agreement between `selected-bool-raw.ullbc.json` and `selected-bool-aeneas.llbc.json`, and axiom lists restricted to `propext`, `Classical.choice`, and `Quot.sound`.
