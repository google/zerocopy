# Rust intrinsics that zerocopy reaches at the Anneal pins

## Summary

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, the production `zerocopy` source does not import `core::intrinsics`, `std::intrinsics`, or the `rust-intrinsic` ABI directly. That absence does **not** mean that zerocopy avoids compiler intrinsics. Its unsafe and layout-sensitive code deliberately calls stable or semi-stable `core` APIs whose implementations at the Rust revision behind Anneal's pinned Charon toolchain lower directly to compiler intrinsics.

For verification work, the useful source-level inventory is:

- `mem::transmute` → the `transmute` intrinsic;
- `hint::unreachable_unchecked` → the `unreachable` intrinsic;
- `ptr::copy_nonoverlapping` and overlapping pointer-copy methods → the `copy_nonoverlapping` and `copy` intrinsics;
- pointer byte filling → the `write_bytes` intrinsic;
- `ptr::read` and `ptr::write` → the implementation-only `read_via_copy` and `write_via_move` intrinsics;
- raw-pointer `add`/`offset` and pointer differences → `offset` and `ptr_offset_from`;
- `usize::unchecked_add`, `unchecked_sub`, and `unchecked_mul` on the pinned nightly → the corresponding unchecked arithmetic intrinsics;
- `size_of`, `align_of`, raw dynamic size/alignment queries, and raw-pointer metadata operations → the matching layout and pointer-metadata intrinsics in `core`.

Two distinctions prevent common false conclusions. First, zerocopy's local function named `transmute_unchecked` is **not** `core::intrinsics::transmute_unchecked`; it is implemented with a `#[repr(C)]` union and `ManuallyDrop`. Second, `ptr::read_unaligned` is not a separate compiler intrinsic at this Rust revision: `core` implements it by copying bytes with `copy_nonoverlapping` into `MaybeUninit<T>` and then assuming initialization.

This report is an integration inventory, not a replacement for the sibling reports about each primitive's semantics. Its main consequence for Anneal is that an intrinsic census must follow the pinned `core` wrappers, not merely search zerocopy for textual `core::intrinsics` calls.

## Applicability

The zerocopy observations apply to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`. The compiler-library mappings apply to `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the Rust source revision recorded for the `nightly-2026-05-31` toolchain used by Charon in the current Anneal toolchain set. `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` independently pins `nightly-2026-05-31` in its `rust-toolchain` file.

"Used by zerocopy" in this report means a compiler-intrinsic-backed `core` operation that zerocopy's own production source invokes or can invoke under a documented crate configuration. This definition captures the boundary that a verifier or MIR/LLBC translator must model even though the Rust source names a stable wrapper rather than an intrinsic. It does not attempt to enumerate every compiler intrinsic that rustc may introduce while lowering ordinary language constructs, nor intrinsics used only inside transitive dependencies.

The inventory is source-level potential reachability, not a dynamic or monomorphized reachability set. In particular:

- some paths require `alloc`;
- some raw size/alignment calls are used only in `cfg(miri)` instrumentation or tests, while related layout operations are used in ordinary production code;
- zerocopy's `NumExt` implementations are compatibility polyfills for older compilers, while the pinned nightly has the inherent unchecked integer methods;
- test-only examples and unit-test probes are not treated as production intrinsic uses here.

The Rust primitive semantics themselves remain owned by the dedicated reference subjects for pointer arithmetic, pointer copying, transmutation, layout, raw-pointer construction, validity, and `unreachable_unchecked`. The inventory here records how those subjects connect to zerocopy and to the pinned compiler implementation.

## Findings

### Zerocopy has no direct unstable-intrinsics import boundary

A scan of the `zerocopy/src` tree at the examined revision found no production import of `core::intrinsics` or `std::intrinsics`, and no use of the `rust-intrinsic` ABI. The one repository code-search hit for `std::intrinsics` is in the historical `anneal/v1/README.md`, not in the zerocopy library source.

That source-level property is weaker than it first appears. `core` deliberately exposes stable APIs whose implementations are compiler intrinsics, so a translator that only recognizes explicit `core::intrinsics::*` syntax would miss real intrinsic-backed operations.

Basis: source + derived.

### The intrinsic-backed surface is concentrated in unsafe memory, arithmetic, layout, and metadata operations

The following table records the load-bearing mappings at the pinned Rust revision. "Zerocopy use" names representative production locations, not every call site.

| Zerocopy-facing operation | Pinned `core` implementation | Representative zerocopy use | Configuration note |
| --- | --- | --- | --- |
| `mem::transmute` | `core::mem` reexports `intrinsics::transmute`; the declaration is `#[rustc_intrinsic]` | exported transmute macros; `Unalign<T>` reference conversion; ZST allocation dangling-pointer construction; macro support | ordinary source, with some call sites feature-specific |
| `hint::unreachable_unchecked` | checks its contract, then calls `intrinsics::unreachable` | impossible `AlignmentError` conversions; impossible `FromBytes` alignment branches; impossible `KnownLayout` size branch | ordinary source; also used by old-toolchain numeric polyfills |
| `ptr::copy_nonoverlapping` | wrapper calls intrinsic `copy_nonoverlapping` | `TryFromBytes` candidate initialization; `util::copy_unchecked` | ordinary source |
| raw-pointer `copy_to` / `ptr::copy` | wrapper calls intrinsic `copy` | overlapping move in `FromZeros::insert_vec_zeroed` | `alloc` |
| raw-pointer `write_bytes` | wrapper calls intrinsic `write_bytes` | zero-fill of inserted vector slots | `alloc` |
| `ptr::read` | wrapper calls implementation intrinsic `read_via_copy` | `Ref::read`; `Unalign<T>` mutation helper | ordinary source |
| `ptr::write` | wrapper calls implementation intrinsic `write_via_move` | `Ref::write`; `Unalign<T>` write-back guard | ordinary source |
| `ptr::read_unaligned` | implemented through byte `copy_nonoverlapping` plus `MaybeUninit::assume_init` | fallible transmute support in `util::macro_util` | ordinary source; no distinct `read_unaligned` intrinsic at this pin |
| raw-pointer `add` / `offset` | pointer methods call intrinsic `offset` | `ByteSlice` splitting; `PtrInner` trailing-slice/subslice projections; vector insertion | ordinary source / `alloc` |
| raw-pointer `offset_from` / `byte_offset_from` | method calls intrinsic `ptr_offset_from` | field-offset derivation in macro support | ordinary source |
| `usize::unchecked_add/sub/mul` | pinned integer inherent methods are stable counterparts of intrinsic `unchecked_add/sub/mul` | cast-metadata arithmetic; DST padding calculation; slice-length subtraction | ordinary source on pinned nightly |
| `size_of` / `align_of` | intrinsic `size_of` / `align_of` | pervasive static layout checks and calculations | ordinary source |
| raw `size_of_val` / `align_of_val` family | intrinsic `size_of_val` / `align_of_val` beneath the raw APIs | layout/metadata machinery and Miri-only alignment promises | exact call-site configuration varies |
| raw-pointer metadata construction/extraction | `ptr::from_raw_parts{,_mut}` uses `aggregate_raw_ptr`; `ptr::metadata` uses `ptr_metadata` | raw slice construction and `KnownLayout` pointer metadata plumbing | ordinary source; trait-object metadata has separate semantic concerns |

Basis: source + derived.

The table matters more than the textual spelling of the zerocopy calls. At this pin, for example, `ptr::read` is documented in `core` as intentionally using an intrinsic so MIR sees a typed load directly; `ptr::write` similarly uses an intrinsic to keep the MIR operation as a move into the destination. A verifier that expands only handwritten zerocopy source but treats these wrappers as opaque library calls would therefore lose semantics that are explicit at the MIR/compiler boundary.

### `transmute` appears both as a runtime operation and as compile-time type checking

The exported `transmute!` macro calls the `core::mem::transmute` reexport directly. The macro's comments rely on the compiler's size check as "compiler magic" because a generic Rust function cannot express equality of arbitrary type sizes in the same way.

`try_transmute!` contains a different-looking use: it places `mem::transmute(e)` in an `if false` branch. That branch is never executed, but it is still type-checked, so the intrinsic's compile-time same-size requirement is part of the macro's implementation strategy. A translation model that reasons only about executed runtime calls can therefore miss a compile-time role that zerocopy intentionally depends on.

By contrast, `crate::util::transmute_unchecked<Src, Dst>` is a local helper with an unfortunate intrinsic-like name. It first statically checks equal sizes and then reads a different field of a `#[repr(C)]` union containing `ManuallyDrop<Src>` and `ManuallyDrop<Dst>`. It does not invoke `core::intrinsics::transmute_unchecked` at this revision.

Basis: source.

### Copying has three different compiler-facing forms in zerocopy

Zerocopy uses `copy_nonoverlapping` directly where the proof establishes disjoint regions. A central example is the `TryFromBytes` path: it copies all source bytes into a fresh `MaybeUninit<T>` candidate before validation, and its safety comment explicitly discharges the source-read, destination-write, alignment, and non-overlap obligations. `util::copy_unchecked` uses the same primitive for byte slices whose borrow structure establishes non-overlap.

The `alloc`-gated vector insertion path deliberately needs overlapping movement. It calls the raw pointer method `copy_to`, whose pinned `core` implementation delegates to `ptr::copy`, and then calls `write_bytes` to initialize the newly opened range to zero. These reach the `copy` and `write_bytes` intrinsics, respectively.

`read_unaligned` is a fourth source-level operation but not a fourth intrinsic. At this Rust revision, `core::ptr::read_unaligned` allocates a `MaybeUninit<T>`, copies `size_of::<T>()` bytes into it with `copy_nonoverlapping`, and then calls `assume_init`. Its presence in zerocopy therefore expands the conditions under which the copy intrinsic is relevant; it does not add a `read_unaligned` intrinsic to the compiler boundary.

Basis: source + derived.

### Typed loads and stores are explicit MIR-facing intrinsic operations

`Ref::read` ultimately performs `ptr::read` after its `ByteSlice` and `FromBytes` reasoning establishes that the bytes have the right size, alignment, and validity. At the pinned Rust revision, `ptr::read` calls `intrinsics::read_via_copy`. The `core` source explains why: the intrinsic lowers to a typed MIR load and preserves optimization-relevant type information that the earlier implementation via an untyped byte copy did not convey adequately.

`Ref::write` analogously calls `ptr::write`, whose pinned implementation calls `intrinsics::write_via_move`. The `Unalign<T>` mutation helper uses the same pair to make a temporary aligned copy and then write it back, including on unwind.

For Anneal, this is a semantic boundary rather than merely a code-generation detail. Charon or another MIR consumer can encounter operations whose source spelling is an ordinary stable library function but whose implementation deliberately exposes a typed MIR primitive.

Basis: source + derived.

### Pointer arithmetic reaches both address-offset and pointer-difference intrinsics

Zerocopy uses raw-pointer `add` while splitting byte slices and while projecting portions of its internal pointer representation. At the pinned Rust revision, both raw-pointer `add` and `offset` ultimately call the `offset` compiler intrinsic after their wrapper-level checks.

For differences, raw pointer `offset_from` calls `intrinsics::ptr_offset_from`, and `byte_offset_from` delegates to `offset_from` after casting both operands to byte pointers. Zerocopy's macro support uses `offset_from` when deriving a field's byte offset from a base pointer.

The source comments in zerocopy are significant: they explicitly prove same-allocation, in-bounds-or-one-past, and non-overflow conditions before these operations. Those obligations are not represented merely by the function name, so a later semantic report should preserve the primitive's exact contract independently of this inventory.

Basis: source + derived.

### Unchecked integer arithmetic is real on the pinned nightly; the local fallback is a different implementation

Zerocopy uses `unchecked_add`, `unchecked_sub`, and `unchecked_mul` to avoid redundant checked arithmetic after surrounding invariants establish that overflow or underflow is impossible. Examples include DST metadata conversion, trailing-slice size calculation, and source/remainder length calculations.

The pinned Rust `core` declares `unchecked_add`, `unchecked_sub`, and `unchecked_mul` as compiler intrinsics and describes the integer inherent methods as their stable counterparts. Zerocopy also defines a local `NumExt` compatibility trait with methods of the same names. Its own source notes that those implementations are polyfills for features already stabilized on the nightly toolchain and therefore are not tested on nightly. The fallback implementations use `checked_*` and route the impossible failure arm through `unreachable_unchecked`.

This produces two distinct verification paths:

1. on Anneal's pinned nightly, the inherent unchecked integer operations carry the direct unchecked-arithmetic contract;
2. on an older compiler configuration selecting the polyfill, zerocopy instead performs checked arithmetic and asserts the failure arm unreachable.

A source analysis that resolves method names without configuration can conflate these paths.

Basis: source + derived.

### Layout and raw-pointer metadata APIs add compiler intrinsics without requiring unsafe intrinsic syntax

At the pinned Rust revision, `size_of` and `align_of` are compiler intrinsics. Raw dynamic-size and alignment queries are backed by `size_of_val` and `align_of_val`. Zerocopy's layout machinery depends heavily on static size/alignment operations, and some raw dynamic queries appear in layout or Miri-specific paths.

Raw-pointer metadata is similar. `core::ptr::metadata` delegates to `ptr_metadata`; `core::ptr::from_raw_parts` and `from_raw_parts_mut` delegate to `aggregate_raw_ptr`. Zerocopy constructs raw slice pointers in its byte-slice and internal pointer machinery, so wide-pointer construction can reach this intrinsic-backed representation even though the public raw-slice constructor itself is safe.

These mappings should not be used as substitutes for the dedicated reports on layout or wide-pointer validity. In particular, the fact that pointer assembly is intrinsic-backed says nothing by itself about whether the resulting pointer may safely be dereferenced.

Basis: source + derived.

### Anneal must inventory wrappers and MIR, not spellings

The source evidence supports a narrow but important engineering rule: textual absence of `core::intrinsics` in zerocopy cannot establish that Charon/Aeneas never need intrinsic handling for zerocopy. Stable `core` APIs are part of the compiler boundary, and their lowering is version-sensitive.

A robust Anneal compatibility check should therefore distinguish three layers:

1. **zerocopy source surface** — which `core` operations zerocopy invokes under the selected feature/configuration set;
2. **pinned `core` lowering** — which of those wrappers become compiler intrinsics or special MIR operations at the selected Rust revision;
3. **Charon/Aeneas support** — how that exact MIR/intrinsic operation is represented, translated, modeled, rejected, or treated as opaque.

This report establishes layers 1 and 2 for the operations above. The Charon-intrinsics reference subject owns layer 3 and should remain a separate report because Charon's handling can change independently of zerocopy's source.

Basis: source + derived.

## Boundaries

**No compiled MIR or LLBC census was run.** The inventory follows exact source and exact `core` implementations. It therefore establishes source-level potential intrinsic reachability, not the exact set of intrinsic instances emitted after cfg expansion, monomorphization, MIR optimization, or Charon extraction.

**This is not an exhaustive census of every intrinsic rustc may synthesize.** Ordinary language constructs, primitive operations, compiler-generated glue, proc-macro expansion, or transitive dependencies can introduce additional compiler-internal operations. The report focuses on explicit zerocopy source calls whose pinned `core` implementation exposes an intrinsic-backed semantic boundary relevant to unsafe/layout verification.

**Feature reachability is not flattened.** `alloc` adds overlapping pointer copy and byte fill through vector insertion. Miri-only code adds some raw alignment observations. Compatibility polyfills change the implementation of unchecked integer arithmetic on older Rust releases. A consumer that needs one exact build must apply that build's cfg and feature set.

**Primitive semantics are not re-proved here.** The table records wrapper-to-intrinsic relationships. It does not establish that every zerocopy call satisfies the primitive's safety preconditions; zerocopy's local safety arguments and the dedicated reference reports remain necessary evidence for those questions.

**FFI is excluded.** The adjacent `FFI primitives used by zerocopy` inventory item is a separate boundary. This report does not infer FFI coverage from intrinsic coverage.

**`transmute_unchecked` names are ambiguous.** The local zerocopy helper is established to be union-based at this revision. This report does not claim that some future revision or generated dependency code cannot call the compiler's `transmute_unchecked` intrinsic.

## Evidence

All source observations below were acquired on 2026-09-27.

### zerocopy source

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `zerocopy/src/macros.rs`, blob `2b5a66929f544a60cede7194c3f82260a1b9e8e3`, lines 60-210 and 610-665: exported `transmute!` and `try_transmute!` use `core::mem::transmute`, including the dead type-checking branch.
- Same revision, `zerocopy/src/util/mod.rs`, blob `50454af00ccff8b0b58684fb3f048f955d4650c6`, lines 270-390: `copy_unchecked`, local union-based `transmute_unchecked`, and reference transmute helpers; lines 425-455: ZST dangling-pointer `mem::transmute`; lines 565-595: unchecked size arithmetic; lines 721-800: compatibility `NumExt` methods and the explicit note that the polyfills are not used on the pinned nightly.
- Same revision, `zerocopy/src/lib.rs`, blob `944f177c0b0bf66ebd136e5f21ae1b4c2bde48b5`, lines 3535-3590: `TryFromBytes` candidate initialization via `copy_nonoverlapping`; lines 3990-4080: `alloc`-gated overlapping `copy_to` and `write_bytes`; lines 5415-5580: `unreachable_unchecked` in impossible unaligned `FromBytes` branches; lines 6020-6115: byte-slice construction from raw parts.
- Same revision, `zerocopy/src/ref.rs`, blob `dd0816327ba2532e4f92cdad5266f38c5de9eb54`, lines 360-395: unchecked subtraction after a size proof; lines 750-805: `ptr::read` and `ptr::write`.
- Same revision, `zerocopy/src/wrappers.rs`, blob `2d4ff5515918a8e486683d1863289e4105da3022`, lines 230-260: reference conversion via `mem::transmute`; lines 350-400: typed `ptr::read`/`ptr::write` write-back guard.
- Same revision, `zerocopy/src/util/macro_util.rs`, blob `f374a089f414614ea81764ae1ee078af05d27109`, lines 536-585: `read_unaligned`; lines 760-795: reference transmute helper; this file also computes field byte offsets with `offset_from` around line 213.
- Same revision, `zerocopy/src/byte_slice.rs`, blob `3b70ecc2481a05e01fad69c027932fc9481306e6`, lines 245-310: pointer `add`, unchecked length subtraction, and raw mutable-slice construction.
- Same revision, `zerocopy/src/pointer/inner.rs`, blob `023df07d045243e0a2924de1d4db2826d2770bb4`, lines 340-425: provenance-preserving `add`, unchecked length subtraction, and raw-slice pointer assembly.
- Same revision, `zerocopy/src/pointer/mod.rs`, blob `03b17bf0786e46d74ba957f36c6013e28ca6806d`, lines 365-400: impossible size branch via `unreachable_unchecked` and raw-byte-slice pointer assembly.
- Same revision, `zerocopy/src/layout.rs`, blob `d58786d637cf8fb94cde85ed7a3549448561ff60`, lines 1025-1070: unchecked metadata arithmetic.
- Same revision, `zerocopy/src/error.rs`, blob `afdbc038291633afae5f90a29066f753229d366e`, lines 345-375: conversion of an impossible `AlignmentError<_, Unaligned>` via `unreachable_unchecked`.

### Rust core implementation

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `library/core/src/intrinsics/mod.rs`, blob `78d7314c58110b49839894a0f69377f4ee0d1204`:
  - lines 380-400: `unreachable`/`assume` intrinsic boundary;
  - lines 838-857: `transmute` and `transmute_unchecked` declarations;
  - lines 892-916: pointer `offset`/`arith_offset` declarations;
  - lines 1986-2011: unchecked add/sub/mul declarations;
  - lines 2200-2217: `read_via_copy` and `write_via_move`;
  - lines 2269-2278: pointer-difference intrinsics;
  - lines 2777-2800: static size/alignment intrinsics;
  - lines 2850-2874: raw dynamic size/alignment intrinsics;
  - lines 3002-3017: aggregate raw pointer and pointer metadata intrinsics;
  - lines 3019-3050: copy, overlapping copy, and byte-fill intrinsic declarations.
- Same revision, `library/core/src/mem/mod.rs`, blob `62c612e7ba2a65bb1645faaa669abd2a1d35a6c2`, lines 66-68: stable `mem::transmute` reexport of the intrinsic.
- Same revision, `library/core/src/hint.rs`, blob `90326e649058bee9f49c1e600a054f2805a3ab4f`, lines 101-113: `unreachable_unchecked` checks its contract and invokes `intrinsics::unreachable`.
- Same revision, `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2`, lines 430-552: `copy_nonoverlapping` contract and intrinsic call; lines 1690-1820: typed `read` via `read_via_copy` and unaligned read via byte copy; lines 1910-1935: typed `write` via `write_via_move`.
- Same revision, `library/core/src/ptr/const_ptr.rs`, blob `5cbbebf9f478819ee80e0c6486d622ae9ffdac00`, lines 340-405 and 820-885: `offset`/`add` wrappers call `intrinsics::offset`; lines 608-637: `offset_from` calls `ptr_offset_from`, and `byte_offset_from` delegates to it; lines 1222-1253: pointer copy methods delegate to `copy`/`copy_nonoverlapping`.
- Same revision, `library/core/src/ptr/mut_ptr.rs`, blob `53ef7f754d201a1dc08aa50a320266a8ab55245f`, lines 1314-1385: copy methods; lines 1427-1438: `write_bytes` wrapper.
- Same revision, `library/core/src/ptr/metadata.rs`, blob `1eeadf1217b5f94b48a33de62cd82ad47941890c`, lines 3-6 and 90-134: `ptr_metadata` and `aggregate_raw_ptr` implement metadata extraction and pointer assembly.

### Toolchain pin

- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `rust-toolchain`, blob `4e348edab20d6bd5b195e758afe20f9d8258a3e1`: channel `nightly-2026-05-31` with `rustc-dev`, `llvm-tools-preview`, `rust-src`, and `miri` components.

## Revalidation

For another zerocopy revision, first scan the production `zerocopy/src` tree for direct unstable intrinsic imports and for the source-facing operations named in `intrinsic-surface.json`. Record feature/cfg additions rather than flattening them into one reachability claim.

For another Rust toolchain, diff the narrow wrapper regions in `core` listed above. In particular, check whether `ptr::read`, `ptr::write`, `read_unaligned`, raw-pointer arithmetic, pointer metadata assembly, and unchecked integer methods still lower through the same intrinsic names. These implementation mappings are not language-level guarantees.

If an exact execution or translation set matters, strengthen this report with a build-derived probe rather than broadening the source claim: compile zerocopy with the target feature set and pinned compiler, inspect the resulting MIR or Charon LLBC for intrinsic/special-operation references, and preserve the command, cfg/features, item-selection rule, and resulting inventory. Compare that emitted set with this source-level table. A successful probe establishes only the selected build and reachable item set, not every zerocopy configuration.
