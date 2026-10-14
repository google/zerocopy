# Target, dynamic-layout and primitive contracts in MiniRust

## Summary

MiniRust separates mathematical integers from modeled bounded operations, and separates decoding a wide pointer from validating it against memory and metadata. Target, layout, pointee information and memory implementation are part of a theorem's subject. The allocation and intrinsic definitions expose useful unsafe leaves, but they do not verify the Rust library/runtime that would implement those leaves.

Finite mathematical probes discriminate 32/64-bit widths, both byte orders, raw versus safe wide-pointer checks, packed tails and allocation address reuse. They are independent reconstructions, not runs of MiniRust or cross-target Rust.

## Applicability

Directly examined MiniRust revision: `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`. The comparison uses Rust Reference `2dafab96d919d6ab2884488e970bf95610ff83eb` and Rust atomic documentation source `d8ef4f3fe7031514cbd7d056b7b058814987ecec`. The MiniRust example named `x86_64` is testing configuration evidence, not a certificate that it exactly models any named hardware/ABI target.

This report handles MR09/MR10 and the allocation/intrinsic parts of MR17. It does not prove representation laws (MR06), copy refinements (MR07), compiler layout extraction, or source-safety correspondence.

## Findings

### F1. Targets select bounded semantics and supplied layout facts

Basis: **source**, checked against **normative** layout guarantees.

`Target` supplies pointer size/alignment, maximum integer alignment, byte order, maximum atomic size and `valid_size`. Its introduction explicitly says program well-formedness depends on the target. The example uses 64-bit pointers, 8-byte pointer alignment, 16-byte maximum integer alignment, little endian, 8-byte maximum atomics and sizes fitting signed pointer width. [Target interface](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/prelude/target.md).

`Int` is mathematical, while `IntType` bounds results. Ordinary add/subtract/multiply are wrapped into the result type after mathematical evaluation; unchecked variants reject out-of-range results. Division/remainder reject zero and signed MIN/-1 overflow. Ordinary shifts reduce the count modulo bit width; unchecked shifts require a count in [0,width). Source checked-overflow/panic behavior must be represented by elaborated checks; the core Add rule alone does not specify the surface expression's panic behavior. `ThinPointer::wrapping_offset` wraps its address to unsigned pointer width and does not establish in-bounds authority. [Integer operators](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/step/operators.md#L183), [pointer arithmetic](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/pointer.md#L62).

The inspected `Type` enum has no float variant. This wave supplies no FP semantics or FP experiments. `MAX_ATOMIC_SIZE` is only a width bound; it does not encode operation-by-operation target availability. Rust documentation separately conditions atomics on target support, including targets with load/store but no CAS. A target certificate must therefore cover actual requested operations, not just maximum width. [Types](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/types.md#L21), [atomic portability](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/sync/atomic.rs#L115).

The Reference guarantees thin-pointer layout like usize and weaker minimum guarantees for DST pointers; the current two-word DST representation is expressly not a portable guarantee. It also permits platform-specific primitive alignment and compilation-dependent layout. MiniRust instead receives concrete field offsets, enum discriminators/taggers, sizes and alignments. Such supplied facts must be justified by the intended Rust layout guarantee or by an explicitly compiler/target-specific extraction certificate. [Reference layout](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/type-layout.md).

### F2. Metadata, dynamic layout and referent validity are distinct

Basis: **source** + **derived** consequences.

The metadata kind is None, element count or vtable pointer for a named trait. Counts must fit target usize. Vtable metadata must identify an allocated vtable for the expected trait. A safe pointer additionally requires dynamic total size at most isize::MAX, nonzero address, dynamic alignment, inhabited pointee and memory dereferenceability. Raw pointers skip those safe-pointee conditions, while still satisfying address/metadata checks. The validator explicitly does not inspect the data behind a safe pointer. A valid reference in this model is therefore not a recursive proof that its referent satisfies every Rust/library invariant. [Pointer checks](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/representation.md#L487).

| Layout case | Computation | Safety obligation beyond “two words” |
|---|---|---|
| Slice | count × element size; element alignment | usize count, safe total-size bound, allocation range, alignment |
| Zero-size elements | total size remains zero even for large valid counts | safe pointer still nonnull/aligned/inhabited; dereferenceability uses zero-size rule |
| Trait object | vtable size/alignment/cell locations; method table lookup | correct trait identity, valid vtable pointer and compatible selected function ABI |
| Unsized tail | recursively compute tail layout, cap tail alignment for packed layout, align head end, then round final size | correct head layout and metadata for the recursively selected tail |
| Recursive Rust type | pointer stores finite PointeeInfo rather than the whole recursive type | elaborator must faithfully provide inhabited/freeze/unpin/cell/layout facts |

[Dynamic layout](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/types.md#L200), [pointee descriptions](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/pointer.md#L90).

Enum representation explicitly supplies a discriminator decision tree and per-variant tag writes; it does not derive rustc's niche selection. MiniRust treats str as [u8], so this representation interface does not itself encode UTF-8 validity. Unsized values are accessed through places/pointers, not decoded as ordinary whole values. Retagging additionally computes dynamic per-byte UnsafeCell permissions, including vtable cell information; validating pointer metadata alone does not establish a mask's relation to compiler layout. [Types and enums](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/types.md#L48), [retag masks](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/reborrow_settings.md).

### F3. Finite target/layout probes

Basis: **execution** of owned formulas reconstructed from the above source.

`probe.py` runs four width/endianness families. Integer 0x01020304 encodes as [4,3,2,1] little endian and [1,2,3,4] big endian. Signed maximum plus one wraps to minimum; unchecked overflow fails; a regular shift by width acts as shift by zero, while the unchecked count fails. Address maximum plus two wraps to one.

The safe-slice predicate rejects count = 2^(width-1) for element size one while the raw-pointer predicate accepts the same metadata. A ZST slice with count usize::MAX passes the reconstructed size test at aligned nonnull address without an allocation. Valid metadata with a nonempty invalid data range fails, wrong-trait vtables fail, and zero-size safe pointers still fail when null or misaligned.

For a head ending at byte one and an eight-byte tail aligned to four, ordinary layout gives tail offset four, size twelve, align four; packed(1) gives offset one, size nine, align one. No packed Rust reference was created.

These outcomes test selected formulas only. The pointer probe abstracts allocation identity, exact vtable lookup and retagging to explicit premises. Wrong-trait rejection is a negative control for that premise, not execution of forged metadata.

### F4. Allocation and environment leaves need their own contracts

Basis: **source**, with **derived** import obligations.

BasicMemory uses demonic choice of a positive aligned base whose one-past end fits unsigned pointer width and which does not overlap a live allocation. IDs are fresh list indices; dead allocations remain recorded. Deallocation requires original allocation identity, live status, base address, allocation kind, size and alignment. Addresses may be reused after free; old provenance still selects the dead allocation. Its overlap rule also preserves unique base addresses for live zero-size allocations, a deliberate modeling choice not a blanket Rust guarantee. [Basic allocation](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/basic.md#L65).

The tiny 8-bit candidate-address probe excludes base four while a size-eight allocation at four is live, then permits it after deallocation. This checks numeric candidate selection only. It does not implement provenance freshness, nondeterministic quantifiers, allocator exhaustion or Rust allocator APIs.

The source explicitly flags exhausted allocation choice as “no behavior” rather than a satisfactory OOM model. Thus no allocation-failure contract follows from the current Allocate primitive. A theorem about Vec-like growth must state which failure/abort behavior is permitted and whether the implementation/runtime refines it.

| Leaf | What is directly defined | Remaining source/environment obligation |
|---|---|---|
| Allocate/Deallocate | Primitive memory operations with size/alignment checks | Bind allocator implementation, failure policy, ownership and reuse |
| Atomic loads/stores/RMW | Power-of-two size/alignment and maximum-size checks; SC flag | Actual target availability, source ordering and alias/race integration |
| RawEq | Raw memory loads and initialized-byte comparison | Preserve permitted padding/initialization/provenance observations |
| CopyNonOverlapping MIR statement | Explicit unsupported translator branch | Add a defined lowering and prove overlap, alignment and copy semantics |
| Unaligned read/write, overlapping copy, realloc | No direct dedicated primitive in inspected intrinsic enumeration | Inspect actual library/lowered paths; no support/absence verdict for all paths |
| Panic/FFI | Synthetic panic lowering; foreign calls rejected | Panic runtime/payload and ABI/environment relation |

[Intrinsic definitions](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/step/intrinsics.md), [copy statement rejection](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/bb.rs#L117), [foreign call rejection](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/bb.rs#L788).

## Boundaries

- **Established:** source parameter/check inventory and bounded reconstruction outcomes.
- **Not established:** target-parametric representation theorem, compiler layout correctness, all-target atomic support, allocator failure adequacy or a verified standard-library implementation.
- **Not examined:** every niche encoding, enum validity case, recursive DST shape, malformed-mask invariant, source unaligned/realloc path, foreign callbacks, FP model or physical access refinement.
- **Unknown:** full MiniRust agreement with normative Rust pointer validity; source TODOs and disputed policy questions remain distinct from implementation behavior.
- **Unsupported at the inspected translator branch:** MIR CopyNonOverlapping. No unsupported upstream code was executed.

## Evidence

Observed 2026-10-14. `source-evidence.json` preserves revision/blob identities, narrow excerpts and primary links. `probe.py` and `results.json` are portable support. Invocation: `python3 probe.py > results.json`, Python 3.9.6, exit 0. No cross-target compilation or upstream build occurred.

## Revalidation

First diff Target, integer operators, Type/layout and check_ptr together. Rerun the formulas after reviewing their correspondence; add negative controls before broadening a pointer/layout claim. Inspect generated layout and monomorphic intrinsic/language-item paths for the actual rustc/target. A general portability result needs quantification over valid Target/layout certificates, not a successful run on four sample families.

*Authored by an AI agent acting on joshlf's behalf.*
