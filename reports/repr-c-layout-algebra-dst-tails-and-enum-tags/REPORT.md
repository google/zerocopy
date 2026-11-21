# Formal Algebra of `#[repr(C)]` Structs, Unions, Target-Parameterized Enum Tags, and Flat Slice-Tailed DSTs

## Summary

This package (`Toy.Layout`) mechanizes in core Lean 4 (`leanprover/lean4:v4.34.1`, `Std` only, no Mathlib) an unbundled `Nat`-arithmetic model of `#[repr(C)]` struct, union, target-parameterized C-enum tag, `#[repr(C)]` / `#[repr(C, Int)]` versus `#[repr(Int)]` data-carrying enum, alignment-modifier (`packed(N)` and `align(N)`), and flat slice-tailed dynamically sized type (DST) layout calculations, together with 25 kernel-checked result cards, minimal-hypothesis tightness counterexamples, non-vacuity witnesses, and empirical cross-checks against pinned `rustc`.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Every formal theorem below is a statement about the `Toy.Layout` mathematical model (`Basis: execution (Lean kernel check)`); connecting any model statement to the Rust Reference, `rustc`, or `google/zerocopy` is a separate `Basis: derived (modeling bridge)` inference subject to the non-claims, Rust-universality qualifications, and scope limits documented in `## Boundaries` (which should be read first before applying any card downstream):

1. **`repr-c-struct-invariants` (`Toy.Layout.reprCStruct_invariants_of_align_pos`, `T0`):** For any modifier `m` whose packing bound (when `m = .packed p`) is positive and any field list `fields` whose fields all have positive alignment (`0 < f.align`), `reprCStruct m fields` satisfies the five layout invariants `OffsetsLengthMatch`, `OffsetsAligned`, `OrderedNonOverlapping`, `FieldsInBounds`, and `SizeMinimalAligned` (with `OffsetsMonotone` and `FieldsDisjoint` following via `Toy.Layout.orderedNonOverlapping_implies_monotone_and_disjoint`).
2. **`repr-c-struct-characterization` (`Toy.Layout.reprCStruct_eq_iff_of_align_pos`, `T1`):** Under the same positivity hypotheses (`∀ f ∈ fields, 0 < f.align` and `∀ p, m = .packed p → 0 < p`), a `StructLayout` `L` equals `reprCStruct m fields` if and only if `L` satisfies `OffsetsLengthMatch`, `OffsetsGreedyMinimal`, `EndOffsetExact`, `AlignIsMaxEffective`, and `SizeMinimalAligned`.
3. **`repr-c-struct-align-pow2-divides` (`Toy.Layout.reprCStruct_align_pow2_divides`, `T0`):** Whenever every field in `fields` has a power-of-two alignment and `m` satisfies `ModifierPow2 m`, `(reprCStruct m fields).align` is a power of two divisible by every field's effective (possibly `packed`-reduced) alignment `effFieldAlign m f.align`.
4. **`struct-invariants-mutually-independent` (`Toy.Layout.struct_invariants_mutually_independent`, `T1`):** On the concrete sample structs `sampleStructAsc = [⟨1, 1⟩, ⟨4, 4⟩]` and `sampleStructDesc = [⟨4, 4⟩, ⟨1, 1⟩]`, five variant layout algorithms each violate one of `OffsetsAligned`, `OffsetsMonotone`, `FieldsDisjoint`, `FieldsInBounds`, and `SizeMinimalAligned` while satisfying the other four together with `OffsetsLengthMatch`.
5. **`repr-c-packed-one-no-padding` (`Toy.Layout.reprCStruct_packed_one_no_padding`, `T0`):** For every field list `fields` (with no alignment hypotheses), `reprCStruct (.packed 1) fields` has no shallow padding (`AllBytesOccupied`), total `size` and `endOffset` equal to `totalFieldSize fields`, `align = 1`, and field `i` at offset `totalFieldSize (fields.take i)`.
6. **`repr-c-packed-align-le` (`Toy.Layout.reprCStruct_packed_align_le`, `T0`):** For every field list `fields` and packing bound `n : Nat`, `(reprCStruct (.packed n) fields).align` is bounded above both by `max 1 n` and by `(reprCStruct .none fields).align` (without implying size monotonicity for non-power-of-two alignments).
7. **`repr-c-packed-ge-fields-noop` (`Toy.Layout.reprCStruct_packed_ge_fields_noop`, `T0`):** Whenever `n` is at least every field's natural alignment (`∀ f ∈ fields, f.align ≤ n`), `reprCStruct (.packed n) fields = reprCStruct .none fields`.
8. **`repr-c-aligned-preserves-offsets` (`Toy.Layout.reprCStruct_aligned_preserves_offsets`, `T0`):** By construction of `reprCStruct`, `reprCStruct (.aligned n) fields` preserves the exact `offsets` and `endOffset` of `base = reprCStruct .none fields` while setting `align = max base.align n` and `size = alignUp base.endOffset (max base.align n)`.
9. **`repr-c-aligned-size-composition` (`Toy.Layout.reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2`, `T0`):** When every field in `fields` has a power-of-two alignment and `n` is a power of two, `(reprCStruct (.aligned n) fields).size` equals `alignUp (reprCStruct .none fields).size (max (reprCStruct .none fields).align n)`.
10. **`repr-c-no-padding-iff-size-eq-sum` (`Toy.Layout.reprCStruct_no_padding_iff_size_eq_sum`, `T1`):** For every modifier `m` and field list `fields`, `reprCStruct m fields` has no shallow padding (`AllBytesOccupied`) if and only if `(reprCStruct m fields).size = totalFieldSize fields`.
11. **`repr-c-homogeneous-no-padding-iff` (`Toy.Layout.reprCStruct_homogeneous_no_padding_iff_of_align_pos`, `T0`):** For any field layout `f` with positive alignment (`0 < f.align`), `(∀ k : Nat, AllBytesOccupied (List.replicate k f) (reprCStruct .none (List.replicate k f))) ↔ f.align ∣ f.size`: the homogeneous structs `reprCStruct .none (List.replicate k f)` have no shallow padding for all `k` simultaneously if and only if `f.align ∣ f.size` (the quantifier over `k` is inside the left-hand side; no per-`k` biconditional is claimed).
12. **`ce-heterogeneous-u8-u16-has-padding` (`Toy.Layout.ce_heterogeneous_u8_u16_has_padding`, `T0`):** Even when every field is individually well-formed (`AlignPow2 f ∧ SizeMultipleOfAlign f`), the heterogeneous `#[repr(C)]` struct `[⟨1, 1⟩, ⟨2, 2⟩]` (`[u8, u16]`) has inter-field padding (`size = 4 ≠ 3 = totalFieldSize`, and `[⟨2, 2⟩, ⟨1, 1⟩]` has trailing padding via `Toy.Layout.ce_heterogeneous_u16_u8_has_trailing_padding`).
13. **`repr-c-enum-geometry` (`Toy.Layout.reprCEnum_geometry_of_vars_pow2`, `T1`):** For any `tag : FieldLayout` (with no hypothesis on `tag`) and any `variants` whose variant fields all satisfy `AlignPow2`, `reprCEnum tag variants` satisfies `EnumSizeValid`, `EnumVariantsValid`, and the construction-matching shared-payload predicate `EnumSharedPayload`.
14. **`repr-int-enum-geometry` (`Toy.Layout.reprIntEnum_geometry_of_nonempty_align_pos`, `T1`):** For any `tag : FieldLayout` and any non-empty `variants` (`variants ≠ []`) whose variant fields all satisfy `AlignPos` (`0 < f.align`), `reprIntEnum tag variants` satisfies `EnumSizeValid`, `EnumVariantsValid`, and the construction-matching per-variant predicate `EnumPerVariantTagged`.
15. **`repr-c-enum-align-valid` (`Toy.Layout.reprCEnum_align_valid_of_pow2`, `T0`):** Whenever `tag` and every field of every variant in `variants` have power-of-two alignments, `reprCEnum tag variants` satisfies `EnumAlignValid` (power-of-two alignment divisible by `tag.align` and all variant field alignments).
16. **`repr-int-enum-align-eq-repr-c-enum` (`Toy.Layout.reprIntEnum_align_eq_reprCEnum_align_of_nonempty`, `T1`):** For any `tag : FieldLayout` and any non-empty `variants` (`variants ≠ []`, without needing power-of-two alignments), `(reprIntEnum tag variants).align = (reprCEnum tag variants).align`.
17. **`repr-int-enum-size-le-repr-c-enum-size` (`Toy.Layout.reprIntEnum_size_le_reprCEnum_size_of_pow2`, `T1`):** Whenever `tag` and every field of every variant in `variants` have power-of-two alignments, `(reprIntEnum tag variants).size ≤ (reprCEnum tag variants).size`.
18. **`ce-repr-c-enum-tag-sizing-targets` (`Toy.Layout.ce_reprCEnum_tag_sizing_divergence` and `Toy.Layout.ce_reprCEnum_tag_sizing_divergence_aligns`, `T0`):** Under `reprCEnumForTarget`, neither a pointer-sized tag (`usizeTag64`) nor a fixed 4-byte `c_int` tag (`cIntLayout32Bit`) matches across targets and discriminant ranges: on discriminants `[0, 1]` for `[[⟨1, 1⟩], []]`, `targetX86_64Linux` gives `(8, 4)` vs. `(16, 8)` for `usizeTag64`, while `targetThumbV7mNoneEabi` and `targetHexagonNoneElf` (`cEnumMinBytes = 1`) give `(2, 1)` vs. `(8, 4)` for `cIntLayout32Bit`; and on discriminants `[0x1_0000_0000, 0x1_0000_0001]` (which do not fit in 32 bits) for `[[], []]`, `targetX86_64Linux` gives `(8, 8)` vs. `(4, 4)` for `cIntLayout32Bit` (with sizes and five alignments in `ce_reprCEnum_tag_sizing_divergence` and the remaining three alignments in `ce_reprCEnum_tag_sizing_divergence_aligns`). How the Rust Reference and `rustc` treat such discriminants is stated separately, with its basis, in the card.
19. **`ce-repr-int-strictly-smaller-than-repr-c-u8` (`Toy.Layout.ce_reprIntEnum_lt_reprCEnum_u8`, `T0`):** On `variants = [[⟨1, 1⟩, ⟨2, 2⟩], []]` with `u8Tag`, `reprIntEnum` yields `size = 4` and offsets `[[1, 2], []]` whereas `reprCEnum` yields `size = 6` and offsets `[[2, 4], []]`, and each of `EnumSharedPayload` and `EnumPerVariantTagged` rejects the opposite representation's layout.
20. **`dst-instantiated-eq-closed-form` (`Toy.Layout.dstInstantiated_eq_closed_form`, `T0`):** For every flat `SliceDstSpec` `d` and element count `n : Nat`, instantiating the trailing slice as a fixed-length field `⟨n * d.elem.size, d.elem.align⟩` produces `align = dstAlign d`, `size = dstSize d n`, and `offsets = (placeFields d.modifier 0 d.headFields).1 ++ [dstTailOffset d]`.
21. **`max-slice-elems-some-iff` (`Toy.Layout.maxSliceElems_some_iff`, `T1`):** For every flat `SliceDstSpec` `d` and `bufferLen n : Nat`, `maxSliceElems d bufferLen = some n` holds if and only if `n` is the greatest natural number satisfying `dstSize d n ≤ bufferLen` (`IsMaxFittingElems d bufferLen n`).
22. **`max-slice-elems-none-iff` (`Toy.Layout.maxSliceElems_none_iff_of_elem_size_pos`, `T1`):** Whenever `0 < d.elem.size`, `maxSliceElems d bufferLen = none` holds if and only if no element count `n : Nat` fits in `bufferLen` (`∀ n, bufferLen < dstSize d n`).
23. **`zst-tail-no-max-fitting-elems` (`Toy.Layout.zst_tail_no_max_fitting_elems`, `T1`):** Over unbounded `Nat` metadata, if `d.elem.size = 0`, then for every `bufferLen : Nat` no `n : Nat` satisfies `IsMaxFittingElems d bufferLen n` (whereas over any bounded metadata domain `[0, B]`, `B` fits whenever `n = 0` fits by `Toy.Layout.zst_tail_bounded_max_exists`).
24. **`dst-no-trailing-padding-all-iff` (`Toy.Layout.dst_no_trailing_padding_all_iff`, `T1`):** For every flat `SliceDstSpec` `d`, trailing padding `dstTrailingPadding d n` equals `0` for all `n : Nat` if and only if `dstAlign d` divides both `dstTailOffset d` and `d.elem.size`.
25. **`ce-dst-trailing-padding-breaks-naive-prefix-cast` (`Toy.Layout.ce_dst_trailing_padding_breaks_naive_prefix_cast`, `T1`):** There exist flat `SliceDstSpec`s `d` with `¬ (dstAlign d ∣ dstTailOffset d ∧ dstAlign d ∣ d.elem.size)` for which trailing padding makes naive `(bufferLen - dstTailOffset d) / d.elem.size` over-estimate `maxSliceElems`, or makes the naive check `dstTailOffset d ≤ bufferLen` accept a buffer for which `maxSliceElems = none`. The theorem proves three concrete instances, one per failure cause: `¬ (dstAlign d ∣ d.elem.size)` alone, both divisibilities failing, and `¬ (dstAlign d ∣ dstTailOffset d)` alone. It does not claim that every such `d` exhibits either effect.

See `## Boundaries` first for package-wide non-claims, modeling-bridge limitations, Rust-universal hypothesis caveats, and proved escape-hatch regimes.

## Applicability

### Model Fidelity and Real-System Scope

`Toy.Layout` (in `lean/Toy/Layout/{Core,Struct,Enum,Dst,CrossCheck}.lean`) is a self-contained mathematical model written in core Lean 4 (`leanprover/lean4:v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`) using only core Lean and `Std`, with **no Mathlib** and no external Lake `[[require]]` dependencies. Rather than importing compiler internals or bundling validity proofs inside dependent types, `Toy.Layout` represents field layouts as plain pairs `(size : Nat, align : Nat)` (`FieldLayout`) over unbounded natural numbers and separates each layout algorithm from its declarative correctness and characterization predicates.

The four core modules are designed to model the following real-system specifications and implementations:

- **`Toy.Layout.Core` and `Toy.Layout.Struct`** model the greedy sequential field-placement, effective-alignment, and trailing-rounding rules of `#[repr(C)]` structs with optional `#[repr(packed(N))]` or `#[repr(align(N))]` modifiers in the Rust Reference (`r[layout.repr.c.struct]`, `r[layout.repr.alignment]`), CompCert's composite C struct offset/alignment mechanization (`cfrontend/Ctypes.v`), `rustc_abi`'s `univariant_biased` / `layout_of_univariant_biased` struct calculator, and the shallow zero-padding sum check `size_of::<T>() == Σ size_of::<F_i>()` used by `google/zerocopy` (`struct_padding!`) and `Lokathor/bytemuck` (`generate_assert_no_padding`).
- **`Toy.Layout.Enum`** models `#[repr(C)]` unions (`reprCUnion`, `r[layout.repr.c.union]`), target-parameterized bare `#[repr(C)]` enum tag sizing (`CEnumTarget`, `minFittingIntBytes`, `cEnumTagBytes`, `cEnumTagLayout`, modeling `rustc`'s `discr_range_of_repr` and `TargetDataLayout::c_enum_min_size`), `#[repr(C)]` / `#[repr(C, Int)]` data-carrying enums as `struct { tag, union { variants } }` (`reprCEnum`, `r[layout.repr.c.adt]`, `r[layout.repr.primitive-c]`, RFC 2195), and `#[repr(Int)]` data-carrying enums as `union { struct { tag, fields_v } | v ∈ variants }` (`reprIntEnum`, `r[layout.repr.primitive.adt]`, RFC 2195).
- **`Toy.Layout.Dst`** models flat `#[repr(C)]` slice-tailed dynamically sized types (`struct S { head_1, ..., head_k, tail: [T] }` with optional struct-level `packed(N)` or `align(N)`) under the per-value instantiation reading (`dstInstantiated`, `dstSize`) shared by MiniRust (`TupleHeadLayout::full_size_and_align`) and `google/zerocopy` (`DstLayout::extend` / `pad_to_align` and test model `size_for_metadata_model`), together with prefix-cast maximum fitting slice element calculation (`maxSliceElems`) and dynamic trailing-padding vanishing (`dstTrailingPadding`).

### Rust-Universal Hypotheses in the Toy `Nat` Domain

Because `FieldLayout`, `ReprModifier`, and variant lists are unbundled over arbitrary `Nat` values and arbitrary `List` inputs, `Toy.Layout` states each theorem under the weakest mathematical precondition required in `Nat` rather than bundling Rust's type-system invariants into every input. Two classes of hypotheses in this package are **tight in the formal `Toy.Layout` model** yet **satisfied by every valid Rust type or enum** to which the corresponding representation applies. Each item states its basis.

1. **Alignment positivity, power-of-two alignments, and size divisibility (`AlignPos`, `ModifierPackPos`, `AlignPow2`, `ModifierPow2`, `IsPowerOfTwo`, `SizeMultipleOfAlign`).** `Basis: normative + derived (modeling bridge)`. The Reference states that an alignment "must be at least 1, and always a power of 2" (`r[layout.properties.align]`, line 19) and that "The size of a value is always a multiple of its alignment." (`r[layout.properties.size]`, line 22); it also requires the argument of `#[repr(align(x))]` and `#[repr(packed(x))]` to be a power of two from 1 up to 2^29 (`r[layout.repr.alignment.constraint-alignment]`, lines 638–639, paraphrased). Derived conclusion: the `(size, align)` pair of every Rust type and every `align`/`packed` argument satisfy these hypotheses. Their kernel-checked tightness counterexamples (using alignments `0`, `3`, or `6`, or packing argument `0`) pinpoint where modular divisibility or `max = lcm` breaks in `Nat`, and do **not** exhibit any valid Rust type for which the conclusion fails.
2. **Non-empty variant lists (`h_nonempty : variants ≠ []` on Cards 14 and 16, and the empty-variants transfer caveat on Card 15).** `Basis: normative + execution + derived (modeling bridge)`. The Reference states for the `C` representation: "This representation can be applied to structs, unions, and enums. The exception is [zero-variant enums] for which the `C` representation is an error." (`r[layout.repr.c.constraint]`, `src/type-layout.md` line 238), and for primitive representations: "It is an error for [zero-variant enums] to have a primitive representation." (`r[layout.repr.primitive.constraint]`, line 508). Execution: `support/e0084_zero_variant_enums.rs` declares zero-variant enums with `#[repr(C)]`, `#[repr(u8)]`, `#[repr(i32)]`, and `#[repr(usize)]`; compiling it fails with one error `E0084` (`unsupported representation for zero-variant enum`) per enum on both `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` (`support/e0084_zero_variant_enums_output.txt`). Derived conclusion: the `variants = []` tightness counterexamples (`ce_reprIntEnum_geometry_drop_nonempty`, `ce_reprIntEnum_align_eq_drop_nonempty`) test boundary behavior of the mathematical `reprIntEnum` / `reprCEnum` definitions and exhibit no valid Rust enum.

### Known Model Gaps

Connecting `Toy.Layout` theorems to real Rust systems (`Basis: derived (modeling bridge)`) applies only within the modeled fragment and is bounded by the following explicit abstractions:

1. **Unbounded `Nat` arithmetic vs. finite machine words:** `Toy.Layout` performs arithmetic in `Nat` without `usize::MAX`, `isize::MAX`, or `TargetDataLayout::obj_size_bound` overflow checks. `Basis: source`: in `rustc_abi` at `14210df0e`, struct layout computation returns `LayoutCalculatorError::SizeOverflow` when the size is at least `dl.obj_size_bound()` (`compiler/rustc_abi/src/layout.rs` lines 1322–1323), an exclusive bound of `1 << 15`, `1 << 31`, or `1 << 61` bytes for 16-, 32-, or 64-bit pointers (`compiler/rustc_abi/src/lib.rs` lines 608–615). Rust slice metadata `n` is a `usize`, so it is bounded by `usize::MAX` (which defeats the unbounded-`Nat` ZST-tail impossibility of Card 23; see `Toy.Layout.zst_tail_bounded_max_exists`).
2. **Unit base aggregate alignment (`aggregate_align = 1`):** `fieldsMaxAlign` folds `max` starting from `1`, matching targets whose `TargetDataLayout::aggregate_align` is `1` byte. `Basis: source` (`rust-lang/rust` at `14210df0e`): the default `aggregate_align` is `align(8)` bits, i.e. 1 byte (`compiler/rustc_abi/src/lib.rs` line 311); the data-layout strings of `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu` have no `a` component, while those of `thumbv7m-none-eabi` (`a:0:32`) and `hexagon-unknown-none-elf` (`a:0`) give an ABI alignment of 0, which `Align::from_bytes` treats as 1 byte (`compiler/rustc_target/src/spec/targets/*.rs`; `compiler/rustc_abi/src/lib.rs` lines 1079–1083). The starting alignment of an unpacked struct is `dl.aggregate_align`, and that of a `packed` struct is `dl.i8_align`: `let mut align = if pack.is_some() { dl.i8_align } else { dl.aggregate_align };` (`compiler/rustc_abi/src/layout.rs` line 1108). Targets with `dl.aggregate_align > 1` are not modeled.
3. **Opaque shallow fields (`FieldLayout`):** Each field is modeled solely by its `(size, align)` pair. Struct-padding predicates (`AllBytesOccupied`, `totalFieldSize`) detect shallow inter-field and trailing padding of the enclosing struct only, not padding nested inside composite field types (`r[layout.repr.alignment.intro]`).
4. **Modifier and representation exclusions:** `Toy.Layout` models mutually exclusive struct-level `.none`, `.packed n`, and `.aligned n`. `Basis: normative`: "The `align` and `packed` modifiers cannot be applied on the same type and a `packed` type cannot transitively contain another `align`ed type." (`r[layout.repr.alignment.constraint-exclusive]`, line 654); this package did not probe how `rustc` enforces it. `Basis: documentation`: `google/zerocopy` records that "while Rust accepts an instantiation which transitively places a `repr(align)` type inside a `repr(packed)` type, that instantiation follows the otherwise-applicable `repr(C)`, `repr(packed)`, and inner-type layout rules" (`DstLayout::for_repr_c_struct` documentation, `zerocopy/src/layout.rs` lines 1136–1139 at `ec133ce4`). It does **not** model `#[repr(C, align(N))]` on enums, `packed`/`align` modifiers on unions, `#[repr(transparent)]`, `#[repr(Rust)]` field reordering or niche-filling enum optimizations, or function-call register-passing ABIs (`FnAbi`).
5. **Flat slice-tailed DSTs only:** `SliceDstSpec` models a single `#[repr(C)]` struct whose last field is `[T]`. It does **not** model nested DSTs (a last field that is itself a slice-tailed struct), such as the case described in `google/zerocopy`'s internal `TrailingSliceLayout` documentation: "a `repr(packed(2))` wrapper around a DST with alignment 4 can have an object alignment of 2 and a rounding alignment of 4" (`zerocopy/src/layout.rs` lines 199–201 at `ec133ce4`). Nor does it model trait-object (`dyn Trait`) vtable DSTs, address-alignment checks, suffix casts, or Rust's drop-glue restriction on generic `?Sized` tails inside `#[repr(packed)]` structs. For flat DSTs, the exact correspondence between the model and `zerocopy`'s normal form `(size_base, size_align, size_phase)` is stated under Card 21.

### Relationship Among Examined Subjects and Toolchain

`REPORT.json` records nine durable upstream subjects whose specifications, source implementations, mechanizations, or toolchains are directly examined in this package:

1. **Lean 4 toolchain (`leanprover/lean4`, release `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`):** executes and kernel-checks the `Toy` Lake library and audit scripts.
2. **The Rust Reference (`rust-lang/reference`, commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`):** normative specification for `#[repr(C)]` structs, unions, field-less and data-carrying enums, `#[repr(Int)]` / `#[repr(C, Int)]` enums, arrays/slices, and `packed(N)` / `align(N)` modifiers.
3. **Rust RFC 2195 (`rust-lang/rfcs`, commit `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, `text/2195-really-tagged-unions.md`):** primary design specification defining `#[repr(Int)]`, `#[repr(C, Int)]`, bare `#[repr(C)]` data-carrying enums, the `TwoCases` 4-byte vs. 6-byte separation example (Card 19), and the space-usage ordering mechanized in Card 17.
4. **`rustc` executed compiler and layout source (`rust-lang/rust`, `1.98.0-nightly`, commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, 2026-05-31):** primary `rustc` revision used both for source inspection (`rustc_abi`, `rustc_middle`, `rustc_target`, `rustc_const_eval`, `rustc_lint_defs`) and for executing the 31 cross-check probes across `x86_64-unknown-linux-gnu`, `thumbv7m-none-eabi`, and `hexagon-unknown-none-elf`.
5. **`rustc` refactored enum-layout source (`rust-lang/rust`, commit `4b5350e87e487aed08ab2f9f0160a4b2616438bc`):** a later `rustc` revision in which enum layout lives in `compiler/rustc_abi/src/layout/enum_layout.rs` (`calculate_tagged_layout`) rather than `compiler/rustc_abi/src/layout.rs`. It is cited only for source coordinates of the code regions cited at `14210df0e` (`Basis: source`). No probe was executed at this revision, and this package makes no claim about whether the move changed layout behavior.
6. **CompCert (`AbsInt/CompCert`, commit `2685140bf72c959446981fb99b5e44a8975021bc`, `cfrontend/Ctypes.v`):** prior Coq mechanization of C composite struct field alignment, range, and disjunctive non-overlap invariants (Cards 1 and 3).
7. **`google/zerocopy` (`google/zerocopy`, commit `ec133ce4d7993775413d852f91c9e3eb2a2a0897`, `zerocopy/src/layout.rs` and `zerocopy/src/util/macro_util.rs`):** production Rust implementation and Kani-verified bit-precise contracts for DST prefix-cast metadata calculation (`DstLayout`, `TrailingSliceLayout`, `validate_cast_and_convert_metadata`, `requires_dynamic_padding`) and `struct_padding!` (Cards 9, 10, 20–25).
8. **`Lokathor/bytemuck` (`Lokathor/bytemuck`, commit `ea3616110b0134e9991fdb66be8892dbc427c5ac`, `derive/src/traits.rs`):** proc-macro `NoUninit` assertion `generate_assert_no_padding` checking `size_of::<T>() == Σ size_of::<field>()` (Card 10).
9. **MiniRust (`minirust/minirust`, commit `063d784186d3252bee242217f218223205c0b568`, `spec/lang/types.md`):** operational semantics specification of `TupleHeadLayout::{tail_offset, full_size_and_align}` for slice-tailed tuple/struct layouts (Card 20).

Per `FORMAT.md`, unmerged pull requests and issue-tracker items are excluded from `REPORT.json` `subjects` and cited only as self-contained prose context: specifically, the unmerged Aeneas layout prototype `AeneasVerif/aeneas#1447` (fork `JoJoDeveloping/aeneas`, commit `2a1dd75567517e078f90b1df746af7373fe24cbc`, `backends/lean/Aeneas/Data/Layout/{ReprC,Properties}.lean`, whose pointer-sized default `reprC_default_tag_ty := .unsigned .Usize` motivates Card 18's pointer-sized tag counterexample) and `rustc` future-incompatibility tracking issue `rust-lang/rust#124403` (`repr_c_enums_larger_than_int`). Methodological inspiration from `rust-lang/rust-bindgen` (`e9a5f1fc501b55c3f7392a09ba8cd2a1041f7a33`) is noted solely under `## Evidence` cross-check design.

## Findings

### Core Definitions and Kernel-Checked Examples

Every core definition in `Toy.Layout` is accompanied in the Lean source by kernel-checked positive examples (`ex_*_pos*`) that it admits and negative examples (`ex_*_neg*`) that it rejects (`Basis: execution (Lean kernel check)`).

#### Arithmetic, Alignment, and Modifiers (`Toy.Layout.Core`)

```lean
def IsPowerOfTwo (a : Nat) : Prop :=
  ∃ k : Nat, a = 2 ^ k

def paddingNeeded (n a : Nat) : Nat :=
  if a = 0 then 0
  else
    let r := n % a
    if r = 0 then 0 else a - r

def alignUp (n a : Nat) : Nat :=
  n + paddingNeeded n a

def roundDown (x a : Nat) : Nat :=
  if a = 0 then 0 else (x / a) * a

def IsLeastMultipleGe (x n a : Nat) : Prop :=
  n ≤ x ∧ a ∣ x ∧ ∀ m : Nat, n ≤ m → a ∣ m → x ≤ m

structure FieldLayout where
  size : Nat
  align : Nat

def AlignPos (f : FieldLayout) : Prop :=
  0 < f.align

def AlignPow2 (f : FieldLayout) : Prop :=
  IsPowerOfTwo f.align

def SizeMultipleOfAlign (f : FieldLayout) : Prop :=
  f.align ∣ f.size

inductive ReprModifier where
  | none
  | packed (n : Nat)
  | aligned (n : Nat)

def ModifierPackPos (m : ReprModifier) : Prop :=
  ∀ p : Nat, m = .packed p → 0 < p

def ModifierPow2 : ReprModifier → Prop
  | .none => True
  | .packed n => IsPowerOfTwo n
  | .aligned n => IsPowerOfTwo n

def effFieldAlign (m : ReprModifier) (a : Nat) : Nat :=
  match m with
  | .packed p => min a p
  | .none | .aligned _ => a
```

- **`IsPowerOfTwo`:** Captures power-of-two byte alignments (`1, 2, 4, 8, ...`), under which `max` over alignments coincides with `lcm`. Positive: `ex_isPowerOfTwo_pos_1` (`1`), `ex_isPowerOfTwo_pos_4` (`4`), `ex_isPowerOfTwo_pos_8` (`8`). Negative: `ex_isPowerOfTwo_neg_0` (`0`), `ex_isPowerOfTwo_neg_3` (`3`), `ex_isPowerOfTwo_neg_6` (`6`).
- **`paddingNeeded` and `alignUp`:** Capture the Rust Reference's modular upward cursor rounding to the next multiple of `a` (totalized to a no-op at `a = 0` so definitions avoid proof obligations). Positive: `ex_paddingNeeded_pos` (`paddingNeeded 5 4 = 3`), `ex_paddingNeeded_zero` (`paddingNeeded 8 4 = 0`), `ex_alignUp_pos_unaligned` (`alignUp 5 4 = 8`), `ex_alignUp_pos_aligned` (`alignUp 8 4 = 8`), and `alignUp_zero` (`alignUp 0 a = 0`). Negative: `ex_paddingNeeded_neg` (`paddingNeeded 5 4 ≠ 0`), `ex_alignUp_neg` (`alignUp 5 4 ≠ 5`).
- **`roundDown`:** Captures largest-multiple-at-most rounding `(x / a) * a` used to strip trailing struct alignment slack from a byte buffer before slicing. Positive: `ex_roundDown_pos` (`roundDown 7 4 = 4`). Negative: `ex_roundDown_neg` (`roundDown 7 4 ≠ 7`).
- **`IsLeastMultipleGe`:** Declarative specification of minimal upward alignment rounding (`n ≤ x`, `a ∣ x`, and minimal among all multiples of `a` at least `n`), independent of the `%`-based implementation of `alignUp`. Positive: `ex_isLeastMultipleGe_pos` (`(8, 5, 4)`). Negative: `ex_isLeastMultipleGe_neg_not_minimal` (`(12, 5, 4)`), `ex_isLeastMultipleGe_neg_not_multiple` (`(5, 5, 4)`).
- **`FieldLayout`, `AlignPos`, `AlignPow2`, `SizeMultipleOfAlign`:** Unbundled `(size, align)` pair and its three decoupled well-formedness properties (`0 < f.align`, `IsPowerOfTwo f.align`, `f.align ∣ f.size`). Positive: `ex_alignPos_pos`, `ex_alignPow2_pos`, `ex_sizeMultipleOfAlign_pos`. Negative: `ex_alignPos_neg` (`⟨4, 0⟩`), `ex_alignPow2_neg` (`⟨3, 3⟩`), `ex_sizeMultipleOfAlign_neg` (`⟨3, 2⟩`).
- **`ReprModifier`, `ModifierPackPos`, `ModifierPow2`, `effFieldAlign`:** Optional struct-level `packed(n)` or `aligned(n)` modifier (`r[layout.repr.alignment]`), its positivity/power-of-two predicates, and per-field effective alignment (`min a p` under `.packed p`, `a` otherwise). Positive: `ex_modifierPackPos_pos_none`, `ex_modifierPackPos_pos_packed`, `ex_modifierPow2_pos_aligned`, `ex_effFieldAlign_pos_packed` (`effFieldAlign (.packed 2) 8 = 2`), `ex_effFieldAlign_pos_aligned` (`effFieldAlign (.aligned 16) 4 = 4`). Negative: `ex_modifierPackPos_neg_packed0`, `ex_modifierPow2_neg_aligned`, `ex_modifierPow2_neg_packed`, `ex_effFieldAlign_neg_packed_unchanged`.

#### Struct Layout, Soundness Predicates, and Declarative Characterization (`Toy.Layout.Struct`)

```lean
structure StructLayout where
  offsets : List Nat
  endOffset : Nat
  size : Nat
  align : Nat

def placeFields (m : ReprModifier) (cursor : Nat) : List FieldLayout → List Nat × Nat
  | [] => ([], cursor)
  | f :: fs =>
    let off := alignUp cursor (effFieldAlign m f.align)
    let (restOffs, endOff) := placeFields m (off + f.size) fs
    (off :: restOffs, endOff)

def fieldsMaxAlign (m : ReprModifier) (fields : List FieldLayout) : Nat :=
  fields.foldl (fun acc f => max acc (effFieldAlign m f.align)) 1

def structAlign (m : ReprModifier) (fields : List FieldLayout) : Nat :=
  match m with
  | .aligned n => max (fieldsMaxAlign m fields) n
  | .none | .packed _ => fieldsMaxAlign m fields

def reprCStruct (m : ReprModifier) (fields : List FieldLayout) : StructLayout :=
  let (offs, endOff) := placeFields m 0 fields
  let a := structAlign m fields
  { offsets := offs
    endOffset := endOff
    size := alignUp endOff a
    align := a }

def totalFieldSize : List FieldLayout → Nat
  | [] => 0
  | f :: fs => f.size + totalFieldSize fs

def OffsetsLengthMatch (fields : List FieldLayout) (L : StructLayout) : Prop :=
  L.offsets.length = fields.length

def OffsetsAligned (m : ReprModifier) (fields : List FieldLayout) (L : StructLayout) : Prop :=
  ∀ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
    effFieldAlign m fields[i].align ∣ L.offsets[i]

def OffsetsMonotone (L : StructLayout) : Prop :=
  ∀ (i j : Nat) (hi : i < L.offsets.length) (hj : j < L.offsets.length),
    i ≤ j → L.offsets[i] ≤ L.offsets[j]

def FieldsDisjoint (fields : List FieldLayout) (L : StructLayout) : Prop :=
  ∀ (i j : Nat) (hi : i < fields.length) (hj : j < fields.length)
    (hoi : i < L.offsets.length) (hoj : j < L.offsets.length),
    i ≠ j →
      L.offsets[i] + fields[i].size ≤ L.offsets[j] ∨
      L.offsets[j] + fields[j].size ≤ L.offsets[i]

def OrderedNonOverlapping (fields : List FieldLayout) (L : StructLayout) : Prop :=
  ∀ (i j : Nat) (hi : i < fields.length) (hj : j < fields.length)
    (hoi : i < L.offsets.length) (hoj : j < L.offsets.length),
    i < j → L.offsets[i] + fields[i].size ≤ L.offsets[j]

def FieldsInBounds (fields : List FieldLayout) (L : StructLayout) : Prop :=
  ∀ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
    L.offsets[i] + fields[i].size ≤ L.endOffset

def SizeMinimalAligned (L : StructLayout) : Prop :=
  IsLeastMultipleGe L.size L.endOffset L.align

def OffsetsGreedyMinimal (m : ReprModifier) (fields : List FieldLayout) (L : StructLayout) : Prop :=
  (∀ (hf : 0 < fields.length) (ho : 0 < L.offsets.length),
    IsLeastMultipleGe L.offsets[0] 0 (effFieldAlign m fields[0].align)) ∧
  ∀ (i : Nat) (hf : i + 1 < fields.length) (ho : i + 1 < L.offsets.length),
    IsLeastMultipleGe L.offsets[i + 1]
      (L.offsets[i]'(Nat.lt_of_succ_lt ho) + fields[i].size)
      (effFieldAlign m fields[i + 1].align)

def EndOffsetExact (fields : List FieldLayout) (L : StructLayout) : Prop :=
  match fields.getLast?, L.offsets.getLast? with
  | none, _ => L.endOffset = 0
  | some f, some o => L.endOffset = o + f.size
  | some _, none => False

def AlignIsMaxEffective (m : ReprModifier) (fields : List FieldLayout) (L : StructLayout) : Prop :=
  1 ≤ L.align ∧
  (∀ f ∈ fields, effFieldAlign m f.align ≤ L.align) ∧
  (∀ n : Nat, m = .aligned n → n ≤ L.align) ∧
  ∀ k : Nat, 1 ≤ k →
    (∀ f ∈ fields, effFieldAlign m f.align ≤ k) →
    (∀ n : Nat, m = .aligned n → n ≤ k) →
    L.align ≤ k

def AllBytesOccupied (fields : List FieldLayout) (L : StructLayout) : Prop :=
  ∀ b : Nat, b < L.size →
    ∃ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
      L.offsets[i] ≤ b ∧ b < L.offsets[i] + fields[i].size
```

- **`StructLayout`, `placeFields`, `fieldsMaxAlign`, `structAlign`, `reprCStruct`, `totalFieldSize`:** Capture the sequential cursor algorithm of `r[layout.repr.c.struct]` (exposing `offsets`, raw post-field cursor `endOffset`, rounded `size`, and `align`) and the scalar sum of field sizes. Positive: `ex_reprCStruct_pos_three_ints`, `ex_totalFieldSize_pos`. Negative: `ex_reprCStruct_neg_no_padding_assumed`, `ex_totalFieldSize_neg`.
- **Soundness invariants (`OffsetsLengthMatch`, `OffsetsAligned`, `OffsetsMonotone`, `FieldsDisjoint`, `OrderedNonOverlapping`, `FieldsInBounds`, `SizeMinimalAligned`):** Separate each geometric guarantee of a struct layout into an independent named predicate. Note that `OrderedNonOverlapping` together with `OffsetsLengthMatch` implies both `OffsetsMonotone` and `FieldsDisjoint` (`Toy.Layout.orderedNonOverlapping_implies_monotone_and_disjoint`), whereas without `OffsetsLengthMatch` the layout `{ offsets := [1, 0], endOffset := 0, size := 0, align := 1 }` satisfies `OrderedNonOverlapping []` (vacuously, since there are no fields) but violates `OffsetsMonotone` (`Toy.Layout.orderedNonOverlapping_without_length_not_monotone`). Positive/negative examples: `ex_offsetsLengthMatch_{pos,neg}`, `ex_offsetsAligned_{pos,neg}`, `ex_offsetsMonotone_{pos,neg}`, `ex_fieldsDisjoint_{pos,neg}`, `ex_orderedNonOverlapping_{pos,neg}`, `ex_fieldsInBounds_{pos,neg}`, `ex_sizeMinimalAligned_{pos,neg}`.
- **Declarative characterization predicates (`OffsetsGreedyMinimal`, `EndOffsetExact`, `AlignIsMaxEffective`) and byte-occupancy predicate (`AllBytesOccupied`):** Pin down minimal inter-field padding (`OffsetsGreedyMinimal`), exact post-field cursor (`EndOffsetExact`), least upper bound alignment (`AlignIsMaxEffective`), and absence of shallow padding (`AllBytesOccupied`). Positive/negative examples: `ex_offsetsGreedyMinimal_pos`, `ex_offsetsGreedyMinimal_neg_extra_pad`, `ex_endOffsetExact_{pos,neg}`, `ex_alignIsMaxEffective_pos`, `ex_alignIsMaxEffective_neg_{too_small,too_large}`, `ex_allBytesOccupied_{pos,neg}`.

#### Unions, Target-Parameterized C-Enum Tags, and Data-Carrying Enums (`Toy.Layout.Enum`)

```lean
structure UnionLayout where
  size : Nat
  align : Nat

def reprCUnion (fields : List FieldLayout) : UnionLayout :=
  let maxAlign := fields.foldl (fun acc f => max acc f.align) 1
  let maxSize := fields.foldl (fun acc f => max acc f.size) 0
  { size := alignUp maxSize maxAlign
    align := maxAlign }

structure EnumLayout where
  size : Nat
  align : Nat
  tagOffset : Nat
  variantFieldOffsets : List (List Nat)

def fitsUnsignedBytes (w : Nat) (minDiscr maxDiscr : Int) : Bool :=
  decide (0 ≤ minDiscr ∧ maxDiscr < (2 : Int) ^ (8 * w))

def fitsSignedBytes (w : Nat) (minDiscr maxDiscr : Int) : Bool :=
  if w = 0 then false
  else decide (-(2 : Int) ^ (8 * w - 1) ≤ minDiscr ∧ maxDiscr < (2 : Int) ^ (8 * w - 1))

def minFittingIntBytes (minDiscr maxDiscr : Int) : Nat :=
  if fitsUnsignedBytes 1 minDiscr maxDiscr || fitsSignedBytes 1 minDiscr maxDiscr then 1
  else if fitsUnsignedBytes 2 minDiscr maxDiscr || fitsSignedBytes 2 minDiscr maxDiscr then 2
  else if fitsUnsignedBytes 4 minDiscr maxDiscr || fitsSignedBytes 4 minDiscr maxDiscr then 4
  else if fitsUnsignedBytes 8 minDiscr maxDiscr || fitsSignedBytes 8 minDiscr maxDiscr then 8
  else 16

structure CEnumTarget where
  /-- Minimum byte width of a C enum on this target (`4` on `x86_64-unknown-linux-gnu`;
      `1` on `arm-none` / `thumbv7m-none-eabi` / `hexagon-unknown-none-elf`). -/
  cEnumMinBytes : Nat
  /-- Byte layout `(size, align)` of a scalar integer of width `bytes` on this target. -/
  intLayout : Nat → FieldLayout

def cEnumTagBytes (target : CEnumTarget) (minDiscr maxDiscr : Int) : Nat :=
  max target.cEnumMinBytes (minFittingIntBytes minDiscr maxDiscr)

def cEnumTagLayout (target : CEnumTarget) (minDiscr maxDiscr : Int) : FieldLayout :=
  target.intLayout (cEnumTagBytes target minDiscr maxDiscr)

def reprCEnum (tag : FieldLayout) (variants : List (List FieldLayout)) : EnumLayout :=
  let variantStructs := variants.map (reprCStruct .none)
  let payload := reprCUnion (variantStructs.map fun s => ⟨s.size, s.align⟩)
  let outer := reprCStruct .none [tag, ⟨payload.size, payload.align⟩]
  let payloadOffset := alignUp tag.size payload.align
  { size := outer.size
    align := outer.align
    tagOffset := outer.offsets.headD 0
    variantFieldOffsets := variantStructs.map fun s => s.offsets.map (· + payloadOffset) }

def reprCEnumForTarget (target : CEnumTarget) (minDiscr maxDiscr : Int)
    (variants : List (List FieldLayout)) : EnumLayout :=
  reprCEnum (cEnumTagLayout target minDiscr maxDiscr) variants

def reprIntEnum (tag : FieldLayout) (variants : List (List FieldLayout)) : EnumLayout :=
  let variantStructs := variants.map fun v => reprCStruct .none (tag :: v)
  let u := reprCUnion (variantStructs.map fun s => ⟨s.size, s.align⟩)
  { size := u.size
    align := u.align
    tagOffset := match variantStructs with | [] => 0 | s :: _ => s.offsets.headD 0
    variantFieldOffsets := variantStructs.map fun s => s.offsets.tail }

def EnumTagAtZero (E : EnumLayout) : Prop :=
  E.tagOffset = 0

def EnumAlignValid (tag : FieldLayout) (variants : List (List FieldLayout)) (E : EnumLayout) : Prop :=
  IsPowerOfTwo E.align ∧
  tag.align ∣ E.align ∧
  ∀ v ∈ variants, ∀ f ∈ v, f.align ∣ E.align

def EnumSizeValid (tag : FieldLayout) (E : EnumLayout) : Prop :=
  E.align ∣ E.size ∧ tag.size ≤ E.size

def EnumVariantsValid (tag : FieldLayout) (variants : List (List FieldLayout)) (E : EnumLayout) : Prop :=
  E.variantFieldOffsets.length = variants.length ∧
  ∀ (k : Nat) (hk : k < variants.length) (ho : k < E.variantFieldOffsets.length),
    let v := variants[k]
    let offs := E.variantFieldOffsets[k]
    offs.length = v.length ∧
    (∀ (j : Nat) (hj : j < v.length) (hjo : j < offs.length),
      tag.size ≤ offs[j] ∧
      v[j].align ∣ offs[j] ∧
      offs[j] + v[j].size ≤ E.size) ∧
    (∀ (j1 j2 : Nat) (h1 : j1 < v.length) (h2 : j2 < v.length)
       (ho1 : j1 < offs.length) (ho2 : j2 < offs.length),
      j1 < j2 → offs[j1] + v[j1].size ≤ offs[j2])

def EnumSharedPayload (tag : FieldLayout) (variants : List (List FieldLayout)) (E : EnumLayout) : Prop :=
  let variantStructs := variants.map (reprCStruct .none)
  let payload := reprCUnion (variantStructs.map fun s => ⟨s.size, s.align⟩)
  let payloadOffset := alignUp tag.size payload.align
  E.variantFieldOffsets = variantStructs.map (fun s => s.offsets.map (· + payloadOffset)) ∧
  IsLeastMultipleGe E.size (payloadOffset + payload.size) E.align

def EnumPerVariantTagged (tag : FieldLayout) (variants : List (List FieldLayout)) (E : EnumLayout) : Prop :=
  let variantStructs := variants.map fun v => reprCStruct .none (tag :: v)
  let maxVarSize := variantStructs.foldl (fun acc s => max acc s.size) 0
  E.variantFieldOffsets = variantStructs.map (fun s => s.offsets.tail) ∧
  IsLeastMultipleGe E.size maxVarSize E.align
```

- **`UnionLayout` and `reprCUnion`:** Capture `#[repr(C)]` union size and alignment (`r[layout.repr.c.union.size-align]`: maximum field alignment with base `1`, and maximum field size rounded up to `align`). Positive: `ex_reprCUnion_pos_rounded` (`reprCUnion [⟨4, 4⟩, ⟨6, 2⟩] = { size := 8, align := 4 }`). Negative: `ex_reprCUnion_neg_unrounded` (`size ≠ 6`).
- **`fitsUnsignedBytes`, `fitsSignedBytes`, `minFittingIntBytes`, `CEnumTarget`, `cEnumTagBytes`, `cEnumTagLayout`:** Capture `rustc`'s target-parameterized bare `#[repr(C)]` enum tag selection (`discr_range_of_repr` in `compiler/rustc_middle/src/ty/layout.rs` lines 77–120 at `14210df0e`), taking the maximum of the target's `c_enum_min_size` (`CEnumTarget.cEnumMinBytes`: `4` on `targetX86_64Linux`, `1` on `targetThumbV7mNoneEabi` and `targetHexagonNoneElf`) and the smallest fitting standard integer width (`minFittingIntBytes`). Positive: `ex_fitsUnsignedBytes_pos`, `ex_fitsSignedBytes_pos`, `ex_minFittingIntBytes_pos_{small,signed_i16,large64}`, `ex_cEnumTarget_pos_x86_64_min`, `ex_cEnumTagBytes_pos_{x86_64,thumb}`, `ex_cEnumTagLayout_pos_{x86_64,thumb,x86_64_large_discr}`. Negative: `ex_fitsUnsignedBytes_neg`, `ex_fitsSignedBytes_neg`, `ex_minFittingIntBytes_neg_large_not_4`, `ex_cEnumTarget_neg_thumb_min_not_4`, `ex_cEnumTagBytes_neg_thumb_not_4`, `ex_cEnumTagLayout_neg_thumb_not_c_int`.
- **`EnumLayout`, `reprCEnum`, `reprCEnumForTarget`, `reprIntEnum`:** Capture the two distinct tagged-union layouts standardized by RFC 2195 (`struct { tag, union { variants } }` for `#[repr(C)]` / `#[repr(C, Int)]` versus `union { struct { tag, v } }` for `#[repr(Int)]`), reading `tagOffset` from the computed struct offsets rather than hardcoding `0`. Positive: `ex_reprCEnum_pos_reference_enum`, `ex_reprCEnumForTarget_pos_thumb`, `ex_reprIntEnum_pos_u8_packs_after_tag`. Negative: `ex_reprCEnum_neg_not_packed_after_tag`, `ex_reprCEnumForTarget_neg_thumb_not_8`, `ex_reprIntEnum_neg_not_reprC_u8`.
- **Enum predicates (`EnumTagAtZero`, `EnumAlignValid`, `EnumSizeValid`, `EnumVariantsValid`, `EnumSharedPayload`, `EnumPerVariantTagged`):** Separate tag-at-zero (`reprCEnum_tagOffset_zero`, `reprIntEnum_tagOffset_zero`, `reprIntEnum_all_variants_tag_at_zero`), power-of-two alignment divisibility (`EnumAlignValid`), size validity (`EnumSizeValid`), variant field disjointness/alignment/ordering (`EnumVariantsValid`), and the two structural offset/rounding rules (`EnumSharedPayload` vs. `EnumPerVariantTagged`). Positive/negative examples: `ex_enumTagAtZero_{pos,neg}`, `ex_enumAlignValid_{pos,neg}`, `ex_enumSizeValid_{pos,neg}`, `ex_enumVariantsValid_{pos,neg_misaligned}`, `ex_enumSharedPayload_{pos,neg_reprInt,neg_padded}`, `ex_enumPerVariantTagged_{pos,neg_reprC,neg_padded}`.

- **Concrete targets and tag layouts (used in Cards 13–19):** verbatim from `lean/Toy/Layout/Enum.lean`. Every target maps a byte width `b` to the scalar layout `⟨b, b⟩` (size and alignment both `b`); `cEnumTagX86_64` evaluates to `⟨4, 4⟩` (`ex_cEnumTagLayout_pos_x86_64 : cEnumTagLayout targetX86_64Linux 0 1 = ⟨4, 4⟩`).

```lean
def targetX86_64Linux : CEnumTarget :=
  { cEnumMinBytes := 4, intLayout := fun b => ⟨b, b⟩ }

def targetThumbV7mNoneEabi : CEnumTarget :=
  { cEnumMinBytes := 1, intLayout := fun b => ⟨b, b⟩ }

def targetHexagonNoneElf : CEnumTarget :=
  { cEnumMinBytes := 1, intLayout := fun b => ⟨b, b⟩ }

def cEnumTagX86_64 : FieldLayout := cEnumTagLayout targetX86_64Linux 0 1
def cEnumTagThumbV7m : FieldLayout := cEnumTagLayout targetThumbV7mNoneEabi 0 1
def cIntLayout32Bit : FieldLayout := ⟨4, 4⟩
def usizeTag64 : FieldLayout := ⟨8, 8⟩
def u8Tag : FieldLayout := ⟨1, 1⟩
def u16Tag : FieldLayout := ⟨2, 2⟩
```

#### Flat Slice-Tailed DSTs and Prefix-Cast Metadata (`Toy.Layout.Dst`)

```lean
structure SliceDstSpec where
  modifier : ReprModifier
  headFields : List FieldLayout
  elem : FieldLayout

def dstInstantiated (d : SliceDstSpec) (n : Nat) : StructLayout :=
  reprCStruct d.modifier (d.headFields ++ [⟨n * d.elem.size, d.elem.align⟩])

def dstTailOffset (d : SliceDstSpec) : Nat :=
  let (_, headEnd) := placeFields d.modifier 0 d.headFields
  alignUp headEnd (effFieldAlign d.modifier d.elem.align)

def dstAlign (d : SliceDstSpec) : Nat :=
  structAlign d.modifier (d.headFields ++ [d.elem])

def dstSize (d : SliceDstSpec) (n : Nat) : Nat :=
  alignUp (dstTailOffset d + n * d.elem.size) (dstAlign d)

def dstTrailingPadding (d : SliceDstSpec) (n : Nat) : Nat :=
  dstSize d n - (dstTailOffset d + n * d.elem.size)

def maxSliceElems (d : SliceDstSpec) (bufferLen : Nat) : Option Nat :=
  if d.elem.size = 0 then none
  else
    let cap := roundDown bufferLen (dstAlign d)
    if cap < dstTailOffset d then none
    else some ((cap - dstTailOffset d) / d.elem.size)

def IsMaxFittingElems (d : SliceDstSpec) (bufferLen n : Nat) : Prop :=
  dstSize d n ≤ bufferLen ∧ ∀ k : Nat, dstSize d k ≤ bufferLen → k ≤ n
```

- **`SliceDstSpec`, `dstInstantiated`, `dstTailOffset`, `dstAlign`, `dstSize`, `dstTrailingPadding`:** Capture flat `#[repr(C)]` structs with sized `headFields` and a trailing slice `[elem]`, comparing per-count array instantiation `[T; n]` (`dstInstantiated`) against the three-parameter closed form (`dstTailOffset`, `dstAlign`, `elem.size`) and post-slice dynamic trailing padding (`dstTrailingPadding`). Positive: `ex_dstSize_pos` (`dstSize ⟨.none, [⟨4, 4⟩], ⟨1, 1⟩⟩ 1 = 8`). Negative: `ex_dstSize_neg_unaligned` (`dstSize ... 1 ≠ 5`).
- **`maxSliceElems` and `IsMaxFittingElems`:** Capture flat prefix-cast slice metadata computation (rounding `bufferLen` down to `dstAlign d` before subtracting `dstTailOffset d` and dividing by `d.elem.size`, returning `none` when `d.elem.size = 0` or `cap < dstTailOffset d`) and its declarative specification (`n` fits and dominates every fitting `k : Nat`). Positive: `ex_maxSliceElems_pos_some`, `ex_maxSliceElems_pos_none`, `ex_isMaxFittingElems_pos`. Negative: `ex_maxSliceElems_neg_naive`, `ex_isMaxFittingElems_neg_not_max`, `ex_isMaxFittingElems_neg_overflows_buf`.

### Result Cards (Cards 1–25)

#### Card 1: `repr-c-struct-invariants` (`Toy.Layout.reprCStruct_invariants_of_align_pos`)

- **Kind / Tier / Depth:** `theorem` | `T0` | `substantive`
- **Plain-language claim:** For any modifier with a positive packing bound (if packed) and any field list whose fields all have positive alignment, `reprCStruct m fields` satisfies the five structural layout invariants: `OffsetsLengthMatch`, `OffsetsAligned`, `OrderedNonOverlapping`, `FieldsInBounds`, and `SizeMinimalAligned` (`OffsetsMonotone` and `FieldsDisjoint` follow as corollaries via `Toy.Layout.orderedNonOverlapping_implies_monotone_and_disjoint`).
- **Lean statement (exact signature and unfolded predicates):**
```lean
-- lean/Toy/Layout/Struct.lean:721-730
theorem reprCStruct_invariants_of_align_pos
    (m : ReprModifier) (fields : List FieldLayout)
    (h_fields : ∀ f ∈ fields, AlignPos f)
    (h_pack : ModifierPackPos m) :
    let L := reprCStruct m fields
    OffsetsLengthMatch fields L ∧
    OffsetsAligned m fields L ∧
    OrderedNonOverlapping fields L ∧
    FieldsInBounds fields L ∧
    SizeMinimalAligned L

-- With key definitions unfolded:
-- h_fields : ∀ f ∈ fields, 0 < f.align
-- h_pack   : ∀ p : Nat, m = .packed p → 0 < p
-- Conclusion for L := reprCStruct m fields:
--   L.offsets.length = fields.length ∧
--   (∀ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
--     effFieldAlign m fields[i].align ∣ L.offsets[i]) ∧
--   (∀ (i j : Nat) (hi : i < fields.length) (hj : j < fields.length)
--      (hoi : i < L.offsets.length) (hoj : j < L.offsets.length),
--     i < j → L.offsets[i] + fields[i].size ≤ L.offsets[j]) ∧
--   (∀ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
--     L.offsets[i] + fields[i].size ≤ L.endOffset) ∧
--   (L.endOffset ≤ L.size ∧ L.align ∣ L.size ∧
--     ∀ k : Nat, L.endOffset ≤ k → L.align ∣ k → L.size ≤ k)
```
- **Supporting hashed Lean statements (`lean_names`):** `Toy.Layout.orderedNonOverlapping_implies_monotone_and_disjoint`, `Toy.Layout.orderedNonOverlapping_without_length_not_monotone`.
- **Hypothesis ledger:**
  - `h_fields` (`∀ f ∈ fields, AlignPos f`): requires `0 < f.align` for every field `f` so modular alignment `alignUp cursor (effFieldAlign m f.align)` produces a multiple of `effFieldAlign m f.align` (`alignUp` totalizes division by `0` to a no-op) — `tight`: counterexample `Toy.Layout.ce_reprCStruct_invariants_drop_fields_align_pos` (`m = .none`, `fields = [⟨1, 1⟩, ⟨1, 0⟩]`). Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.properties.align]`).
  - `h_pack` (`ModifierPackPos m`): requires `0 < p` whenever `m = .packed p` so clamping `min f.align p` remains strictly positive — `tight`: counterexample `Toy.Layout.ce_reprCStruct_invariants_drop_pack_pos` (`m = .packed 0`, `fields = [⟨1, 1⟩, ⟨1, 4⟩]`). Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.repr.alignment.constraint-alignment]`).
- **Non-vacuity witness:** `Toy.Layout.nv_reprCStruct_invariants_of_align_pos` (`m = .none`, `fields = [⟨1, 1⟩, ⟨4, 4⟩, ⟨2, 2⟩]`).
- **Non-claims:**
  - These properties do not characterize `reprCStruct`: layouts with gratuitous inter-field padding, or with a struct alignment smaller than a field's alignment, satisfy all of them. The minimal-padding and alignment rules of `repr(C)` are not among the stated properties (see Card 2).
  - Does not establish `IsPowerOfTwo L.align` or that effective field alignments divide `L.align` (requires power-of-two alignments; Card 3).
  - Mutual independence in Card 4 (`Toy.Layout.struct_invariants_mutually_independent`) is proved for the five-invariant set obtained by splitting `OrderedNonOverlapping` into `OffsetsMonotone` and `FieldsDisjoint` under `OffsetsLengthMatch` (on Card 1's five-conjunct set, `overlappingUnionLayout` violates only `OrderedNonOverlapping` and `offsets = []` on `[⟨1, 1⟩]` violates only `OffsetsLengthMatch`).
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.c.struct]` lines 240–353, `r[layout.repr.alignment]` lines 632–655); CompCert (`AbsInt/CompCert` `2685140bf72c959446981fb99b5e44a8975021bc`, `cfrontend/Ctypes.v`, `field_offset_in_range_gen`/`field_offset_in_range` lines 748–770, `field_offset_no_overlap` lines 774–797, `field_offset_aligned_gen`/`field_offset_aligned` lines 812–830); `rustc_abi` (`rust-lang/rust` executed commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `compiler/rustc_abi/src/layout.rs`, `LayoutCalculator::univariant_biased` lines 1094–1328; commit `4b5350e87e487aed08ab2f9f0160a4b2616438bc`, `layout_of_univariant_biased` lines 591–823); prose context: unmerged Aeneas PR `AeneasVerif/aeneas#1447` (`JoJoDeveloping/aeneas` `2a1dd75567517e078f90b1df746af7373fe24cbc`, `backends/lean/Aeneas/Data/Layout/ReprC.lean`, `tupleFieldOffset_mono` lines 163–168, `tupleFieldOffset_le_end` lines 172–176).
- **Design question informed:** Identifies the minimal toy-domain preconditions (`0 < align`, rather than powers of two or `align ∣ size`) under which `reprCStruct` satisfies its five structural soundness invariants, with `OffsetsMonotone` and `FieldsDisjoint` separated as proved corollaries.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprCStruct_invariants_of_align_pos`, `nv_reprCStruct_invariants_of_align_pos`, `ce_reprCStruct_invariants_drop_fields_align_pos`, `ce_reprCStruct_invariants_drop_pack_pos`, `orderedNonOverlapping_implies_monotone_and_disjoint`, and `orderedNonOverlapping_without_length_not_monotone` in `lean/Toy/Layout/Struct.lean`.
  - `Basis: normative (r[layout.properties.align], r[layout.properties.size], r[layout.repr.alignment.constraint-alignment]) + derived (modeling bridge)` — The Reference requires every alignment to be "at least 1, and always a power of 2" (line 19) and every size to be "a multiple of its alignment" (line 22), and requires every `align(x)` / `packed(x)` argument to be a power of two from 1 up to 2^29 (lines 638–639, paraphrased). Field layouts and modifiers of real Rust types therefore satisfy this card's alignment hypotheses, and its tightness counterexamples (alignments or packing arguments such as `0`, `3`, or `6`) correspond to no Rust type; they do not exhibit a Rust layout for which the conclusion fails.
  - `Basis: derived (modeling bridge)` — Connecting `reprCStruct` to Rust `#[repr(C)]` structs rests on normative rules `r[layout.repr.c.struct]` and `r[layout.repr.alignment]` (`c9cc3282`), `rustc_abi`'s `univariant_biased` cursor loop (`14210df0e`), and 12 empirical struct probes (`xc_01`–`xc_12`), restricted to non-overflowing sizes (`< obj_size_bound`) on targets with `aggregate_align = 1`.

#### Card 2: `repr-c-struct-characterization` (`Toy.Layout.reprCStruct_eq_iff_of_align_pos`)

- **Kind / Tier / Depth:** `characterization` | `T1` | `substantive`
- **Plain-language claim:** For any modifier with a positive packing bound (if packed), any field list whose fields all have positive alignment, and any `StructLayout` `L`, `L = reprCStruct m fields` holds if and only if `L` satisfies the five declarative rules `OffsetsLengthMatch`, `OffsetsGreedyMinimal`, `EndOffsetExact`, `AlignIsMaxEffective`, and `SizeMinimalAligned`.
- **Lean statement (exact signature and unfolded predicates):**
```lean
-- lean/Toy/Layout/Struct.lean:806-815
theorem reprCStruct_eq_iff_of_align_pos
    (m : ReprModifier) (fields : List FieldLayout) (L : StructLayout)
    (h_fields : ∀ f ∈ fields, AlignPos f)
    (h_pack : ModifierPackPos m) :
    L = reprCStruct m fields ↔
      OffsetsLengthMatch fields L ∧
      OffsetsGreedyMinimal m fields L ∧
      EndOffsetExact fields L ∧
      AlignIsMaxEffective m fields L ∧
      SizeMinimalAligned L

-- With key definitions unfolded on the right-hand side:
--   L.offsets.length = fields.length ∧
--   ((∀ (hf : 0 < fields.length) (ho : 0 < L.offsets.length),
--       IsLeastMultipleGe L.offsets[0] 0 (effFieldAlign m fields[0].align)) ∧
--    ∀ (i : Nat) (hf : i + 1 < fields.length) (ho : i + 1 < L.offsets.length),
--      IsLeastMultipleGe L.offsets[i + 1]
--        (L.offsets[i]'(Nat.lt_of_succ_lt ho) + fields[i].size)
--        (effFieldAlign m fields[i + 1].align)) ∧
--   (match fields.getLast?, L.offsets.getLast? with
--    | none, _ => L.endOffset = 0
--    | some f, some o => L.endOffset = o + f.size
--    | some _, none => False) ∧
--   (1 ≤ L.align ∧
--    (∀ f ∈ fields, effFieldAlign m f.align ≤ L.align) ∧
--    (∀ n : Nat, m = .aligned n → n ≤ L.align) ∧
--    ∀ k : Nat, 1 ≤ k → (∀ f ∈ fields, effFieldAlign m f.align ≤ k) →
--      (∀ n : Nat, m = .aligned n → n ≤ k) → L.align ≤ k) ∧
--   IsLeastMultipleGe L.size L.endOffset L.align
```
- **Hypothesis ledger:**
  - `h_fields` (`∀ f ∈ fields, AlignPos f`): requires `0 < f.align` so `alignUp cursor (effFieldAlign m f.align)` satisfies `IsLeastMultipleGe` (`IsLeastMultipleGe _ n 0` is unsatisfiable for `n > 0`) — `tight`: counterexample `Toy.Layout.ce_reprCStruct_eq_iff_drop_fields_align_pos`. Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.properties.align]`).
  - `h_pack` (`ModifierPackPos m`): requires `0 < p` when `m = .packed p` so `effFieldAlign (.packed p) f.align > 0` — `tight`: counterexample `Toy.Layout.ce_reprCStruct_eq_iff_drop_pack_pos`. Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.repr.alignment.constraint-alignment]`).
- **Non-vacuity witness:** `Toy.Layout.nv_reprCStruct_eq_iff_of_align_pos` (`m = .none`, `fields = [⟨1, 1⟩, ⟨4, 4⟩]`).
- **Non-claims:**
  - Characterizes `Toy.Layout.reprCStruct` (which abstracts away `isize::MAX` / `obj_size_bound` overflow and non-unit `aggregate_align`); agreement with `rustc` is a separate `derived (modeling bridge)` claim. Does not characterize `#[repr(Rust)]` structs.
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.c.struct.align]` line 244, `r[layout.repr.c.struct.size-field-offset]` lines 246–253, `r[layout.repr.alignment.packed-padding]` line 651); `rustc_abi` (`rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `compiler/rustc_abi/src/layout.rs`, `univariant_biased` lines 1263–1324).
- **Design question informed:** Answers which declarative properties uniquely pin down the `#[repr(C)]` struct layout algorithm without mentioning `%`-based `alignUp` or left-folds in the specification.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprCStruct_eq_iff_of_align_pos`, `nv_reprCStruct_eq_iff_of_align_pos`, `ce_reprCStruct_eq_iff_drop_fields_align_pos`, and `ce_reprCStruct_eq_iff_drop_pack_pos` in `lean/Toy/Layout/Struct.lean`.
  - `Basis: normative (r[layout.properties.align], r[layout.properties.size], r[layout.repr.alignment.constraint-alignment]) + derived (modeling bridge)` — The Reference requires every alignment to be "at least 1, and always a power of 2" (line 19) and every size to be "a multiple of its alignment" (line 22), and requires every `align(x)` / `packed(x)` argument to be a power of two from 1 up to 2^29 (lines 638–639, paraphrased). Field layouts and modifiers of real Rust types therefore satisfy this card's alignment hypotheses, and its tightness counterexamples (alignments or packing arguments such as `0`, `3`, or `6`) correspond to no Rust type; they do not exhibit a Rust layout for which the conclusion fails.
  - `Basis: derived (modeling bridge)` — The Reference's algorithm (`c9cc3282`) says to "add padding bytes to the current offset until it is a multiple of the field's alignment" (line 251) and that "the size of the struct is the current offset rounded up to the nearest multiple of the struct's alignment" (line 253); the struct's alignment is "the alignment of the most-aligned field in it, or one if there are no fields" (line 244), and with `packed` the inter-field padding is "the minimum required in order to satisfy each field's (possibly altered) alignment" (line 651). Translating these least-multiple clauses gives `OffsetsGreedyMinimal`, `SizeMinimalAligned`, and `AlignIsMaxEffective`, under `aggregate_align = 1` and non-overflowing sizes.

#### Card 3: `repr-c-struct-align-pow2-divides` (`Toy.Layout.reprCStruct_align_pow2_divides`)

- **Kind / Tier / Depth:** `theorem` | `T0` | `shallow`
- **Plain-language claim:** If every field alignment and any numeric modifier argument in `m` is a power of two, then `(reprCStruct m fields).align` is a power of two divisible by every field's effective (possibly `packed`-reduced) alignment.
- **Lean statement (exact signature and unfolded predicates):**
```lean
-- lean/Toy/Layout/Struct.lean:965-970
theorem reprCStruct_align_pow2_divides
    (m : ReprModifier) (fields : List FieldLayout)
    (h_fields : ∀ f ∈ fields, AlignPow2 f)
    (h_mod : ModifierPow2 m) :
    let L := reprCStruct m fields
    IsPowerOfTwo L.align ∧
    ∀ f ∈ fields, effFieldAlign m f.align ∣ L.align

-- Unfolded: AlignPow2 f := ∃ k : Nat, f.align = 2 ^ k;
-- IsPowerOfTwo L.align := ∃ k : Nat, L.align = 2 ^ k.
```
- **Hypothesis ledger:**
  - `h_fields` (`∀ f ∈ fields, AlignPow2 f`): requires power-of-two field alignments so `max` acts as `lcm` — `tight`: counterexample `Toy.Layout.ce_reprCStruct_align_dvd_drop_fields_pow2` (`[⟨2, 2⟩, ⟨3, 3⟩]` gives `align = 3`, `¬ (2 ∣ 3)`). Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.properties.align]`).
  - `h_mod` (`ModifierPow2 m`): requires power-of-two numeric modifier arguments — `tight`: counterexample `Toy.Layout.ce_reprCStruct_align_dvd_drop_mod_pow2` (`m = .aligned 3` on `[⟨2, 2⟩]`). Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.repr.alignment.constraint-alignment]`).
- **Non-vacuity witness:** `Toy.Layout.nv_reprCStruct_align_pow2_divides` (`m = .aligned 8`, `[⟨1, 1⟩, ⟨4, 4⟩]`).
- **Non-claims:**
  - Does not show that natural (unclamped) field alignment divides `L.align` under `packed(p)`, and does not enforce Rust's concrete `align ≤ 2^29` ceiling (`r[layout.repr.alignment.constraint-alignment]`).
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.properties.align]` line 19, `r[layout.repr.c.struct.align]` line 244); CompCert (`AbsInt/CompCert` `2685140bf72c959446981fb99b5e44a8975021bc`, `cfrontend/Ctypes.v`, `alignof_composite_two_p` lines 642–649); prose context: unmerged Aeneas PR `AeneasVerif/aeneas#1447` (`JoJoDeveloping/aeneas` `2a1dd75567517e078f90b1df746af7373fe24cbc`, `ReprC.lean`, `effAlign_isPowerOfTwo` lines 125–131).
- **Design question informed:** Isolates the exact algebraic role of power-of-two alignments (`max` over powers of two equals `lcm`), ensuring that an `L.align`-aligned struct base address aligns every field to its effective alignment.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprCStruct_align_pow2_divides`, `nv_reprCStruct_align_pow2_divides`, `ce_reprCStruct_align_dvd_drop_fields_pow2`, and `ce_reprCStruct_align_dvd_drop_mod_pow2` in `lean/Toy/Layout/Struct.lean`.
  - `Basis: normative (r[layout.properties.align], r[layout.properties.size], r[layout.repr.alignment.constraint-alignment]) + derived (modeling bridge)` — The Reference requires every alignment to be "at least 1, and always a power of 2" (line 19) and every size to be "a multiple of its alignment" (line 22), and requires every `align(x)` / `packed(x)` argument to be a power of two from 1 up to 2^29 (lines 638–639, paraphrased). Field layouts and modifiers of real Rust types therefore satisfy this card's alignment hypotheses, and its tightness counterexamples (alignments or packing arguments such as `0`, `3`, or `6`) correspond to no Rust type; they do not exhibit a Rust layout for which the conclusion fails.
  - `Basis: derived (modeling bridge)` — Applies to valid Rust `#[repr(C)]` structs because Rust enforces power-of-two type and modifier alignments (`r[layout.properties.align]`, `r[layout.repr.alignment.constraint-alignment]`).

#### Card 4: `struct-invariants-mutually-independent` (`Toy.Layout.struct_invariants_mutually_independent`)

- **Kind / Tier / Depth:** `counterexample` | `T1` | `shallow`
- **Plain-language claim:** None of the five struct-layout invariants (`OffsetsAligned`, `OffsetsMonotone`, `FieldsDisjoint`, `FieldsInBounds`, `SizeMinimalAligned`) is implied by the conjunction of the other four together with `OffsetsLengthMatch`: on the concrete sample structs `sampleStructAsc = [⟨1, 1⟩, ⟨4, 4⟩]` and `sampleStructDesc = [⟨4, 4⟩, ⟨1, 1⟩]`, five concrete variant layout algorithms each violate one property while satisfying the other four and `OffsetsLengthMatch`.
- **Lean statement:**
```lean
-- lean/Toy/Layout/Struct.lean:1284-1304
theorem struct_invariants_mutually_independent :
    (let L := unalignedPackingLayout sampleStructAsc
     OffsetsLengthMatch sampleStructAsc L ∧ ¬ OffsetsAligned .none sampleStructAsc L ∧
     OffsetsMonotone L ∧ FieldsDisjoint sampleStructAsc L ∧
     FieldsInBounds sampleStructAsc L ∧ SizeMinimalAligned L) ∧
    (let L := reversedOrderLayout sampleStructAsc
     OffsetsLengthMatch sampleStructAsc L ∧ OffsetsAligned .none sampleStructAsc L ∧
     ¬ OffsetsMonotone L ∧ FieldsDisjoint sampleStructAsc L ∧
     FieldsInBounds sampleStructAsc L ∧ SizeMinimalAligned L) ∧
    (let L := overlappingUnionLayout sampleStructAsc
     OffsetsLengthMatch sampleStructAsc L ∧ OffsetsAligned .none sampleStructAsc L ∧
     OffsetsMonotone L ∧ ¬ FieldsDisjoint sampleStructAsc L ∧
     FieldsInBounds sampleStructAsc L ∧ SizeMinimalAligned L) ∧
    (let L := truncatedEndLayout sampleStructAsc
     OffsetsLengthMatch sampleStructAsc L ∧ OffsetsAligned .none sampleStructAsc L ∧
     OffsetsMonotone L ∧ FieldsDisjoint sampleStructAsc L ∧
     ¬ FieldsInBounds sampleStructAsc L ∧ SizeMinimalAligned L) ∧
    (let L := unroundedTailLayout sampleStructDesc
     OffsetsLengthMatch sampleStructDesc L ∧ OffsetsAligned .none sampleStructDesc L ∧
     OffsetsMonotone L ∧ FieldsDisjoint sampleStructDesc L ∧
     FieldsInBounds sampleStructDesc L ∧ ¬ SizeMinimalAligned L)
```
- **Variant layouts and sample structs (verbatim from `lean/Toy/Layout/Struct.lean`):**
```lean
def unalignedPackingLayout (fields : List FieldLayout) : StructLayout :=
  let (offs, endOff) := placeFields (.packed 1) 0 fields
  let a := structAlign .none fields
  { offsets := offs, endOffset := endOff, size := alignUp endOff a, align := a }

def reversedOrderLayout (fields : List FieldLayout) : StructLayout :=
  let rev := reprCStruct .none fields.reverse
  { offsets := rev.offsets.reverse, endOffset := rev.endOffset, size := rev.size, align := rev.align }

def overlappingUnionLayout (fields : List FieldLayout) : StructLayout :=
  let maxSz := fields.foldl (fun acc f => max acc f.size) 0
  let a := structAlign .none fields
  { offsets := List.replicate fields.length 0, endOffset := maxSz, size := alignUp maxSz a, align := a }

def truncatedEndLayout (fields : List FieldLayout) : StructLayout :=
  let base := reprCStruct .none fields
  let truncEnd := base.offsets.getLastD 0
  { offsets := base.offsets, endOffset := truncEnd, size := alignUp truncEnd base.align, align := base.align }

def unroundedTailLayout (fields : List FieldLayout) : StructLayout :=
  let base := reprCStruct .none fields
  { offsets := base.offsets, endOffset := base.endOffset, size := base.endOffset, align := base.align }

def sampleStructAsc : List FieldLayout := [⟨1, 1⟩, ⟨4, 4⟩]

def sampleStructDesc : List FieldLayout := [⟨4, 4⟩, ⟨1, 1⟩]
```
- **Supporting hashed Lean statements (`lean_names`):** `Toy.Layout.orderedNonOverlapping_implies_monotone_and_disjoint`, `Toy.Layout.orderedNonOverlapping_without_length_not_monotone`.
- **Hypothesis ledger:** None (concrete witnessed counterexample theorem).
- **Non-vacuity witness:** Evaluated directly on `sampleStructAsc = [⟨1, 1⟩, ⟨4, 4⟩]` (variants 1–4) and `sampleStructDesc = [⟨4, 4⟩, ⟨1, 1⟩]` (variant 5).
- **Non-claims:**
  - Each variant algorithm violates exactly one property on the stated sample input only. On other inputs a variant may violate none.
  - Does not show that the five properties uniquely determine `reprCStruct` (see Card 2 for the characterizing properties).
  - Does not claim that `OrderedNonOverlapping` is independent of `OffsetsMonotone` or `FieldsDisjoint`: `OrderedNonOverlapping` together with `OffsetsLengthMatch` implies both (`Toy.Layout.orderedNonOverlapping_implies_monotone_and_disjoint`), whereas dropping `OffsetsLengthMatch` breaks that implication (`Toy.Layout.orderedNonOverlapping_without_length_not_monotone`).
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.rust.layout]` and `r[layout.repr.rust.struct]` lines 174–183, contrasting `#[repr(Rust)]` order-independent disjointness against `#[repr(C)]` declaration-order monotonicity).
- **Design question informed:** Definition-adequacy reference point confirming that splitting `OrderedNonOverlapping` into `OffsetsMonotone` and `FieldsDisjoint` produces five mutually non-redundant invariants relative to `OffsetsLengthMatch`.
- **Evidentiary basis:** `Basis: execution (Lean kernel check)` — `Toy.Layout.struct_invariants_mutually_independent`, `orderedNonOverlapping_implies_monotone_and_disjoint`, and `orderedNonOverlapping_without_length_not_monotone` in `lean/Toy/Layout/Struct.lean` (pure formal property of `Toy.Layout` predicates; no external modeling-bridge claim is made).

#### Card 5: `repr-c-packed-one-no-padding` (`Toy.Layout.reprCStruct_packed_one_no_padding`)

- **Kind / Tier / Depth:** `theorem` | `T0` | `shallow`
- **Plain-language claim:** For every field list `fields`, `reprCStruct (.packed 1) fields` has no shallow padding (`AllBytesOccupied`), total size and `endOffset` equal to `totalFieldSize fields`, overall alignment `1`, and every field `i` placed at `totalFieldSize (fields.take i)`.
- **Lean statement (exact signature and unfolded `AllBytesOccupied`):**
```lean
-- lean/Toy/Layout/Struct.lean:1453-1460
theorem reprCStruct_packed_one_no_padding (fields : List FieldLayout) :
    let L := reprCStruct (.packed 1) fields
    AllBytesOccupied fields L ∧
    L.size = totalFieldSize fields ∧
    L.endOffset = totalFieldSize fields ∧
    L.align = 1 ∧
    ∀ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
      L.offsets[i] = totalFieldSize (fields.take i)

-- Unfolded AllBytesOccupied fields L:
--   ∀ b : Nat, b < L.size →
--     ∃ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
--       L.offsets[i] ≤ b ∧ b < L.offsets[i] + fields[i].size
```
- **Hypothesis ledger:** None.
- **Non-vacuity witness:** `Toy.Layout.nv_reprCStruct_packed_one_no_padding` (`[⟨1, 1⟩, ⟨4, 4⟩, ⟨1, 1⟩]` (`[u8, u32, u8]`) -> `offsets = [0, 1, 5]`, `endOffset = 6`, `size = 6`, `align = 1`).
- **Non-claims:**
  - Does not eliminate padding inside individual nested fields (`r[layout.repr.alignment.intro]`: `packed` does not alter internal field layouts).
  - Does not imply `OffsetsAligned (.packed 1) fields L` when a field has `f.align = 0` (that requires `AlignPos`; Card 1).
  - Does not check Rust's static restriction prohibiting a `packed` struct from transitively containing an `align(N)` type (`r[layout.repr.alignment.constraint-exclusive]`).
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.alignment.packed-padding]` line 651); `rustc_abi` (`rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `compiler/rustc_abi/src/layout.rs`, lines 1278–1282; commit `4b5350e87e487aed08ab2f9f0160a4b2616438bc`, lines 780–783).
- **Design question informed:** Establishes the closed-form prefix-sum offsets, total size, unit alignment, and shallow-unpadded guarantee of `#[repr(C, packed(1))]`.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprCStruct_packed_one_no_padding` and `nv_reprCStruct_packed_one_no_padding` in `lean/Toy/Layout/Struct.lean`.
  - `Basis: derived (modeling bridge)` — Matches Rust `#[repr(C, packed)]` / `#[repr(C, packed(1))]` (`r[layout.repr.alignment.packed-padding]`, `xc_08_packed1`) for legal non-overflowing Rust structs.

#### Card 6: `repr-c-packed-align-le` (`Toy.Layout.reprCStruct_packed_align_le`)

- **Kind / Tier / Depth:** `theorem` | `T0` | `shallow`
- **Plain-language claim:** For every field list `fields` and packing bound `n`, `(reprCStruct (.packed n) fields).align` is at most `max 1 n` and at most `(reprCStruct .none fields).align`.
- **Lean statement:**
```lean
-- lean/Toy/Layout/Struct.lean:1490-1492
theorem reprCStruct_packed_align_le (fields : List FieldLayout) (n : Nat) :
    (reprCStruct (.packed n) fields).align ≤ max 1 n ∧
    (reprCStruct (.packed n) fields).align ≤ (reprCStruct .none fields).align
```
- **Supporting hashed Lean statements (`lean_names`):** `Toy.Layout.ex_packed_non_pow2_increases_size`.
- **Hypothesis ledger:** None (holds unconditionally over `Nat`, including `n = 0` and `fields = []`).
- **Non-vacuity witness:** `Toy.Layout.nv_reprCStruct_packed_align_le` (`fields = [⟨1, 1⟩, ⟨8, 8⟩]`, `n = 2` -> `align = 2 ≤ max 1 2` and `2 ≤ 8`).
- **Non-claims:**
  - Does not assert `(reprCStruct (.packed n) fields).size ≤ (reprCStruct .none fields).size` for arbitrary `Nat` alignments: without power-of-two alignments, `packed(2)` on `[⟨3, 3⟩, ⟨3, 3⟩]` strictly increases size from `6` to `8` (`Toy.Layout.ex_packed_non_pow2_increases_size`).
  - Does not claim equality `(reprCStruct (.packed n) fields).align = max 1 n` (when every field has alignment `< n`, the struct alignment remains `fieldsMaxAlign .none fields`).
  - Does not model targets where `TargetDataLayout::aggregate_align > 1`.
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.alignment.packed]` and `r[layout.repr.alignment.packed-fields]` lines 645–648); prose context: unmerged Aeneas PR `AeneasVerif/aeneas#1447` (`JoJoDeveloping/aeneas` `2a1dd75567517e078f90b1df746af7373fe24cbc`, `ReprC.lean`, `mkTuple_packed_bounds_align` lines 220–223).
- **Design question informed:** Bounds the overall alignment of `#[repr(C, packed(N))]` for arbitrary `N`, complementing `packed(1)` (Card 5) and `packed(N)` no-op (Card 7).
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprCStruct_packed_align_le`, `nv_reprCStruct_packed_align_le`, and `ex_packed_non_pow2_increases_size` in `lean/Toy/Layout/Struct.lean`.
  - `Basis: derived (modeling bridge)` — Matches `r[layout.repr.alignment.packed]` (`c9cc3282` lines 645–648) and `xc_09_packed2` on `aggregate_align = 1` targets.

#### Card 7: `repr-c-packed-ge-fields-noop` (`Toy.Layout.reprCStruct_packed_ge_fields_noop`)

- **Kind / Tier / Depth:** `theorem` | `T0` | `shallow`
- **Plain-language claim:** If `n` is at least every field's natural alignment (`∀ f ∈ fields, f.align ≤ n`), then `reprCStruct (.packed n) fields` equals `reprCStruct .none fields`.
- **Lean statement:**
```lean
-- lean/Toy/Layout/Struct.lean:1556-1559
theorem reprCStruct_packed_ge_fields_noop
    (fields : List FieldLayout) (n : Nat)
    (h_ge : ∀ f ∈ fields, f.align ≤ n) :
    reprCStruct (.packed n) fields = reprCStruct .none fields
```
- **Hypothesis ledger:**
  - `h_ge` (`∀ f ∈ fields, f.align ≤ n`): ensures `min f.align n = f.align` for every field in `fields`, leaving effective alignments, offsets, `endOffset`, `align`, and `size` unchanged — `tight`: counterexample `Toy.Layout.ce_packed_noop_drop_ge` (`fields = [⟨1, 1⟩, ⟨4, 4⟩]`, `n = 2`).
- **Non-vacuity witness:** `Toy.Layout.nv_reprCStruct_packed_ge_fields_noop` (`fields = [⟨1, 1⟩, ⟨4, 4⟩]`, `n = 4`).
- **Non-claims:**
  - This is a layout statement only; it says nothing about which references to fields of such a type `rustc` accepts. (`Basis: source`, not probed: `rustc`'s packed-reference check calls `place_unalignment` (`compiler/rustc_mir_transform/src/check_packed_ref.rs` line 42 at `14210df0e`), which classifies a place inside a `packed(N)` struct as not unaligned when its type's ABI alignment is at most `N` and the type is sized or has a slice or `str` tail (`compiler/rustc_const_eval/src/util/alignment.rs` lines 26–44).) Separately, the Reference forbids a `packed` type from transitively containing an `align`ed type, whatever `N` is (`r[layout.repr.alignment.constraint-exclusive]`, line 654; `Basis: normative`).
  - Does not cover targets where `TargetDataLayout::aggregate_align > 1` (in `rustc_abi`, `pack.is_some()` resets the initial aggregate alignment from `dl.aggregate_align` to `1`; `compiler/rustc_abi/src/layout.rs` line 1108 at `14210df0e`, line 605 at `4b5350e8`).
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.alignment.packed]` line 645, `r[layout.repr.alignment.constraint-exclusive]` line 654); `rustc_const_eval` (`rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `4b5350e87e487aed08ab2f9f0160a4b2616438bc`, `compiler/rustc_const_eval/src/util/alignment.rs`, `place_unalignment` lines 9–50, especially lines 26–44); prose context: unmerged Aeneas PR `AeneasVerif/aeneas#1447` (`JoJoDeveloping/aeneas` `2a1dd75567517e078f90b1df746af7373fe24cbc`, `ReprC.lean`, `mkTuple_large_packed_nop` lines 214–218).
- **Design question informed:** Justifies simplifying `packed(N)` to plain `#[repr(C)]` in layout calculations whenever `N` dominates all field alignments on `aggregate_align = 1` targets.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprCStruct_packed_ge_fields_noop`, `nv_reprCStruct_packed_ge_fields_noop`, and `ce_packed_noop_drop_ge` in `lean/Toy/Layout/Struct.lean`.
  - `Basis: derived (modeling bridge)` — Matches `rustc_abi` (`14210df0e`) and `xc_10_packed_noop` on targets where `dl.aggregate_align == 1`.

#### Card 8: `repr-c-aligned-preserves-offsets` (`Toy.Layout.reprCStruct_aligned_preserves_offsets`)

- **Kind / Tier / Depth:** `theorem` | `T0` | `definitional`
- **Plain-language claim:** For any `fields` and `n`, `reprCStruct (.aligned n) fields` has the exact same field offsets and `endOffset` as `reprCStruct .none fields`, alignment `max base.align n`, and size `alignUp base.endOffset (max base.align n)`.
- **Lean statement:**
```lean
-- lean/Toy/Layout/Struct.lean:1601-1607
theorem reprCStruct_aligned_preserves_offsets (fields : List FieldLayout) (n : Nat) :
    let base := reprCStruct .none fields
    let aligned := reprCStruct (.aligned n) fields
    aligned.offsets = base.offsets ∧
    aligned.endOffset = base.endOffset ∧
    aligned.align = max base.align n ∧
    aligned.size = alignUp base.endOffset (max base.align n)
```
- **Hypothesis ledger:** None.
- **Non-vacuity witness:** `Toy.Layout.nv_reprCStruct_aligned_preserves_offsets` (`fields = [⟨2, 2⟩, ⟨1, 1⟩]`, `n = 8`).
- **Non-claims:**
  - Offset invariance under `align(N)` holds by construction of the model (`effFieldAlign (.aligned n) a = a`); that `rustc` behaves the same way is a separate `derived (modeling bridge)` claim.
  - Does not claim `aligned.size = alignUp base.size (max base.align n)` without power-of-two alignments (Card 9).
  - Does not model `#[repr(Rust, align(N))]`, where field order is unspecified.
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.alignment.align]` line 642); `rustc_abi` (`rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `compiler/rustc_abi/src/layout.rs`, lines 1312–1320; commit `4b5350e87e487aed08ab2f9f0160a4b2616438bc`, lines 811–819).
- **Design question informed:** Records the model's exact `align(N)` offset invariance and size/alignment rule, separating it cleanly from the `rustc_abi` source inspection needed to justify offset invariance in `rustc`.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprCStruct_aligned_preserves_offsets` and `nv_reprCStruct_aligned_preserves_offsets` in `lean/Toy/Layout/Struct.lean` (definitional consequence of `effFieldAlign` and `structAlign`).
  - `Basis: derived (modeling bridge)` — In `rustc_abi` (`compiler/rustc_abi/src/layout.rs` lines 1312–1320 at `14210df0e`), `repr.align` is folded into `align` *after* the sequential field-offset placement loop finishes and before final `offset.align_to(align.abi)` struct-size rounding, corroborated empirically by `xc_11_aligned8` and `xc_12_aligned_noop`.

#### Card 9: `repr-c-aligned-size-composition` (`Toy.Layout.reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2`)

- **Kind / Tier / Depth:** `theorem` | `T0` | `shallow`
- **Plain-language claim:** When every field alignment and `n` are powers of two, `(reprCStruct (.aligned n) fields).size` equals `alignUp (reprCStruct .none fields).size (max (reprCStruct .none fields).align n)`.
- **Lean statement (exact signature and unfolded predicates):**
```lean
-- lean/Toy/Layout/Struct.lean:1631-1636
theorem reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2
    (fields : List FieldLayout) (n : Nat)
    (h_fields : ∀ f ∈ fields, AlignPow2 f)
    (h_n : IsPowerOfTwo n) :
    let base := reprCStruct .none fields
    (reprCStruct (.aligned n) fields).size = alignUp base.size (max base.align n)

-- Unfolded: AlignPow2 f := ∃ k : Nat, f.align = 2 ^ k;
-- IsPowerOfTwo n := ∃ k : Nat, n = 2 ^ k.
```
- **Hypothesis ledger:**
  - `h_fields` (`∀ f ∈ fields, AlignPow2 f`): ensures `base.align` is a power of two dividing `max base.align n` so intermediate rounding to `base.align` does not overshoot — `tight`: counterexample `Toy.Layout.ce_aligned_size_drop_fields_pow2` (`[⟨3, 3⟩, ⟨1, 1⟩]`, `n = 4` -> `size = 4 ≠ 8 = alignUp 6 4`). Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.properties.align]`).
  - `h_n` (`IsPowerOfTwo n`): ensures `base.align ∣ max base.align n` when `n > base.align` — `tight`: counterexample `Toy.Layout.ce_aligned_size_drop_n_pow2` (`[⟨4, 4⟩, ⟨1, 1⟩]`, `n = 6` -> `size = 6 ≠ 12 = alignUp 8 6`). Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.repr.alignment.constraint-alignment]`).
- **Non-vacuity witness:** `Toy.Layout.nv_reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2` (`[⟨4, 4⟩, ⟨1, 1⟩]`, `n = 8`).
- **Non-claims:**
  - Fails for non-power-of-two alignments in `Nat`; does not imply `reprCStruct (.aligned n) fields` is padding-free when `base` is padding-free.
- **Prior art:** Prose context (motivating use): unmerged Aeneas PR `AeneasVerif/aeneas#1447` (`JoJoDeveloping/aeneas` `2a1dd75567517e078f90b1df746af7373fe24cbc`, `ReprC.lean`, `alignTupleUp` lines 9–13); related DST normal-form discussion: `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`, `zerocopy/src/layout.rs`, `DstLayout::pad_to_align` lines 1439–1441 and 1474–1476).
- **Design question informed:** Justifies post-hoc `align(N)` size rounding of an already-rounded `#[repr(C)]` struct layout without tracking `endOffset` separately, provided alignments are powers of two.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2`, `nv_reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2`, `ce_aligned_size_drop_fields_pow2`, and `ce_aligned_size_drop_n_pow2` in `lean/Toy/Layout/Struct.lean`.
  - `Basis: normative (r[layout.properties.align], r[layout.properties.size], r[layout.repr.alignment.constraint-alignment]) + derived (modeling bridge)` — The Reference requires every alignment to be "at least 1, and always a power of 2" (line 19) and every size to be "a multiple of its alignment" (line 22), and requires every `align(x)` / `packed(x)` argument to be a power of two from 1 up to 2^29 (lines 638–639, paraphrased). Field layouts and modifiers of real Rust types therefore satisfy this card's alignment hypotheses, and its tightness counterexamples (alignments or packing arguments such as `0`, `3`, or `6`) correspond to no Rust type; they do not exhibit a Rust layout for which the conclusion fails.
  - `Basis: derived (modeling bridge)` — Applies to valid Rust `#[repr(C, align(N))]` structs via Card 8's bridge plus Rust's power-of-two alignment invariants.

#### Card 10: `repr-c-no-padding-iff-size-eq-sum` (`Toy.Layout.reprCStruct_no_padding_iff_size_eq_sum`)

- **Kind / Tier / Depth:** `characterization` | `T1` | `substantive`
- **Plain-language claim:** For any modifier `m` and field list `fields`, every byte in `0 .. (reprCStruct m fields).size` is occupied by some field (`AllBytesOccupied`) if and only if `(reprCStruct m fields).size = totalFieldSize fields`.
- **Lean statement (exact signature and unfolded `AllBytesOccupied`):**
```lean
-- lean/Toy/Layout/Struct.lean:1697-1700
theorem reprCStruct_no_padding_iff_size_eq_sum
    (m : ReprModifier) (fields : List FieldLayout) :
    AllBytesOccupied fields (reprCStruct m fields) ↔
      (reprCStruct m fields).size = totalFieldSize fields

-- Unfolded left-hand side for L := reprCStruct m fields:
--   ∀ b : Nat, b < L.size →
--     ∃ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
--       L.offsets[i] ≤ b ∧ b < L.offsets[i] + fields[i].size
```
- **Hypothesis ledger:** None (holds unconditionally for every `m` and `fields` in `Nat`, including `align = 0` and zero-sized fields).
- **Non-vacuity witness:** `Toy.Layout.nv_reprCStruct_no_padding_iff` (`m = .none`, `fields = [⟨2, 2⟩, ⟨2, 2⟩]`, `size = 4 = totalFieldSize`).
- **Non-claims:**
  - Characterizes only shallow (leading, inter-field, and trailing) struct padding; does not detect padding internal to composite fields.
  - Does not hold for non-disjoint layouts such as unions, where overlapping fields can cover every byte while `size < totalFieldSize`.
- **Prior art:** `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`, `zerocopy/src/util/macro_util.rs`, `struct_padding!` lines 319–340; related flag-propagation mechanism `DstLayout::statically_shallow_unpadded` in `zerocopy/src/layout.rs` lines 37–41, 1372–1374, 1492); `Lokathor/bytemuck` (`ea3616110b0134e9991fdb66be8892dbc427c5ac`, `derive/src/traits.rs`, `generate_assert_no_padding` lines 1078–1115); Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.c.struct.size-field-offset]` lines 247–331).
- **Design question informed:** Mechanizes the folklore scalar criterion `size_of::<T>() == Σ size_of::<F_i>()` (used in `zerocopy::struct_padding!` and `bytemuck`'s `NoUninit` derive) as both necessary and sufficient for shallow byte-by-byte occupancy in `#[repr(C)]` structs.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprCStruct_no_padding_iff_size_eq_sum` and `nv_reprCStruct_no_padding_iff` in `lean/Toy/Layout/Struct.lean`.
  - `Basis: derived (modeling bridge)` — Connects to `zerocopy::struct_padding!` (`ec133ce4` lines 319–340) and `bytemuck`'s `generate_assert_no_padding` (`ea361611` lines 1078–1115) for non-overflowing `#[repr(C)]` structs when each field type is itself known to be unpadded.

#### Card 11: `repr-c-homogeneous-no-padding-iff` (`Toy.Layout.reprCStruct_homogeneous_no_padding_iff_of_align_pos`)

- **Kind / Tier / Depth:** `characterization` | `T0` | `shallow`
- **Plain-language claim:** For any field layout `f` with positive alignment (`0 < f.align`), `∀ k, AllBytesOccupied (List.replicate k f) (reprCStruct .none (List.replicate k f))` holds (that is, the homogeneous `#[repr(C)]` structs `List.replicate k f` have no shallow padding for every `k` simultaneously) if and only if `f.align ∣ f.size` (`SizeMultipleOfAlign f`); no per-`k` biconditional is claimed.
- **Lean statement (exact signature and unfolded predicates):**
```lean
-- lean/Toy/Layout/Struct.lean:1787-1790
theorem reprCStruct_homogeneous_no_padding_iff_of_align_pos
    (f : FieldLayout) (h_pos : AlignPos f) :
    (∀ k : Nat, AllBytesOccupied (List.replicate k f) (reprCStruct .none (List.replicate k f))) ↔
      SizeMultipleOfAlign f

-- Unfolded: AlignPos f := 0 < f.align; SizeMultipleOfAlign f := f.align ∣ f.size;
-- AllBytesOccupied (List.replicate k f) L :=
--   ∀ b < L.size, ∃ (i : Nat) (hf : i < (List.replicate k f).length) (ho : i < L.offsets.length),
--     L.offsets[i] ≤ b ∧ b < L.offsets[i] + (List.replicate k f)[i].size
```
- **Supporting hashed Lean statements (`lean_names`):** `Toy.Layout.ex_homogeneous_non_dvd_has_padding`.
- **Hypothesis ledger:**
  - `h_pos` (`AlignPos f`): excludes `f.align = 0`, where `f = ⟨1, 0⟩` produces padding-free homogeneous structs for all `k` despite `¬ (0 ∣ 1)` — `tight`: counterexample `Toy.Layout.ce_homogeneous_no_padding_iff_drop_align_pos`. Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.properties.align]`).
- **Non-vacuity witness:** `Toy.Layout.nv_reprCStruct_homogeneous_no_padding_iff_of_align_pos` (`f = ⟨4, 4⟩`).
- **Non-claims:**
  - Establishes shallow padding absence only (internal padding inside `f` persists); does not extend to `#[repr(C, align(N))]` with `N > f.align` or to heterogeneous structs (Card 12).
  - At `f.align = 0`, the reverse implication holds without `AlignPos` (`0 ∣ f.size` forces `f.size = 0`), while the forward implication fails at `⟨1, 0⟩`; for positive alignments `f = ⟨3, 2⟩` exhibits padding already at `k = 1` (`Toy.Layout.ex_homogeneous_non_dvd_has_padding`).
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.properties.size]` line 22 and `r[layout.array]` line 77).
- **Design question informed:** Characterizes exactly when homogeneous `#[repr(C)]` structs introduce zero shallow padding (matching `[T; k]` array layout).
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprCStruct_homogeneous_no_padding_iff_of_align_pos`, `nv_reprCStruct_homogeneous_no_padding_iff_of_align_pos`, `ce_homogeneous_no_padding_iff_drop_align_pos`, and `ex_homogeneous_non_dvd_has_padding` in `lean/Toy/Layout/Struct.lean`.
  - `Basis: normative (r[layout.properties.align], r[layout.properties.size], r[layout.repr.alignment.constraint-alignment]) + derived (modeling bridge)` — The Reference requires every alignment to be "at least 1, and always a power of 2" (line 19) and every size to be "a multiple of its alignment" (line 22), and requires every `align(x)` / `packed(x)` argument to be a power of two from 1 up to 2^29 (lines 638–639, paraphrased). Field layouts and modifiers of real Rust types therefore satisfy this card's alignment hypotheses, and its tightness counterexamples (alignments or packing arguments such as `0`, `3`, or `6`) correspond to no Rust type; they do not exhibit a Rust layout for which the conclusion fails.
  - `Basis: derived (modeling bridge)` — Because every Rust type satisfies both `0 < align` and `align ∣ size` (`r[layout.properties.align]`, `r[layout.properties.size]`), every homogeneous `#[repr(C)]` struct of `k` identical Rust fields has zero shallow padding (`xc_07_homog`).

#### Card 12: `ce-heterogeneous-u8-u16-has-padding` (`Toy.Layout.ce_heterogeneous_u8_u16_has_padding`)

- **Kind / Tier / Depth:** `counterexample` | `T0` | `shallow`
- **Plain-language claim:** The heterogeneous `#[repr(C)]` struct `[u8, u16]` (`[⟨1, 1⟩, ⟨2, 2⟩]`) consists exclusively of well-formed fields (power-of-two alignment, size a multiple of alignment), yet has inter-field padding at byte `1` (`size = 4 ≠ 3 = totalFieldSize`).
- **Lean statement:**
```lean
-- lean/Toy/Layout/Struct.lean:1898-1905
theorem ce_heterogeneous_u8_u16_has_padding :
    let fields : List FieldLayout := [⟨1, 1⟩, ⟨2, 2⟩]
    let L := reprCStruct .none fields
    (∀ f ∈ fields, AlignPow2 f ∧ SizeMultipleOfAlign f) ∧
    ¬ AllBytesOccupied fields L ∧
    L.size = 4 ∧
    totalFieldSize fields = 3 ∧
    L.size ≠ totalFieldSize fields
```
- **Supporting hashed Lean statements (`lean_names`):** `Toy.Layout.ce_heterogeneous_u16_u8_has_trailing_padding`.
- **Hypothesis ledger:** None (concrete counterexample).
- **Non-vacuity witness:** Concrete struct `[⟨1, 1⟩, ⟨2, 2⟩]` evaluates directly to `offsets = [0, 2]`, `size = 4`, `totalFieldSize = 3`.
- **Non-claims:**
  - Does not say every heterogeneous `#[repr(C)]` struct has padding (for instance, `[u16, u8, u8]` has `size = 4 = totalFieldSize`).
  - Does not assert `#[repr(Rust)]` offset placement.
  - Dual trailing-padding witness: `[⟨2, 2⟩, ⟨1, 1⟩]` (`[u16, u8]`) has zero inter-field padding (`offsets = [0, 2]`, `endOffset = 3`) yet trailing padding at byte `3` (`size = 4 ≠ 3`, proved in `Toy.Layout.ce_heterogeneous_u16_u8_has_trailing_padding`).
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.c.struct.size-field-offset]` lines 247–353).
- **Design question informed:** Shows homogeneity cannot be dropped from Card 11 even when every field is individually well-formed (`AlignPow2` and `SizeMultipleOfAlign`).
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.ce_heterogeneous_u8_u16_has_padding` and `ce_heterogeneous_u16_u8_has_trailing_padding` in `lean/Toy/Layout/Struct.lean`.
  - `Basis: derived (modeling bridge)` — Corroborated on `rustc 1.98.0-nightly (14210df0e)` by `xc_05_u8_u16` (`U8U16`) and `xc_04_trail_pad` (`TrailPad`).

#### Card 13: `repr-c-enum-geometry` (`Toy.Layout.reprCEnum_geometry_of_vars_pow2`)

- **Kind / Tier / Depth:** `theorem` | `T1` | `substantive`
- **Plain-language claim:** For any tag layout `tag` (with no alignment hypothesis on `tag`) and any variant list `variants` whose variant fields all have power-of-two alignments, `reprCEnum tag variants` satisfies `EnumSizeValid`, `EnumVariantsValid`, and the shared-payload-union structural rule `EnumSharedPayload`.
- **Lean statement (exact signature and unfolded predicates):**
```lean
-- lean/Toy/Layout/Enum.lean:479-485
theorem reprCEnum_geometry_of_vars_pow2
    (tag : FieldLayout) (variants : List (List FieldLayout))
    (h_vars : ∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f) :
    let E := reprCEnum tag variants
    EnumSizeValid tag E ∧
    EnumVariantsValid tag variants E ∧
    EnumSharedPayload tag variants E

-- Unfolded for E := reprCEnum tag variants,
--   variantStructs := variants.map (reprCStruct .none),
--   payload := reprCUnion (variantStructs.map fun s => ⟨s.size, s.align⟩),
--   payloadOffset := alignUp tag.size payload.align:
-- h_vars : ∀ v ∈ variants, ∀ f ∈ v, ∃ k : Nat, f.align = 2 ^ k
-- Conclusion:
--   (E.align ∣ E.size ∧ tag.size ≤ E.size) ∧
--   (E.variantFieldOffsets.length = variants.length ∧
--     ∀ (k : Nat) (hk : k < variants.length) (ho : k < E.variantFieldOffsets.length),
--       let v := variants[k]; let offs := E.variantFieldOffsets[k]
--       offs.length = v.length ∧
--       (∀ (j : Nat) (hj : j < v.length) (hjo : j < offs.length),
--         tag.size ≤ offs[j] ∧ v[j].align ∣ offs[j] ∧ offs[j] + v[j].size ≤ E.size) ∧
--       (∀ (j1 j2 : Nat) (h1 : j1 < v.length) (h2 : j2 < v.length)
--          (ho1 : j1 < offs.length) (ho2 : j2 < offs.length),
--         j1 < j2 → offs[j1] + v[j1].size ≤ offs[j2])) ∧
--   (E.variantFieldOffsets = variantStructs.map (fun s => s.offsets.map (· + payloadOffset)) ∧
--     IsLeastMultipleGe E.size (payloadOffset + payload.size) E.align)
```
- **Supporting hashed Lean statements (`lean_names`):** `Toy.Layout.reprCEnum_tagOffset_zero`.
- **Hypothesis ledger:**
  - `h_vars` (`∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f`): ensures every variant field's alignment divides `payload.align` and therefore divides `payloadOffset = alignUp tag.size payload.align` (dropping it places an align-2 field at offset `3`) — `tight`: counterexample `Toy.Layout.ce_reprCEnum_geometry_drop_vars_pow2` (`tag = ⟨1, 1⟩`, `variants = [[⟨2, 2⟩], [⟨3, 3⟩]]`). Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.properties.align]`).
- **Non-vacuity witness:** `Toy.Layout.nv_reprCEnum_geometry_of_vars_pow2` (`variants = [[⟨4, 4⟩], [⟨4, 4⟩, ⟨8, 8⟩], []]`; with `cEnumTagX86_64`, offsets are `[[8], [8, 16], []]` and `size = 24`).
- **Non-claims:**
  - These theorems establish internal soundness invariants of the model (aligned, in bounds, disjoint from the tag), not that the computed offsets or sizes agree with `rustc` or the Reference beyond the construction itself. `EnumTagAtZero` holds by definition (`Toy.Layout.reprCEnum_tagOffset_zero`). Enum `align(N)` and union `packed`/`align` modifiers are not modeled.
  - `EnumSharedPayload` and `EnumPerVariantTagged` are defined from the same `reprCStruct` / `reprCUnion` construction as `reprCEnum` and `reprIntEnum`. On `reprCEnum tag variants`, the offset conjunct of `EnumSharedPayload` holds definitionally (`rfl`), reducing the predicate on its own layout to its one-step `IsLeastMultipleGe` size-rounding conjunct. They serve to distinguish `reprCEnum` and `reprIntEnum` from each other and from over-padded layouts (Card 19), not as an independent specification.
  - `EnumSizeValid ∧ EnumVariantsValid` alone do not determine `reprCEnum` (`reprIntEnum` satisfies them too). Does not establish `EnumAlignValid` (requires `AlignPow2 tag`; Card 15) and does not select a target's bare `#[repr(C)]` tag width (parameterized separately via `CEnumTarget` / `reprCEnumForTarget`; Card 18).
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.c.adt]` lines 438–499, `r[layout.repr.primitive-c]` lines 570–628); RFC 2195 (`rust-lang/rfcs` `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, `text/2195-really-tagged-unions.md` lines 303–366); `rustc_abi` (`rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `compiler/rustc_abi/src/layout.rs`, `layout_of_enum` lines 817–864; commit `4b5350e87e487aed08ab2f9f0160a4b2616438bc`, `compiler/rustc_abi/src/layout/enum_layout.rs`, `calculate_tagged_layout` lines 339–415); prose context: unmerged Aeneas PR `AeneasVerif/aeneas#1447` (`JoJoDeveloping/aeneas` `2a1dd75567517e078f90b1df746af7373fe24cbc`, `ReprC.lean` lines 86–106, `Properties.lean` lines 306–311).
- **Design question informed:** Establishes internal geometric soundness of the `struct { tag, union { variants } }` tagged-union construction under its minimal variant-field alignment hypothesis (requiring no alignment precondition on `tag`).
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprCEnum_geometry_of_vars_pow2`, `nv_reprCEnum_geometry_of_vars_pow2`, `ce_reprCEnum_geometry_drop_vars_pow2`, and `reprCEnum_tagOffset_zero` in `lean/Toy/Layout/Enum.lean`.
  - `Basis: normative (r[layout.properties.align], r[layout.properties.size], r[layout.repr.alignment.constraint-alignment]) + derived (modeling bridge)` — The Reference requires every alignment to be "at least 1, and always a power of 2" (line 19) and every size to be "a multiple of its alignment" (line 22), and requires every `align(x)` / `packed(x)` argument to be a power of two from 1 up to 2^29 (lines 638–639, paraphrased). Field layouts and modifiers of real Rust types therefore satisfy this card's alignment hypotheses, and its tightness counterexamples (alignments or packing arguments such as `0`, `3`, or `6`) correspond to no Rust type; they do not exhibit a Rust layout for which the conclusion fails.
  - `Basis: derived (modeling bridge)` — Connects to Rust `#[repr(C, Int)]` and bare `#[repr(C)]` data-carrying enums via `r[layout.repr.c.adt]` / `r[layout.repr.primitive-c]` (`c9cc3282`), RFC 2195 (`f17e8623`), `rustc_abi` (`14210df0e`), and cross-check probes `xc_15_enum_c`, `xc_16_ref_enum`, `xc_17a_enum_c_u8`, `xc_19_thumb_short_enums`, and `xc_20_hexagon_short_enums` (excluding enum `#[repr(align(N))]`, zero-variant enums, and size overflow).

#### Card 14: `repr-int-enum-geometry` (`Toy.Layout.reprIntEnum_geometry_of_nonempty_align_pos`)

- **Kind / Tier / Depth:** `theorem` | `T1` | `substantive`
- **Plain-language claim:** For any tag layout `tag` (with no alignment hypothesis on `tag`) and any non-empty variant list `variants` whose variant fields all have positive alignment (`AlignPos`), `reprIntEnum tag variants` satisfies `EnumSizeValid`, `EnumVariantsValid`, and the per-variant tag-prefix structural rule `EnumPerVariantTagged`.
- **Lean statement (exact signature and unfolded predicates):**
```lean
-- lean/Toy/Layout/Enum.lean:626-633
theorem reprIntEnum_geometry_of_nonempty_align_pos
    (tag : FieldLayout) (variants : List (List FieldLayout))
    (h_nonempty : variants ≠ [])
    (h_vars : ∀ v ∈ variants, ∀ f ∈ v, AlignPos f) :
    let E := reprIntEnum tag variants
    EnumSizeValid tag E ∧
    EnumVariantsValid tag variants E ∧
    EnumPerVariantTagged tag variants E

-- Unfolded for E := reprIntEnum tag variants,
--   variantStructs := variants.map (fun v => reprCStruct .none (tag :: v)),
--   maxVarSize := variantStructs.foldl (fun acc s => max acc s.size) 0:
-- h_vars : ∀ v ∈ variants, ∀ f ∈ v, 0 < f.align
-- Conclusion:
--   (E.align ∣ E.size ∧ tag.size ≤ E.size) ∧
--   EnumVariantsValid tag variants E ∧  -- same unfolded form as Card 13
--   (E.variantFieldOffsets = variantStructs.map (fun s => s.offsets.tail) ∧
--     IsLeastMultipleGe E.size maxVarSize E.align)
```
- **Supporting hashed Lean statements (`lean_names`):** `Toy.Layout.reprIntEnum_tagOffset_zero`, `Toy.Layout.reprIntEnum_all_variants_tag_at_zero`.
- **Hypothesis ledger:**
  - `h_nonempty` (`variants ≠ []`): ensures `tag` appears in at least one variant struct of the union so `tag.size ≤ E.size` — `tight`: counterexample `Toy.Layout.ce_reprIntEnum_geometry_drop_nonempty` (`tag = cEnumTagX86_64`, `variants = []` -> `E.size = 0 < 4 = tag.size`). Tight in the formal `Toy.Layout` model; **Rust-universal** — satisfied by every valid Rust enum that can carry `#[repr(C)]` (`r[layout.repr.c.constraint]`, lines 237–238) or `#[repr(Int)]` (`r[layout.repr.primitive.constraint]`, lines 507–508) (`Basis: normative`); `rustc` rejects zero-variant `#[repr(C)]` and primitive-representation enums with error `E0084` (`Basis: execution`, `support/e0084_zero_variant_enums_output.txt`).
  - `h_vars` (`∀ v ∈ variants, ∀ f ∈ v, AlignPos f`): requires `0 < f.align` so per-variant field offsets are multiples of `f.align` (power-of-two alignment is *not* needed for geometric placement in `reprIntEnum`) — `tight`: counterexample `Toy.Layout.ce_reprIntEnum_geometry_drop_vars_align_pos` (`tag = ⟨1, 1⟩`, `variants = [[⟨1, 0⟩]]`). Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.properties.align]`).
- **Non-vacuity witness:** `Toy.Layout.nv_reprIntEnum_geometry_of_nonempty_align_pos` (`variants = [[⟨1, 1⟩, ⟨2, 2⟩], []]`; with `u8Tag`, offsets are `[[1, 2], []]` and `size = 4`).
- **Non-claims:**
  - These theorems establish internal soundness invariants of the model (aligned, in bounds, disjoint from the tag), not that the computed offsets or sizes agree with `rustc` or the Reference beyond the construction itself. `EnumTagAtZero` holds by definition (`Toy.Layout.reprIntEnum_tagOffset_zero`, `Toy.Layout.reprIntEnum_all_variants_tag_at_zero`). Enum `align(N)` and union `packed`/`align` modifiers are not modeled.
  - `EnumSharedPayload` and `EnumPerVariantTagged` are defined from the same `reprCStruct` / `reprCUnion` construction as `reprCEnum` and `reprIntEnum`. On `reprIntEnum tag variants`, the offset conjunct of `EnumPerVariantTagged` holds definitionally (`rfl`), reducing the predicate on its own layout to its one-step `IsLeastMultipleGe` size-rounding conjunct. They serve to distinguish `reprIntEnum` and `reprCEnum` from each other and from over-padded layouts (Card 19), not as an independent specification.
  - The tightness counterexamples `ce_reprIntEnum_geometry_drop_nonempty` (`variants = []`) and `ce_reprIntEnum_geometry_drop_vars_align_pos` (field alignment `0`) do not exhibit valid Rust enums: zero-variant enums cannot carry these representations (normative and execution basis in the hypothesis ledger), and every Rust alignment is at least 1 (`r[layout.properties.align]`, `Basis: normative`).
  - Does not establish `EnumAlignValid` directly (combine Cards 15 and 16), and does not equate `reprIntEnum` with `reprCEnum` (Cards 17 and 19).
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.primitive.adt]` lines 518–568); RFC 2195 (`rust-lang/rfcs` `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, `text/2195-really-tagged-unions.md` lines 195–235); `rustc_abi` (`rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `compiler/rustc_abi/src/layout.rs`, lines 822–859; commit `4b5350e87e487aed08ab2f9f0160a4b2616438bc`, `enum_layout.rs` lines 383–395); prose context: unmerged Aeneas PR `AeneasVerif/aeneas#1447` (`JoJoDeveloping/aeneas` `2a1dd75567517e078f90b1df746af7373fe24cbc`, `ReprC.lean`, `mkEnumPrimitive` lines 108–115).
- **Design question informed:** Shows that `#[repr(Int)]`'s per-variant tag-prefix construction achieves geometric placement validity under strictly weaker field hypotheses (`AlignPos` rather than `AlignPow2`) than `reprCEnum`, provided `variants ≠ []`.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprIntEnum_geometry_of_nonempty_align_pos`, `nv_reprIntEnum_geometry_of_nonempty_align_pos`, `ce_reprIntEnum_geometry_drop_nonempty`, `ce_reprIntEnum_geometry_drop_vars_align_pos`, `reprIntEnum_tagOffset_zero`, and `reprIntEnum_all_variants_tag_at_zero` in `lean/Toy/Layout/Enum.lean`.
  - `Basis: derived (modeling bridge)` — Connects to Rust `#[repr(Int)]` data-carrying enums via `r[layout.repr.primitive.adt]` (`c9cc3282`), RFC 2195 (`f17e8623`), `rustc_abi` (`14210df0e`), and `xc_17b_enum_u8`.

#### Card 15: `repr-c-enum-align-valid` (`Toy.Layout.reprCEnum_align_valid_of_pow2`)

- **Kind / Tier / Depth:** `theorem` | `T0` | `shallow`
- **Plain-language claim:** Whenever `tag` and every field of every variant in `variants` have power-of-two alignments, `(reprCEnum tag variants).align` is a power of two divisible by `tag.align` and every variant field's alignment (`EnumAlignValid`).
- **Lean statement (exact signature and unfolded `EnumAlignValid`):**
```lean
-- lean/Toy/Layout/Enum.lean:789-793
theorem reprCEnum_align_valid_of_pow2
    (tag : FieldLayout) (variants : List (List FieldLayout))
    (h_tag : AlignPow2 tag)
    (h_vars : ∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f) :
    EnumAlignValid tag variants (reprCEnum tag variants)

-- Unfolded for E := reprCEnum tag variants:
--   (∃ k : Nat, E.align = 2 ^ k) ∧
--   tag.align ∣ E.align ∧
--   ∀ v ∈ variants, ∀ f ∈ v, f.align ∣ E.align
```
- **Supporting hashed Lean statements (`lean_names`):** `Toy.Layout.reprCEnum_tagOffset_zero`.
- **Hypothesis ledger:**
  - `h_tag` (`AlignPow2 tag`): required specifically for `EnumAlignValid` (not for geometric placement) — `tight`: counterexample `Toy.Layout.ce_reprCEnum_align_drop_tag_pow2` (`tag = ⟨3, 3⟩`, `variants = [[⟨2, 2⟩]]`). Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.properties.align]`).
  - `h_vars` (`∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f`): required for `EnumAlignValid` — `tight`: counterexample `Toy.Layout.ce_reprCEnum_align_drop_vars_pow2` (`tag = ⟨2, 2⟩`, `variants = [[⟨3, 3⟩]]`). Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.properties.align]`).
- **Non-vacuity witness:** `Toy.Layout.nv_reprCEnum_align_valid_of_pow2` (`tag = cEnumTagX86_64`, `variants = [[⟨4, 4⟩], [⟨4, 4⟩, ⟨8, 8⟩], []]`).
- **Non-claims:**
  - Establishes internal model alignment validity only; `EnumTagAtZero` holds by definition (`Toy.Layout.reprCEnum_tagOffset_zero`); enum `align(N)` and union modifiers are not modeled.
  - The tightness counterexamples use alignment `3`, which no Rust type has (`r[layout.properties.align]`, `Basis: normative`); they do not exhibit a Rust enum for which `EnumAlignValid` fails.
  - Does not by itself cover `reprIntEnum` at `variants = []` (where `reprIntEnum` gives `align = 1`); for non-empty `variants`, Card 16 transfers `EnumAlignValid` directly to `reprIntEnum`, and every Rust enum carrying these representations has `variants ≠ []` (`Basis: normative`: `r[layout.repr.c.constraint]`, `r[layout.repr.primitive.constraint]`; `Basis: execution`: error `E0084`, `support/e0084_zero_variant_enums_output.txt`).
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.properties.align]` line 19, `r[layout.repr.c.adt]` lines 438–499); RFC 2195 (`rust-lang/rfcs` `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, `text/2195-really-tagged-unions.md` lines 303–366); prose context: unmerged Aeneas PR `AeneasVerif/aeneas#1447` (`JoJoDeveloping/aeneas` `2a1dd75567517e078f90b1df746af7373fe24cbc`, `Properties.lean`, `mkEnum_reasonablyAligned` lines 306–311).
- **Design question informed:** Separates power-of-two alignment divisibility (`EnumAlignValid`, needing `AlignPow2` on both `tag` and variant fields) from the weaker geometric placement preconditions of Cards 13 and 14.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprCEnum_align_valid_of_pow2`, `nv_reprCEnum_align_valid_of_pow2`, `ce_reprCEnum_align_drop_tag_pow2`, `ce_reprCEnum_align_drop_vars_pow2`, and `reprCEnum_tagOffset_zero` in `lean/Toy/Layout/Enum.lean`.
  - `Basis: derived (modeling bridge)` — Within the modeled fragment (targets with `aggregate_align = 1`, non-overflowing sizes, no enum `align(N)`) and under the premise stated in Card 16's bridge (the Reference defines these layouts as the compositions that `reprCEnum` implements), the result applies to Rust `#[repr(C)]` and `#[repr(C, Int)]` enums, because every Rust tag and variant field has a power-of-two alignment (`r[layout.properties.align]`, line 19, `Basis: normative`).

#### Card 16: `repr-int-enum-align-eq-repr-c-enum` (`Toy.Layout.reprIntEnum_align_eq_reprCEnum_align_of_nonempty`)

- **Kind / Tier / Depth:** `theorem` | `T1` | `shallow`
- **Plain-language claim:** For any tag layout `tag` and any non-empty variant list `variants` (without requiring power-of-two alignments), `(reprIntEnum tag variants).align = (reprCEnum tag variants).align`.
- **Lean statement:**
```lean
-- lean/Toy/Layout/Enum.lean:871-874
theorem reprIntEnum_align_eq_reprCEnum_align_of_nonempty
    (tag : FieldLayout) (variants : List (List FieldLayout))
    (h_nonempty : variants ≠ []) :
    (reprIntEnum tag variants).align = (reprCEnum tag variants).align
```
- **Hypothesis ledger:**
  - `h_nonempty` (`variants ≠ []`): ensures `tag.align` enters the per-variant struct alignment maximum in `reprIntEnum` — `tight`: counterexample `Toy.Layout.ce_reprIntEnum_align_eq_drop_nonempty` (`tag = cEnumTagX86_64`, `variants = []` -> `1 ≠ 4`). Tight in the formal `Toy.Layout` model; **Rust-universal** — satisfied by every valid Rust enum that can carry `#[repr(C)]` (`r[layout.repr.c.constraint]`, lines 237–238) or `#[repr(Int)]` (`r[layout.repr.primitive.constraint]`, lines 507–508) (`Basis: normative`); `rustc` rejects zero-variant `#[repr(C)]` and primitive-representation enums with error `E0084` (`Basis: execution`, `support/e0084_zero_variant_enums_output.txt`).
- **Non-vacuity witness:** `Toy.Layout.nv_reprIntEnum_align_eq_reprCEnum_align_of_nonempty` (`variants = [[⟨1, 1⟩, ⟨2, 2⟩], []]`).
- **Non-claims:**
  - Asserts equality of overall alignment only, not equality of total size or variant field offsets (Card 19 shows `size = 4 < 6` at equal `align = 2`).
  - Fails in the model when `variants = []` and `tag.align > 1` (`ce_reprIntEnum_align_eq_drop_nonempty`), which exhibits no valid Rust enum (zero-variant enums cannot carry these representations; normative and execution basis in the hypothesis ledger).
  - Compares identical `tag` layouts (`#[repr(Int)]` vs. `#[repr(C, Int)]`), not bare `#[repr(C)]` with a different target tag width, and does not model `#[repr(align(N))]` on enums.
- **Prior art:** Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.primitive.adt]` lines 518–568, `r[layout.repr.primitive-c]` lines 570–628); RFC 2195 (`rust-lang/rfcs` `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, `text/2195-really-tagged-unions.md` lines 195–366).
- **Design question informed:** Establishes that `#[repr(Int)]` and `#[repr(C, Int)]` share identical overall alignment on all non-empty enums without requiring power-of-two alignments.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprIntEnum_align_eq_reprCEnum_align_of_nonempty`, `nv_reprIntEnum_align_eq_reprCEnum_align_of_nonempty`, and `ce_reprIntEnum_align_eq_drop_nonempty` in `lean/Toy/Layout/Enum.lean`.
  - `Basis: derived (modeling bridge)` — Scope: only within the modeled fragment (targets with `aggregate_align = 1`, non-overflowing sizes, no enum `align(N)`), and only for a `#[repr(Int)]` and a `#[repr(C, Int)]` enum with the same tag layout. Premise (a reading of the normative text, not proved in Lean): the Reference defines a `#[repr(Int)]` enum with fields as "a `repr(C)` union of `repr(C)` structs for each variant with a field" whose first field is the tag (`r[layout.repr.primitive.adt]`, line 521), and a `#[repr(C, Int)]` enum with fields as a `repr(C)` struct of the tag and "a `repr(C)` union of `repr(C)` structs for the fields of each variant that had them" (`r[layout.repr.c.adt]`, lines 441–447, with the tag changed to the primitive by `r[layout.repr.primitive-c]`, line 573); `reprIntEnum` and `reprCEnum` implement these compositions with `reprCStruct` (modeling `r[layout.repr.c.struct]`) and `reprCUnion` (modeling `r[layout.repr.c.union.size-align]`); they also include a struct for each field-less variant (tag only, or empty), which for Rust tag layouts cannot raise the union's maximum size or alignment when some variant has fields. Under that premise the alignment equality transfers. The hypothesis `variants ≠ []` holds for every Rust enum with these representations (normative and execution basis in the hypothesis ledger). Execution corroboration is limited to probes `xc_17a_enum_c_u8` and `xc_17b_enum_u8` (both `align = 2`).

#### Card 17: `repr-int-enum-size-le-repr-c-enum-size` (`Toy.Layout.reprIntEnum_size_le_reprCEnum_size_of_pow2`)

- **Kind / Tier / Depth:** `theorem` | `T1` | `substantive`
- **Plain-language claim:** For any tag layout `tag` and variant list `variants` with power-of-two alignments everywhere, `(reprIntEnum tag variants).size ≤ (reprCEnum tag variants).size`.
- **Lean statement (exact signature and unfolded `AlignPow2`):**
```lean
-- lean/Toy/Layout/Enum.lean:967-971
theorem reprIntEnum_size_le_reprCEnum_size_of_pow2
    (tag : FieldLayout) (variants : List (List FieldLayout))
    (h_tag : AlignPow2 tag)
    (h_vars : ∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f) :
    (reprIntEnum tag variants).size ≤ (reprCEnum tag variants).size

-- Unfolded: h_tag : ∃ k : Nat, tag.align = 2 ^ k;
-- h_vars : ∀ v ∈ variants, ∀ f ∈ v, ∃ k : Nat, f.align = 2 ^ k.
```
- **Hypothesis ledger:**
  - `h_tag` (`AlignPow2 tag`): prevents coprime per-variant struct alignment rounding from overshooting `reprCEnum`'s size — `tight`: counterexample `Toy.Layout.ce_reprInt_le_reprC_drop_tag_pow2` (`tag = ⟨3, 3⟩`, `variants = [[⟨4, 4⟩], [⟨4, 2⟩]]` -> `12 > 8`). Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.properties.align]`).
  - `h_vars` (`∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f`): ensures every variant field alignment divides `payloadOffset` in `reprCEnum`, making `reprCEnum`'s shifted layout an upper bound on `reprIntEnum`'s packed-after-tag layout — `tight`: counterexample `Toy.Layout.ce_reprInt_le_reprC_drop_vars_pow2` (`tag = ⟨3, 1⟩`, `variants = [[⟨6, 2⟩], [⟨0, 3⟩]]` -> `12 > 9`). Tight in the toy (`Nat`) domain; Rust-universal (`r[layout.properties.align]`).
- **Non-vacuity witness:** `Toy.Layout.nv_reprIntEnum_size_le_reprCEnum_size_of_pow2` (`tag = u8Tag`, `variants = [[⟨1, 1⟩, ⟨2, 2⟩], []]`).
- **Non-claims:**
  - The tightness counterexamples (alignment `3` for the tag or a variant field) show only that the inequality can fail in `Nat` without the power-of-two hypotheses; they do not exhibit a Rust enum for which the `#[repr(Int)]` layout is larger than the `#[repr(C, Int)]` layout, since no Rust type has alignment `3`. The theorem also does not say that the `#[repr(Int)]` layout is strictly smaller in general; equality is common.
  - Compares identical `tag` layouts (`#[repr(Int)]` vs. `#[repr(C, Int)]`), not bare `#[repr(C)]` with a wider or narrower tag. Alignment equality requires `variants ≠ []` (Card 16).
- **Prior art:** RFC 2195 (`rust-lang/rfcs` `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, `text/2195-really-tagged-unions.md` line 408: *"`repr(Int)` should be preferred by default over `repr(C, Int)` as it has a strictly superior space-usage"*); Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.primitive-c]` note lines 575–577).
- **Design question informed:** Mechanizes RFC 2195's informal space-usage remark as an exact formal size ordering `(reprIntEnum tag variants).size ≤ (reprCEnum tag variants).size` and pinpoints why power-of-two divisibility is essential to the inequality.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.reprIntEnum_size_le_reprCEnum_size_of_pow2`, `nv_reprIntEnum_size_le_reprCEnum_size_of_pow2`, `ce_reprInt_le_reprC_drop_tag_pow2`, and `ce_reprInt_le_reprC_drop_vars_pow2` in `lean/Toy/Layout/Enum.lean`.
  - `Basis: normative (r[layout.properties.align], r[layout.properties.size], r[layout.repr.alignment.constraint-alignment]) + derived (modeling bridge)` — The Reference requires every alignment to be "at least 1, and always a power of 2" (line 19) and every size to be "a multiple of its alignment" (line 22), and requires every `align(x)` / `packed(x)` argument to be a power of two from 1 up to 2^29 (lines 638–639, paraphrased). Field layouts and modifiers of real Rust types therefore satisfy this card's alignment hypotheses, and its tightness counterexamples (alignments or packing arguments such as `0`, `3`, or `6`) correspond to no Rust type; they do not exhibit a Rust layout for which the conclusion fails.
  - `Basis: derived (modeling bridge)` — Scope: only within the modeled fragment (targets with `aggregate_align = 1`, non-overflowing sizes, no enum `align(N)`), and only for a `#[repr(Int)]` and a `#[repr(C, Int)]` enum with the same tag layout. Premise: the same reading of `r[layout.repr.primitive.adt]`, `r[layout.repr.c.adt]`, and `r[layout.repr.primitive-c]` as in Card 16's bridge (not proved in Lean), under which `reprIntEnum` and `reprCEnum` are the Reference's layouts. The power-of-two hypotheses hold for every Rust tag and field (normative basis above). Under that premise the size inequality transfers. Execution corroboration is limited to probes `xc_17a_enum_c_u8` (`size = 6`) and `xc_17b_enum_u8` (`size = 4`).

#### Card 18: `ce-repr-c-enum-tag-sizing-targets` (`Toy.Layout.ce_reprCEnum_tag_sizing_divergence`)

- **Kind / Tier / Depth:** `counterexample` | `T0` | `shallow`
- **Plain-language claim:** In the target-parameterized `reprCEnumForTarget` model, neither a pointer-sized tag (`usizeTag64`) nor a fixed 4-byte `c_int` tag (`cIntLayout32Bit`) matches across targets and discriminant ranges: for `[[⟨1, 1⟩], []]` with discriminants `[0, 1]`, `targetX86_64Linux` (`cEnumMinBytes = 4`) gives `size = 8, align = 4` versus `size = 16, align = 8` for `usizeTag64`, while `targetThumbV7mNoneEabi` and `targetHexagonNoneElf` (`cEnumMinBytes = 1`) give `size = 2, align = 1` versus `size = 8, align = 4` for `cIntLayout32Bit`; and for field-less `[[], []]` with discriminants `[0x1_0000_0000, 0x1_0000_0001]` (which do not fit in 32 bits) on `targetX86_64Linux`, `reprCEnumForTarget` gives `size = 8, align = 8` versus `size = 4, align = 4` for `cIntLayout32Bit` (`ce_reprCEnum_tag_sizing_divergence` proves all size equalities, size inequalities, and the `targetX86_64Linux`, `usizeTag64`, and `targetThumbV7mNoneEabi` alignments; `ce_reprCEnum_tag_sizing_divergence_aligns` proves `align = 1` on `targetHexagonNoneElf` and `align = 4` for `cIntLayout32Bit` on both variant lists).
- **Lean statements (`execution (Lean kernel check)` — main theorem and supporting alignment theorem):**
```lean
-- lean/Toy/Layout/Enum.lean:1121-1140
theorem ce_reprCEnum_tag_sizing_divergence :
    let enumC_variants : List (List FieldLayout) := [[⟨1, 1⟩], []]
    let fieldless_variants : List (List FieldLayout) := [[], []]
    (reprCEnumForTarget targetX86_64Linux 0 1 enumC_variants).size = 8 ∧
    (reprCEnumForTarget targetX86_64Linux 0 1 enumC_variants).align = 4 ∧
    (reprCEnum usizeTag64 enumC_variants).size = 16 ∧
    (reprCEnum usizeTag64 enumC_variants).align = 8 ∧
    (reprCEnumForTarget targetX86_64Linux 0 1 enumC_variants).size ≠
      (reprCEnum usizeTag64 enumC_variants).size ∧
    (reprCEnumForTarget targetThumbV7mNoneEabi 0 1 enumC_variants).size = 2 ∧
    (reprCEnumForTarget targetThumbV7mNoneEabi 0 1 enumC_variants).align = 1 ∧
    (reprCEnumForTarget targetHexagonNoneElf 0 1 enumC_variants).size = 2 ∧
    (reprCEnum cIntLayout32Bit enumC_variants).size = 8 ∧
    (reprCEnumForTarget targetThumbV7mNoneEabi 0 1 enumC_variants).size ≠
      (reprCEnum cIntLayout32Bit enumC_variants).size ∧
    (reprCEnumForTarget targetX86_64Linux 0x100000000 0x100000001 fieldless_variants).size = 8 ∧
    (reprCEnumForTarget targetX86_64Linux 0x100000000 0x100000001 fieldless_variants).align = 8 ∧
    (reprCEnum cIntLayout32Bit fieldless_variants).size = 4 ∧
    (reprCEnumForTarget targetX86_64Linux 0x100000000 0x100000001 fieldless_variants).size ≠
      (reprCEnum cIntLayout32Bit fieldless_variants).size

-- lean/Toy/Layout/Enum.lean:1147-1152
theorem ce_reprCEnum_tag_sizing_divergence_aligns :
    let enumC_variants : List (List FieldLayout) := [[⟨1, 1⟩], []]
    let fieldless_variants : List (List FieldLayout) := [[], []]
    (reprCEnumForTarget targetHexagonNoneElf 0 1 enumC_variants).align = 1 ∧
    (reprCEnum cIntLayout32Bit enumC_variants).align = 4 ∧
    (reprCEnum cIntLayout32Bit fieldless_variants).align = 4
```
- **Supporting hashed Lean statements (`lean_names`):** `Toy.Layout.ce_reprCEnum_tag_sizing_divergence_aligns`.
- **Hypothesis ledger:** None (concrete counterexample).
- **Non-vacuity witness:** Direct kernel evaluation on `targetX86_64Linux`, `targetThumbV7mNoneEabi`, and `targetHexagonNoneElf`, corroborated empirically via `xc_14_fieldless_c_enum`, `xc_14b_fieldless_c_enum_big_discr`, `xc_15_enum_c`, `xc_19_thumb_short_enums`, and `xc_20_hexagon_short_enums`.
- **Non-claims:**
  - (`Basis: normative`.) The Rust Reference does not specify a `c_int`-sized tag. It specifies the size and alignment of *"a C enum with the same discriminant values and no fixed underlying type"*, calls this a *"best guess"*, and marks the size of `EnumC` as platform dependent. The `c_int` equality appears only in an example for `target_arch = "x86_64"`.
  - Small-discriminant witness against the `c_int` heuristic (`Basis: source + execution`): not every target gives a bare `#[repr(C)]` enum whose discriminants fit in C `int` a `c_int`-sized tag. In `rustc` at `14210df0e`, `discr_range_of_repr` (`compiler/rustc_middle/src/ty/layout.rs` lines 77–120) uses the larger of the target's `c_enum_min_size` and the smallest integer fitting the discriminants; `c_enum_min_size` is `c_enum_min_bits.unwrap_or(c_int_width)` (`compiler/rustc_target/src/spec/mod.rs` lines 2190–2191); and `c_enum_min_bits: Some(8)` is set in the `arm_none` target base (`compiler/rustc_target/src/spec/base/arm_none.rs` line 29) and for `hexagon-unknown-none-elf` (`compiler/rustc_target/src/spec/targets/hexagon_unknown_none_elf.rs` line 31). On `thumbv7m-none-eabi` and `hexagon-unknown-none-elf`, `rustc 1.98.0-nightly (14210df0e)` reports `"c-enum-min-bits": 8` and accepts compile-time assertions that `EnumC` has `size = 2, align = 1` (`support/crosscheck_short_enum_output.txt`; reproduced on `rustc 1.102.0-nightly (3ef0c22cd)`). On `x86_64-unknown-linux-gnu`, the field-less enum with discriminants `0, 1` has the size and alignment of 4-byte `c_int` (`support/crosscheck_output.txt`, probes `14` and `15`).
  - Status of the large-discriminant witness (`Basis: normative + source + execution`): the Reference requires the discriminants of a field-less `#[repr(C)]` enum to be all representable by C `int` or all by `unsigned int` (`r[layout.repr.c.enum.discriminant]`, line 402) and notes: "`rustc` accepts enums whose discriminant values do not meet this requirement but lints against them. This will become an error in the future." (line 408). In `rustc` at `14210df0e`, the lint `REPR_C_ENUMS_LARGER_THAN_INT` is declared with level `Warn` and future-incompatibility reason `FutureReleaseError` (`compiler/rustc_lint_defs/src/builtin.rs` lines 5395–5441, tracking issue `rust-lang/rust#124403`), a reason documented as "This will be an error in a future release for all editions" (`compiler/rustc_lint_defs/src/lib.rs` line 361). Both recorded compilers accept such an enum with this warning (`support/repr_c_big_discriminant_lint.rs`, `support/repr_c_big_discriminant_lint_output.txt`). With the lint allowed, probe `14b` (`FieldlessCBigDiscr`, discriminants `0x1_0000_0000` and `0x1_0000_0001`) has `size = 8, align = 8` (`support/crosscheck_output.txt`). These sources state an intent to make the lint an error; this package makes no claim about when or whether that happens.
  - Exact division of labor between the two Lean theorems: `Toy.Layout.ce_reprCEnum_tag_sizing_divergence` proves all size values, size inequalities, and the alignments for `targetX86_64Linux`, `usizeTag64`, and `targetThumbV7mNoneEabi`; `Toy.Layout.ce_reprCEnum_tag_sizing_divergence_aligns` proves the remaining three alignments (`align = 1` on `targetHexagonNoneElf` for `enumC_variants`, and `align = 4` for `cIntLayout32Bit` on `enumC_variants` and `fieldless_variants`).
  - Does not establish anything about released Aeneas versions: the pointer-sized default `reprC_default_tag_ty := .unsigned .Usize` is in an open, unmerged pull request (`AeneasVerif/aeneas#1447`) at commit `2a1dd75567517e078f90b1df746af7373fe24cbc`.
- **Prior art:**
  - Rust Reference (`rust-lang/reference` commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`), verbatim rules:
    - `r[layout.repr.c.enum.discriminant]` (line 402): *"For a field-less enum with the `C` representation, the discriminant values must either all be representable by the `int` type in the target platform's C ABI or all be representable by its `unsigned int` type."* Note (line 408): *"`rustc` accepts enums whose discriminant values do not meet this requirement but lints against them. This will become an error in the future."*
    - `r[layout.repr.c.enum.size-align]` (line 411): *"A field-less enum with the `C` representation has the same size and alignment as a C enum with the same discriminant values and no fixed underlying type."* (`c_int` equality appears only inside `#[cfg(target_arch = "x86_64")]` at lines 422–426; note at lines 429–430: *"The enum representation in C is implementation defined, so this is really a "best guess". In particular, this may be incorrect when the C code of interest is compiled with certain flags."*)
    - `r[layout.repr.c.adt.intro]` / `.tag` / `.fields` (lines 441–447, verbatim):
      > The representation of a `repr(C)` enum with fields is a `repr(C)` struct with two fields, also called a "tagged union" in C:
      > - a `repr(C)` version of the enum with all fields removed ("the tag")
      > - a `repr(C)` union of `repr(C)` structs for the fields of each variant that had them ("the payload")
    - `r[layout.repr.primitive-c]` `EnumC` example (lines 621–622): `// The size of the C representation is platform dependent` followed by `assert_eq!(std::mem::size_of::<EnumC>(), 8);`.
  - RFC 2195 (`rust-lang/rfcs` `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, `text/2195-really-tagged-unions.md` line 365 *"whatever size C enums default to"*, line 437 *"Rust has to basically guess at the type of a `repr(C)` enum anyway"*).
  - `rustc` implementation (`rust-lang/rust` executed commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, also verified at `4b5350e87e487aed08ab2f9f0160a4b2616438bc`): `compiler/rustc_middle/src/ty/layout.rs` `discr_range_of_repr` (lines 77–120 at `14210df0e`, lines 78–130 at `4b5350e8`), `compiler/rustc_target/src/spec/mod.rs` (`c_enum_min_size = c_enum_min_bits.unwrap_or(c_int_width)`, lines 2190–2191 at `14210df0e`, lines 2078–2079 at `4b5350e8`), `compiler/rustc_target/src/spec/base/arm_none.rs` (`c_enum_min_bits: Some(8)`, line 29), `compiler/rustc_target/src/spec/targets/hexagon_unknown_none_elf.rs` (`c_enum_min_bits: Some(8)`, line 31), `compiler/rustc_lint_defs/src/builtin.rs` (`REPR_C_ENUMS_LARGER_THAN_INT`: declaration lines 5395–5441, lint-list entry line 94, at `14210df0e`; tracking issue `rust-lang/rust#124403`), and `compiler/rustc_lint_defs/src/lib.rs` (`FutureIncompatibilityReason::FutureReleaseError`, lines 360–375 at `14210df0e`).
  - Prose context: unmerged Aeneas PR `AeneasVerif/aeneas#1447` (`JoJoDeveloping/aeneas` `2a1dd75567517e078f90b1df746af7373fe24cbc`, `ReprC.lean` line 103, `Properties.lean` lines 108 and 124).
- **Design question informed:** Demonstrates why bare `#[repr(C)]` enum tags must be parameterized by target `c_enum_min_size` and discriminant range (`CEnumTarget`), rather than hardcoded to pointer width (`usize`) or 4-byte `c_int`.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.ce_reprCEnum_tag_sizing_divergence` and `Toy.Layout.ce_reprCEnum_tag_sizing_divergence_aligns` in `lean/Toy/Layout/Enum.lean` establish the arithmetic values and inequalities inside `Toy.Layout`.
  - `Basis: derived (modeling bridge)` — Normative specification (`rust-lang/reference` `c9cc3282` lines 402–447, 621–622) + compiler source (`rust-lang/rust` `14210df0e`, `discr_range_of_repr` lines 77–120, `arm_none.rs` line 29, `hexagon_unknown_none_elf.rs` line 31, `builtin.rs` lines 5395–5441) + execution on `rustc 1.98.0-nightly (14210df0e)`, reproduced on `rustc 1.102.0-nightly (3ef0c22cd)` (`support/crosscheck_output.txt` probes `14`, `14b`, `15`; `support/crosscheck_short_enum_output.txt` on `thumbv7m-none-eabi` and `hexagon-unknown-none-elf`, including the E0308 negative control; `support/repr_c_big_discriminant_lint_output.txt`). The model's `targetX86_64Linux`, `targetThumbV7mNoneEabi`, and `targetHexagonNoneElf` values reproduce these observed sizes and alignments on the probed enums.

#### Card 19: `ce-repr-int-strictly-smaller-than-repr-c-u8` (`Toy.Layout.ce_reprIntEnum_lt_reprCEnum_u8`)

- **Kind / Tier / Depth:** `counterexample` | `T0` | `shallow`
- **Plain-language claim:** On `variants = [[⟨1, 1⟩, ⟨2, 2⟩], []]` with a 1-byte tag `u8Tag`, `reprIntEnum` gives `size = 4` and offsets `[[1, 2], []]`, strictly smaller than `reprCEnum`'s `size = 6` and offsets `[[2, 4], []]`; moreover `EnumSharedPayload` rejects the `reprIntEnum` layout and `EnumPerVariantTagged` rejects the `reprCEnum` layout.
- **Lean statement:**
```lean
-- lean/Toy/Layout/Enum.lean:1159-1167
theorem ce_reprIntEnum_lt_reprCEnum_u8 :
    let variants : List (List FieldLayout) := [[⟨1, 1⟩, ⟨2, 2⟩], []]
    (reprIntEnum u8Tag variants).size = 4 ∧
    (reprIntEnum u8Tag variants).variantFieldOffsets = [[1, 2], []] ∧
    (reprCEnum u8Tag variants).size = 6 ∧
    (reprCEnum u8Tag variants).variantFieldOffsets = [[2, 4], []] ∧
    (reprIntEnum u8Tag variants).size < (reprCEnum u8Tag variants).size ∧
    ¬ EnumSharedPayload u8Tag variants (reprIntEnum u8Tag variants) ∧
    ¬ EnumPerVariantTagged u8Tag variants (reprCEnum u8Tag variants)
```
- **Hypothesis ledger:** None (concrete counterexample).
- **Non-vacuity witness:** Direct kernel evaluation on `u8Tag` and `[[⟨1, 1⟩, ⟨2, 2⟩], []]`.
- **Non-claims:**
  - Does not claim `reprIntEnum` is always strictly smaller than `reprCEnum` for the same tag; equality holds whenever no variant has a leading field narrow enough to pack into the alignment gap after `tag`.
  - `EnumSharedPayload` and `EnumPerVariantTagged` are defined from the same `reprCStruct` / `reprCUnion` construction as `reprCEnum` and `reprIntEnum` (so their offset conjuncts hold by `rfl` on their own layouts in Cards 13 and 14); the genuine cross-layout separation content is witnessed here by each predicate rejecting the opposite representation's concrete layout.
- **Prior art:** RFC 2195 (`rust-lang/rfcs` `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, `text/2195-really-tagged-unions.md` lines 257–300: `TwoCases { A(u8, u16), B(u16) }`, 4 bytes under `#[repr(u8)]` vs. 6 bytes under `(tag, union)`); Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.repr.primitive-c]` note lines 575–577).
- **Design question informed:** Witnesses strict separation between `#[repr(Int)]` and `#[repr(C, Int)]` in total size, payload field offsets, and the structural predicates `EnumSharedPayload` vs. `EnumPerVariantTagged`.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.ce_reprIntEnum_lt_reprCEnum_u8` in `lean/Toy/Layout/Enum.lean`.
  - `Basis: derived (modeling bridge)` — Matches `rustc 1.98.0-nightly (14210df0e)` on `EnumCU8` (`size = 6, align = 2, offsets = [2, 4]`, `xc_17a_enum_c_u8`) and `EnumU8` (`size = 4, align = 2, offsets = [1, 2]`, `xc_17b_enum_u8`).

#### Card 20: `dst-instantiated-eq-closed-form` (`Toy.Layout.dstInstantiated_eq_closed_form`)

- **Kind / Tier / Depth:** `theorem` | `T0` | `shallow`
- **Plain-language claim:** For any flat `#[repr(C)]` slice-tailed DST specification `d` and trailing element count `n`, instantiating the trailing slice `[T]` as `[T; n]` yields alignment `dstAlign d`, size `dstSize d n = alignUp (dstTailOffset d + n * d.elem.size) (dstAlign d)`, and offsets equal to the head offsets followed by `dstTailOffset d`.
- **Lean statement:**
```lean
-- lean/Toy/Layout/Dst.lean:179-183
theorem dstInstantiated_eq_closed_form (d : SliceDstSpec) (n : Nat) :
    (dstInstantiated d n).align = dstAlign d ∧
    (dstInstantiated d n).size = dstSize d n ∧
    (dstInstantiated d n).offsets =
      (placeFields d.modifier 0 d.headFields).1 ++ [dstTailOffset d]
```
- **Hypothesis ledger:** None (holds unconditionally for every `SliceDstSpec` and `n : Nat`).
- **Non-vacuity witness:** `Toy.Layout.nv_dstInstantiated_eq_closed_form` (`d = ⟨.none, [⟨4, 4⟩, ⟨1, 1⟩], ⟨2, 2⟩⟩`, `n = 3` -> `offsets = [0, 4, 6]`, `align = 4`, `size = 12`).
- **Non-claims:**
  - The Rust Reference does not explicitly state the size of a `repr(C)` struct with an unsized tail. The closed form applies the `repr(C)` algorithm per value, with slice and array layout; this is the reading used by `zerocopy` and MiniRust, and the execution cross-check corroborates it (`xc_18a`–`xc_18f`).
  - Does not model nested DST fields wrapped inside an outer `#[repr(packed(N))]` struct whose inner rounding alignment exceeds the outer struct's alignment (`TrailingSliceLayout` in `google/zerocopy`, `zerocopy/src/layout.rs` lines 196–206).
  - Does not model trait-object (`dyn Trait`) DSTs or Rust's drop-glue restriction on generic `?Sized` tails in `#[repr(packed)]` structs.
- **Prior art:** MiniRust (`minirust/minirust` `063d784186d3252bee242217f218223205c0b568`, `spec/lang/types.md`, `TupleHeadLayout::{tail_offset, full_size_and_align}` lines 200–225 and `LayoutStrategy::compute_size_and_align` lines 259–277); Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`, `r[layout.array]` line 77, `r[layout.slice]` line 82, `r[layout.repr.c.struct.size-field-offset]` lines 246–253); `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`, `zerocopy/src/layout.rs`, `DstLayout::extend` and `DstLayout::pad_to_align` lines 1199–1495, test model `size_for_metadata_model` lines 2409–2473).
- **Design question informed:** Reduces dynamic layout evaluation for flat slice-tailed `#[repr(C)]` structs to three static quantities (`dstTailOffset d`, `dstAlign d`, `d.elem.size`) plus one `alignUp`.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.dstInstantiated_eq_closed_form` and `nv_dstInstantiated_eq_closed_form` in `lean/Toy/Layout/Dst.lean`.
  - `Basis: derived (modeling bridge)` — Matches `core::mem::size_of_val` and `align_of_val` on `rustc 1.98.0-nightly (14210df0e)` across 6 flat DST families (`xc_18a`–`xc_18f`), MiniRust's `TupleHeadLayout::full_size_and_align` (`063d7841`), and `zerocopy`'s `size_for_metadata_model` (`ec133ce4`) for flat non-overflowing `#[repr(C)]` slice DSTs.

#### Card 21: `max-slice-elems-some-iff` (`Toy.Layout.maxSliceElems_some_iff`)

- **Kind / Tier / Depth:** `characterization` | `T1` | `substantive`
- **Plain-language claim:** For any flat `SliceDstSpec` `d`, buffer length `bufferLen`, and count `n`, `maxSliceElems d bufferLen = some n` if and only if `n` is the greatest natural number satisfying `dstSize d n ≤ bufferLen` (`IsMaxFittingElems d bufferLen n`).
- **Lean statement (exact signature and unfolded `IsMaxFittingElems`):**
```lean
-- lean/Toy/Layout/Dst.lean:224-225
theorem maxSliceElems_some_iff (d : SliceDstSpec) (bufferLen n : Nat) :
    maxSliceElems d bufferLen = some n ↔ IsMaxFittingElems d bufferLen n

-- Unfolded right-hand side:
--   dstSize d n ≤ bufferLen ∧ ∀ k : Nat, dstSize d k ≤ bufferLen → k ≤ n
```
- **Supporting hashed Lean statements (`lean_names`):** `Toy.Layout.dstSize_eq_phase_normal_form`, `Toy.Layout.maxSliceElems_eq_phase_normal_form_capacity`, `Toy.Layout.dstSize_eq_unphased_normal_form_of_dvd` (in `lean/Toy/Layout/Dst.lean`; they restate `dstSize` and `maxSliceElems` in the normal form used by the bridge bullet below):
```lean
-- lean/Toy/Layout/Dst.lean:620-623
theorem dstSize_eq_phase_normal_form (d : SliceDstSpec) (n : Nat) :
    dstSize d n =
      (dstTailOffset d - dstTailOffset d % dstAlign d) +
        alignUp (dstTailOffset d % dstAlign d + n * d.elem.size) (dstAlign d)

-- lean/Toy/Layout/Dst.lean:645-652
theorem maxSliceElems_eq_phase_normal_form_capacity (d : SliceDstSpec) (bufferLen : Nat)
    (h_elem : 0 < d.elem.size) :
    maxSliceElems d bufferLen =
      if bufferLen < dstTailOffset d - dstTailOffset d % dstAlign d then none
      else if roundDown (bufferLen - (dstTailOffset d - dstTailOffset d % dstAlign d))
          (dstAlign d) < dstTailOffset d % dstAlign d then none
      else some ((roundDown (bufferLen - (dstTailOffset d - dstTailOffset d % dstAlign d))
          (dstAlign d) - dstTailOffset d % dstAlign d) / d.elem.size)

-- lean/Toy/Layout/Dst.lean:687-690
theorem dstSize_eq_unphased_normal_form_of_dvd (d : SliceDstSpec) (n : Nat)
    (h_align_dvd : dstAlign d ∣ d.elem.size) (h_elem_dvd : d.elem.align ∣ d.elem.size) :
    dstSize d n =
      alignUp (dstTailOffset d) (dstAlign d) + alignUp (0 + n * d.elem.size) d.elem.align
```
- **Hypothesis ledger:** None (holds unconditionally over `Nat`; when `d.elem.size = 0`, both sides are `False` by `maxSliceElems` definition and Card 23).
- **Non-vacuity witness:** `Toy.Layout.nv_maxSliceElems_some_iff` (`d = ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩`, `bufferLen = 5`, `n = 1`).
- **Non-claims:**
  - The correspondence with `zerocopy` stated in the bridge bullet below is established only for flat `#[repr(C)]` slice DSTs whose element alignment does not exceed `dstAlign d`, with a positive element size, an address-aligned prefix cast, and no overflow; other cases are not established here. `zerocopy`'s `DstLayout` is a doc-hidden internal type (`#[doc(hidden)] pub struct DstLayout`), and `validate_cast_and_convert_metadata` is crate-private (`pub(crate) const fn`). `zerocopy`'s rounding alignment can exceed the type's alignment under `packed(N)` (for nested DSTs, and for a flat trailing slice whose element alignment exceeds `N`); `zerocopy` also panics on zero-sized elements, checks address alignment first, and handles suffix casts.
  - Does not model finite-precision `usize` or `isize::MAX` overflow checks (`zerocopy`'s Kani harnesses verify the more general bit-precise normalized form `TrailingSliceLayout`).
- **Prior art:** `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`, `zerocopy/src/layout.rs`): internal `#[doc(hidden)] pub struct DstLayout` (lines 19–42), normalized `TrailingSliceLayout` `(size_base, size_align, size_phase)` (lines 150–207), `max_trailing_bytes` (lines 236–341), `max_elems_for_bytes` contract (lines 827–859), `pub(crate) const fn validate_cast_and_convert_metadata` and Kani contract (lines 1672–1852), and Kani harnesses `prove_max_trailing_bytes` (lines 4495–4508), `prove_max_trailing_bytes_components` (lines 4510–4527), `prove_slice_dst_validator_selected_size_fits` (lines 4529–4573), and `prove_slice_dst_validator_rejects_larger_trailing_size` (lines 4575–4590; some harnesses gated behind `cfg(kani_slow)`).
- **Design question informed:** Re-derives in a kernel-checked proof assistant the exact flat-`#[repr(C)]`, unbounded-`Nat` prefix-cast maximum slice count formula `(roundDown bufferLen (dstAlign d) - dstTailOffset d) / d.elem.size`.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.maxSliceElems_some_iff`, `nv_maxSliceElems_some_iff`, `dstSize_eq_phase_normal_form`, `maxSliceElems_eq_phase_normal_form_capacity`, and `dstSize_eq_unphased_normal_form_of_dvd` in `lean/Toy/Layout/Dst.lean`.
  - `Basis: source + execution + derived (modeling bridge)` — Correspondence with `google/zerocopy` at `ec133ce4` (`zerocopy/src/layout.rs`). Source facts:
    - `zerocopy` describes a slice DST's size for `elems` trailing elements as `size_base + round_up(size_phase + elems * elem_size, size_align)` (lines 190–194), where `size_align` and `size_phase` are stored in `size_rounding_align_and_phase` and "the phase need not equal `offset % size_align`" (line 205).
    - `DstLayout::for_repr_c_struct` builds a `#[repr(C)]` layout with `new_zst(repr_align)`, one `extend(field, repr_packed)` per field, and a final `pad_to_align()` (lines 1171–1182). A trailing slice field is `for_slice::<T>()`, which has `offset: 0`, `size_base: 0`, and `size_rounding_align_and_phase: RoundingAlignAndPhase::new(align, 0)` with `align = align_of::<T>()` (lines 1098–1118). `extend` places each field at the preceding size padded to `field_align = min(field.align, max_align)`, where `max_align` is the `repr_packed` argument if any (lines 1243–1246, 1270, 1291–1301), and sets the alignment to `max(self.align, field_align)` (line 1274), starting from `repr_align` or 1 (lines 982–985); this is how `placeFields`, `structAlign`, and `dstTailOffset` compute the tail offset and `dstAlign d`. For a slice field, `extend` adds that offset to both `offset` and `size_base` and keeps the rounding parameters (lines 1342–1365).
    - `pad_to_align` (lines 1430–1486): if `size_align < self.align`, it computes `fixed_contribution` as `size_base` rounded up to `size_align` plus `size_phase` (lines 1453–1461), sets `let phase = fixed_contribution & (self.align.get() - 1);` (line 1463), rounds `fixed_contribution` down to `self.align` to get the new `size_base` (lines 1466–1470), and sets `RoundingAlignAndPhase::new(self.align, phase)` (lines 1471–1472); otherwise it only rounds `size_base` up to `self.align` (lines 1481–1485).
    - For an aligned prefix cast of a slice DST, the contract of `validate_cast_and_convert_metadata` specifies `proofs::max_trailing_bytes(trailing, bytes_len).and_then(|bytes| { let elems = bytes / trailing.elem_size; ... })` (lines 1687–1691), and `proofs::max_trailing_bytes` computes `available.checked_sub(trailing.size_base)?`, rounds that down to `size_align`, and subtracts `size_phase` with `checked_sub` (lines 4064–4066).

    Derived normal form, writing `t = dstTailOffset d`, `a = dstAlign d`, and `e = d.elem.align` for the model of the same struct (so `t` is a multiple of `e` unless `packed(N)` clamps the tail's alignment to `N < e`): if `e < a`, the first `pad_to_align` branch gives `(size_base, size_align, size_phase) = (t - t % a, a, t % a)`; if `e = a`, the second branch gives `(t, a, 0)`, which is the same triple because `a ∣ t`; if `e > a`, which happens only under `packed(N)` with `N < e`, the second branch gives `(alignUp t a, e, 0)`. Hence `size_align = dstAlign d`, `size_phase = dstTailOffset d % dstAlign d`, and `size_base = dstTailOffset d - size_phase` whenever the element alignment does not exceed `dstAlign d`, which always holds without `packed(N)` and holds under `packed(N)` exactly when the element alignment is at most `N`. The phase is nonzero whenever `dstAlign d` does not divide `dstTailOffset d`; for example, the flat DSTs `[u16, u8, [u8]]` and `[u16, u8, [[u8; 2]]]` have phase `1`.

    Execution: the unit-test probe `support/zerocopy_flat_normal_form_probe.rs`, appended to `zerocopy/src/layout.rs` at `ec133ce4` and run with the crate's pinned nightly toolchain (`nightly-2026-09-30`, `rustc 1.101.0-nightly (5c543b0b8 2026-09-29)`), prints `offset` and `align` values equal to the model's `dstTailOffset d` and `dstAlign d`, and `(size_base, size_align, size_phase)` = `(4, 4, 0)` for `[u32, [u8]]`, `(2, 2, 1)` for `[u16, u8, [u8]]` and `[u16, u8, [[u8; 2]]]`, `(0, 8, 3)` for `align(8)` `[u16, u8, [u8]]`, `(0, 4, 1)` for `align(4)` `[u8, [[u8; 3]]]`, `(2, 4, 0)` for `packed(2)` `[u8, [u32]]`, and `(4, 2, 0)` for `packed(1)` `[u32, [u16]]`. Its aligned prefix casts of `[u16, u8, [u8]]` and `[u16, u8, [[u8; 2]]]` with buffer lengths 3, 4, 5, 6, and of `[u32, [u8]]` with buffer lengths 4, 5, 8, 9, return `Err(Size)`/`1`/`1`/`3`, `Err(Size)`/`0`/`0`/`1`, and `0`/`0`/`4`/`4` elements (`support/zerocopy_flat_normal_form_probe_output.txt`); these are the values of `maxSliceElems` on the same inputs (`none`/`some 1`/`some 1`/`some 3`, `none`/`some 0`/`some 0`/`some 1`, `some 0`/`some 0`/`some 4`/`some 4`, computed from its definition; four of them are kernel-checked in `ce_dst_trailing_padding_breaks_naive_prefix_cast`).

    Lean: `dstSize_eq_phase_normal_form` proves that `zerocopy`'s size formula with `(size_base, size_align, size_phase) = (t - t % a, a, t % a)` equals `dstSize d n` for all `d` and `n`; `maxSliceElems_eq_phase_normal_form_capacity` proves that, for `0 < d.elem.size`, `maxSliceElems d bufferLen` equals the element count computed from that normal form as in lines 1687–1691 and 4064–4066 (over unbounded `Nat`); and `dstSize_eq_unphased_normal_form_of_dvd` proves that the size formula with `(alignUp t a, e, 0)` equals `dstSize d n` when `dstAlign d` and `d.elem.align` both divide `d.elem.size` (for real Rust types in the `e > a` case both hold: `e` divides the element size by `r[layout.properties.size]`, and `a` divides `e` because both are powers of two with `a < e`).

    Conclusion: for flat `#[repr(C)]` slice DSTs whose element alignment does not exceed `dstAlign d`, with a positive element size, no overflow, and an address-aligned prefix cast, `maxSliceElems d bufferLen` is `some n` exactly when `zerocopy`'s contract specifies `Ok` with `elems = n`, and is `none` exactly when it specifies `Err(MetadataCastError::Size)`. For `e > a`, only the size formula is shown to agree; the element-count correspondence is not established here.

#### Card 22: `max-slice-elems-none-iff` (`Toy.Layout.maxSliceElems_none_iff_of_elem_size_pos`)

- **Kind / Tier / Depth:** `characterization` | `T1` | `shallow`
- **Plain-language claim:** Whenever `0 < d.elem.size`, `maxSliceElems d bufferLen = none` if and only if no element count `n` fits in `bufferLen` (`∀ n, bufferLen < dstSize d n`).
- **Lean statement:**
```lean
-- lean/Toy/Layout/Dst.lean:276-278
theorem maxSliceElems_none_iff_of_elem_size_pos (d : SliceDstSpec) (bufferLen : Nat)
    (h_elem : 0 < d.elem.size) :
    maxSliceElems d bufferLen = none ↔ ∀ n : Nat, bufferLen < dstSize d n
```
- **Hypothesis ledger:**
  - `h_elem` (`0 < d.elem.size`): excludes zero-sized trailing elements (`d.elem.size = 0`), for which `maxSliceElems` returns `none` even when `dstSize d 0 ≤ bufferLen` — `tight`: counterexample `Toy.Layout.ce_maxSliceElems_none_drop_elem_pos` (`d = ⟨.none, [], ⟨0, 1⟩⟩`, `bufferLen = 0` -> `maxSliceElems = none` while `dstSize d 0 = 0 ≤ 0`).
- **Non-vacuity witness:** `Toy.Layout.nv_maxSliceElems_none_iff_of_elem_size_pos` (`d = ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩`, `bufferLen = 3`).
- **Non-claims:**
  - Same `google/zerocopy` scope and internal-visibility boundary as Card 21 (`DstLayout` is `#[doc(hidden)]`, `validate_cast_and_convert_metadata` is `pub(crate)`, the correspondence is established only when the element alignment does not exceed `dstAlign d`, and `zerocopy` also handles nested DSTs, address alignment, suffix casts, and zero-sized-element panics).
  - Does not claim `maxSliceElems d bufferLen = none` implies `bufferLen < dstTailOffset d` (trailing alignment padding can yield `dstTailOffset d ≤ bufferLen < dstSize d 0`, as in `nv_maxSliceElems_none_iff_of_elem_size_pos` where `dstTailOffset d = 3 = bufferLen < 4 = dstSize d 0`).
- **Prior art:** `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`, `zerocopy/src/layout.rs`, internal `validate_cast_and_convert_metadata` lines 1618–1619, 1672–1704, 1743–1746, 1791–1794; Kani harness `prove_max_trailing_bytes` lines 4495–4508).
- **Design question informed:** Characterizes the exact empty-result (`none`) condition of flat prefix-cast metadata calculation when `0 < d.elem.size`, separating under-sized buffers from zero-sized-element rejection.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.maxSliceElems_none_iff_of_elem_size_pos`, `nv_maxSliceElems_none_iff_of_elem_size_pos`, and `ce_maxSliceElems_none_drop_elem_pos` in `lean/Toy/Layout/Dst.lean`.
  - `Basis: derived (modeling bridge)` — Via Card 21's bridge (`maxSliceElems_eq_phase_normal_form_capacity` and the derived normal form), `maxSliceElems d bufferLen = none` corresponds to the `Err(MetadataCastError::Size)` case of `zerocopy`'s internal `validate_cast_and_convert_metadata` contract (`ec133ce4`, `zerocopy/src/layout.rs` lines 1683–1701) for flat `#[repr(C)]` slice DSTs whose element alignment does not exceed `dstAlign d`, with `elem_size > 0`, no overflow, and an address-aligned prefix cast.

#### Card 23: `zst-tail-no-max-fitting-elems` (`Toy.Layout.zst_tail_no_max_fitting_elems`)

- **Kind / Tier / Depth:** `impossibility` | `T1` | `shallow`
- **Plain-language claim:** If the trailing slice element of a `SliceDstSpec` is zero-sized (`d.elem.size = 0`), then for every `bufferLen : Nat`, no `n : Nat` satisfies `IsMaxFittingElems d bufferLen n`.
- **Lean statement (exact signature and unfolded `IsMaxFittingElems`):**
```lean
-- lean/Toy/Layout/Dst.lean:330-332
theorem zst_tail_no_max_fitting_elems (d : SliceDstSpec) (bufferLen : Nat)
    (h_zst : d.elem.size = 0) :
    ∀ n : Nat, ¬ IsMaxFittingElems d bufferLen n

-- Unfolded: ∀ n : Nat, ¬ (dstSize d n ≤ bufferLen ∧ ∀ k : Nat, dstSize d k ≤ bufferLen → k ≤ n)
```
- **Supporting hashed Lean statements (`lean_names`):** `Toy.Layout.zst_tail_bounded_max_exists`.
- **Hypothesis ledger:**
  - `h_zst` (`d.elem.size = 0`): makes `dstSize d n` independent of `n` so `n + 1` fits whenever `n` fits — `tight`: counterexample / positive control `Toy.Layout.pc_zst_tail_no_max_fitting_elems` (`d = ⟨.none, [⟨4, 4⟩], ⟨1, 1⟩⟩`, `bufferLen = 8` satisfies `IsMaxFittingElems d 8 4`).
- **Non-vacuity witness:** `Toy.Layout.nv_zst_tail_no_max_fitting_elems` (`d = ⟨.none, [⟨4, 4⟩], ⟨0, 1⟩⟩`).
- **Positive control:** `Toy.Layout.pc_zst_tail_no_max_fitting_elems` (`d.elem.size = 1` restores a unique maximum fitting count `n = 4` at `bufferLen = 8`).
- **Non-claims:**
  - The impossibility is an artifact of unbounded `Nat` metadata. Over any bounded metadata domain (for example Rust's actual `n ≤ usize::MAX`), a greatest fitting element count exists whenever `n = 0` fits, namely the bound itself. `zerocopy`'s panic on zero-sized elements is an API choice, not a mathematical necessity.
  - Does not say zero-sized-element slice DSTs cannot fit in a buffer: when `dstSize d 0 ≤ bufferLen`, every `n : Nat` fits, and over any bounded domain `[0, B]` the bound `B` itself fits (`Toy.Layout.zst_tail_bounded_max_exists` proves `dstSize d B ≤ bufferLen ∧ ∀ k : Nat, k ≤ B → dstSize d k ≤ bufferLen → k ≤ B`; note that its substantive content is the first conjunct `dstSize d B ≤ bufferLen`, since the second conjunct holds tautologically from `k ≤ B`).
  - `zerocopy`'s `DstLayout` is `#[doc(hidden)]` and `validate_cast_and_convert_metadata` is `pub(crate)`; its zero-sized-element panic is internal documented behavior, not forced by this theorem.
- **Prior art:** `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`, `zerocopy/src/layout.rs`, internal `validate_cast_and_convert_metadata` lines 1659–1662, 1743–1746).
- **Design question informed:** Clarifies that over unbounded `Nat` no maximum fitting count exists for ZST slice tails, whereas over any finite metadata domain `[0, B]` (such as `usize::MAX`) `B` is the greatest fitting count whenever `n = 0` fits — so a finite API must explicitly choose between returning the domain maximum or rejecting ZST slice tails.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.zst_tail_no_max_fitting_elems`, `nv_zst_tail_no_max_fitting_elems`, `pc_zst_tail_no_max_fitting_elems`, and `zst_tail_bounded_max_exists` in `lean/Toy/Layout/Dst.lean`.
  - `Basis: derived (modeling bridge)` — Contrasts unbounded `Nat` against Rust's finite `usize` slice metadata and `zerocopy`'s explicit `elem_size == 0` panic (`ec133ce4` lines 1659–1662, 1743–1746).

#### Card 24: `dst-no-trailing-padding-all-iff` (`Toy.Layout.dst_no_trailing_padding_all_iff`)

- **Kind / Tier / Depth:** `characterization` | `T1` | `shallow`
- **Plain-language claim:** For any flat `SliceDstSpec` `d`, the trailing padding after the slice is `0` for every element count `n` if and only if `dstAlign d` divides both `dstTailOffset d` and `d.elem.size`.
- **Lean statement (exact signature and unfolded `dstTrailingPadding`):**
```lean
-- lean/Toy/Layout/Dst.lean:377-379
theorem dst_no_trailing_padding_all_iff (d : SliceDstSpec) :
    (∀ n : Nat, dstTrailingPadding d n = 0) ↔
      (dstAlign d ∣ dstTailOffset d ∧ dstAlign d ∣ d.elem.size)

-- Unfolded left-hand side:
--   ∀ n : Nat, alignUp (dstTailOffset d + n * d.elem.size) (dstAlign d) -
--     (dstTailOffset d + n * d.elem.size) = 0
```
- **Hypothesis ledger:** None (holds unconditionally for every `SliceDstSpec` in `Nat`).
- **Non-vacuity witness:** `Toy.Layout.nv_dst_no_trailing_padding_all_iff` (`d = ⟨.none, [⟨4, 4⟩], ⟨4, 4⟩⟩`).
- **Non-claims:**
  - Same `google/zerocopy` scope and internal-visibility boundary as Card 21 (`DstLayout` is `#[doc(hidden)]`, `validate_cast_and_convert_metadata` is `pub(crate)`, and `zerocopy` documents `DstLayout::requires_dynamic_padding` as conservative, proving only the safety-critical direction).
  - Measures trailing padding *after* the slice only; does not rule out inter-field padding inside `headFields` or before `dstTailOffset d`.
  - Does not claim `dstTrailingPadding d n > 0` for *every* `n` when the right-hand side fails (for example, `[u32, [u8]]` has `dstTrailingPadding = 0` whenever `4 ∣ n` and nonzero padding otherwise).
- **Prior art:** `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`, `zerocopy/src/layout.rs`, internal `DstLayout::requires_dynamic_padding` lines 1518–1558: documented conservative at lines 1518–1522, Kani contract lines 1525–1530, safety-critical direction lines 1543–1545; Kani harness `prove_requires_dynamic_padding` lines 4742–4780 gated behind `cfg(kani_slow)`).
- **Design question informed:** Provides the exact necessary and sufficient static divisibility condition under which dynamic trailing padding vanishes for all slice lengths `n` in a flat `#[repr(C)]` slice DST.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.dst_no_trailing_padding_all_iff` and `nv_dst_no_trailing_padding_all_iff` in `lean/Toy/Layout/Dst.lean`.
  - `Basis: derived (modeling bridge)` — The exact iff is a statement about the model's `dstTrailingPadding`; it applies to flat `#[repr(C)]` slice DSTs through Card 20's closed form, and it neither establishes nor refutes the corresponding claim about `zerocopy`'s `DstLayout::requires_dynamic_padding`. Context only (`Basis: source`, not modeled in Lean): `zerocopy`'s internal `DstLayout::requires_dynamic_padding` (`ec133ce4`, `zerocopy/src/layout.rs` lines 1532–1558) returns `initial_size != trailing_slice_layout.offset || !has_static_stride`; it is documented as conservative ("A `true` result conservatively selects the dynamic-padding path; it does not guarantee that any valid metadata actually requires padding.", lines 1521–1522), and only the direction in which a `false` result implies that no valid metadata requires dynamic padding is proved (lines 1543–1545, paraphrased). This package does not model that function and makes no claim about whether it is exact for flat DSTs.

#### Card 25: `ce-dst-trailing-padding-breaks-naive-prefix-cast` (`Toy.Layout.ce_dst_trailing_padding_breaks_naive_prefix_cast`)

- **Kind / Tier / Depth:** `counterexample` | `T1` | `shallow`
- **Plain-language claim:** When `¬ (dstAlign d ∣ dstTailOffset d ∧ dstAlign d ∣ d.elem.size)`, trailing padding can break naive prefix-cast division `(bufferLen - dstTailOffset d) / d.elem.size` and the naive tail check `dstTailOffset d ≤ bufferLen`, across both failure causes: (1) on `[u32, [u8]]` (`4 ∣ 4` holds, `¬ (4 ∣ 1)`), naive `(5 - 4) / 1 = 1` over-estimates `maxSliceElems = some 0`; (2) on `[u16, u8, [u8]]` (neither divisibility holds), `tailOffset = 3 ≤ 3` yet `maxSliceElems = none`; (3) on `[u16, u8, [[u8; 2]]]` (`2 ∣ 2` holds, `¬ (2 ∣ 3)`), naive `(5 - 3) / 2 = 1` over-estimates `maxSliceElems = some 0` and `tailOffset = 3 ≤ 3` accepts a buffer where `maxSliceElems = none`.
- **Lean statement:**
```lean
-- lean/Toy/Layout/Dst.lean:546-573
theorem ce_dst_trailing_padding_breaks_naive_prefix_cast :
    let d1 : SliceDstSpec := ⟨.none, [⟨4, 4⟩], ⟨1, 1⟩⟩
    let d2 : SliceDstSpec := ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩
    let d3 : SliceDstSpec := ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨2, 1⟩⟩
    -- Instance 1: dstAlign ∣ dstTailOffset, ¬ (dstAlign ∣ elem.size)
    (dstAlign d1 ∣ dstTailOffset d1) ∧
    ¬ (dstAlign d1 ∣ d1.elem.size) ∧
    dstTrailingPadding d1 1 = 3 ∧
    (5 - dstTailOffset d1) / d1.elem.size = 1 ∧
    5 < dstSize d1 1 ∧
    maxSliceElems d1 5 = some 0 ∧
    IsMaxFittingElems d1 5 0 ∧
    -- Instance 2: ¬ (dstAlign ∣ dstTailOffset) ∧ ¬ (dstAlign ∣ elem.size)
    ¬ (dstAlign d2 ∣ dstTailOffset d2) ∧
    ¬ (dstAlign d2 ∣ d2.elem.size) ∧
    dstTailOffset d2 ≤ 3 ∧
    maxSliceElems d2 3 = none ∧
    (∀ n : Nat, 3 < dstSize d2 n) ∧
    -- Instance 3: dstAlign ∣ elem.size, ¬ (dstAlign ∣ dstTailOffset)
    (dstAlign d3 ∣ d3.elem.size) ∧
    ¬ (dstAlign d3 ∣ dstTailOffset d3) ∧
    (5 - dstTailOffset d3) / d3.elem.size = 1 ∧
    5 < dstSize d3 1 ∧
    maxSliceElems d3 5 = some 0 ∧
    IsMaxFittingElems d3 5 0 ∧
    dstTailOffset d3 ≤ 3 ∧
    maxSliceElems d3 3 = none ∧
    (∀ n : Nat, 3 < dstSize d3 n)
```
- **Supporting hashed Lean statements (`lean_names`):** `Toy.Layout.maxSliceElems_eq_naive_of_no_trailing_padding`, `Toy.Layout.ce_naive_agrees_fails_zst`, `Toy.Layout.ce_naive_agrees_fails_short_buffer`.
- **Hypothesis ledger:** None (concrete counterexample).
- **Non-vacuity witness:** Direct kernel evaluation on `d1`, `d2`, and `d3`.
- **Non-claims:**
  - Does not say naive division fails when all four sufficient conditions hold (`dstAlign d ∣ dstTailOffset d`, `dstAlign d ∣ d.elem.size`, `0 < d.elem.size`, and `dstTailOffset d ≤ bufferLen`): in that regime `maxSliceElems d bufferLen = some ((bufferLen - dstTailOffset d) / d.elem.size)` (`Toy.Layout.maxSliceElems_eq_naive_of_no_trailing_padding`).
  - Both extra conditions `0 < d.elem.size` and `dstTailOffset d ≤ bufferLen` are essential for agreement with naive `Nat` division (`Toy.Layout.ce_naive_agrees_fails_zst` shows `(8 - 4) / 0 = 0` vs. `none`, and `Toy.Layout.ce_naive_agrees_fails_short_buffer` shows `(2 - 4) / 4 = 0` vs. `none` when `dstSize d 0 = 4 > 2`).
  - Does not claim `dstAlign d ∣ d.elem.size` alone makes naive division sound (instance `d3` refutes that).
- **Prior art:** `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`, `zerocopy/src/layout.rs`, internal `TrailingSliceLayout` doc example lines 158–168 and `max_trailing_bytes` lines 236–341).
- **Design question informed:** Demonstrates across both divisibility failure causes why rounding `bufferLen` down to `dstAlign d` before subtracting `dstTailOffset d` is required for sound flat prefix-cast slice metadata calculation.
- **Evidentiary basis:**
  - `Basis: execution (Lean kernel check)` — `Toy.Layout.ce_dst_trailing_padding_breaks_naive_prefix_cast`, `maxSliceElems_eq_naive_of_no_trailing_padding`, `ce_naive_agrees_fails_zst`, and `ce_naive_agrees_fails_short_buffer` in `lean/Toy/Layout/Dst.lean`.
  - `Basis: derived (modeling bridge)` — All three concrete DSTs match `core::mem::size_of_val` on `rustc 1.98.0-nightly (14210df0e)` (`xc_18a_dst_trail_pad`, `xc_18b_dst_unaligned_off`, `xc_18f_dst_unaligned_off_elem2`).

## Boundaries

### Non-Claims and Unestablished Stronger Conclusions

1. **Formal model vs. real compiler (`execution (Lean kernel check)` vs. `derived (modeling bridge)`):** Proving a theorem in `Toy.Layout` establishes that mathematical statement inside the `Toy.Layout` `Nat` formalism; by itself it neither establishes nor refutes the corresponding claim about `rustc` or the Rust Reference. It does **not** prove equivalence with `rustc` or the Rust Reference across all Rust types or targets; every real-system statement is a separate `derived (modeling bridge)` claim bounded by the modeling assumptions in `## Applicability` and corroborated empirically on 31 concrete probes (`## Evidence`).
2. **Soundness invariants vs. characterization (Cards 1, 2, 4, 13, 14):** Card 1's five invariants (`OffsetsLengthMatch`, `OffsetsAligned`, `OrderedNonOverlapping`, `FieldsInBounds`, `SizeMinimalAligned`) do **not** uniquely determine `reprCStruct` — layouts with gratuitous inter-field padding or smaller struct alignment satisfy all five; uniqueness requires Card 2's greedy-minimal and max-alignment predicates (`OffsetsGreedyMinimal`, `EndOffsetExact`, `AlignIsMaxEffective`). Likewise, `EnumSizeValid ∧ EnumVariantsValid ∧ EnumAlignValid` is a soundness envelope satisfied by *both* `reprCEnum` and `reprIntEnum`; `EnumSharedPayload` and `EnumPerVariantTagged` separate the two layouts and exclude over-padded layouts, but because they are defined from the same `reprCStruct` / `reprCUnion` pipeline as `reprCEnum` / `reprIntEnum`, their offset conjuncts hold by `rfl` on their own layouts and do **not** constitute an independent specification of enum offsets (Cards 13, 14, 19).
3. **Rust-universality of toy-domain alignment and non-emptiness hypotheses (Cards 1–3, 9, 11, 13–17):** `Basis: normative` — every Rust alignment is at least 1 and a power of two (`r[layout.properties.align]`), every size is a multiple of its alignment (`r[layout.properties.size]`), every `align(N)` / `packed(N)` argument is a power of two (`r[layout.repr.alignment.constraint-alignment]`), and zero-variant enums cannot carry `#[repr(C)]` or a primitive representation (`r[layout.repr.c.constraint]`, `r[layout.repr.primitive.constraint]`). `Basis: execution` — `rustc 1.98.0-nightly (14210df0e)` and `rustc 1.102.0-nightly (3ef0c22cd)` reject zero-variant `#[repr(C)]`, `#[repr(u8)]`, `#[repr(i32)]`, and `#[repr(usize)]` enums with error `E0084` (`support/e0084_zero_variant_enums_output.txt`). `Basis: derived (modeling bridge)` — accordingly, the tightness counterexamples using alignments `0`, `3`, `6` or `variants = []` witness minimal mathematical hypotheses in `Toy.Layout` and do **not** exhibit valid Rust types or enums for which those conclusions fail. See `## Applicability` for the quoted rules.
4. **Shallow vs. nested padding (Cards 5, 10, 11, 12, 24):** `AllBytesOccupied`, `totalFieldSize`, and `dstTrailingPadding` treat each `FieldLayout` as an opaque byte block of length `f.size`. Neither `#[repr(C, packed(1))]` (Card 5), `size == totalFieldSize` (Card 10), homogeneous structs (Card 11), nor `dstTrailingPadding = 0` (Card 24) eliminates padding nested inside composite field types (`r[layout.repr.alignment.intro]`).
5. **Bare `#[repr(C)]` enum tag sizing and lint-gated non-conforming discriminants (Card 18):**
   - (`Basis: normative`.) The Rust Reference does not specify a `c_int`-sized tag; it specifies *"a C enum with the same discriminant values and no fixed underlying type"*, calls this a *"best guess"*, and marks `EnumC`'s size as platform dependent (`c_int` equality appears only inside an `x86_64` example).
   - (`Basis: execution`, with source coordinates in Card 18.) On `x86_64-unknown-linux-gnu`, a bare `#[repr(C)]` enum with discriminants `0, 1` has the size and alignment of 4-byte `c_int` (probes `14`, `15`); the divergence from a fixed `c_int` tag for such small discriminants occurs on `thumbv7m-none-eabi` and `hexagon-unknown-none-elf`, which report `c_enum_min_bits = 8` and give `EnumC` `size = 2, align = 1` despite 4-byte `c_int` (`support/crosscheck_short_enum_output.txt`).
   - Discriminants outside C `int` / `unsigned int` (such as `0x1_0000_0000` in `FieldlessCBigDiscr`) violate `r[layout.repr.c.enum.discriminant]` (`src/type-layout.md` line 402; `Basis: normative`). Both recorded compilers accept such an enum with the warning-level future-incompatibility lint `repr_c_enums_larger_than_int` (`rust-lang/rust#124403`; `Basis: execution`, `support/repr_c_big_discriminant_lint_output.txt`; the lint is silenced via `#[allow]` in `support/crosscheck.rs`). That the lint will become an error is a stated intent, not an observation: the Reference note says "This will become an error in the future." (line 408), the lint's declared reason `FutureReleaseError` is documented as "This will be an error in a future release for all editions" (`compiler/rustc_lint_defs/src/lib.rs` line 361 at `14210df0e`), and the emitted warning says "it will become a hard error in a future release!".
   - Nothing in Card 18 applies to released Aeneas versions; `reprC_default_tag_ty := .unsigned .Usize` appears only in the unmerged prototype pull request `AeneasVerif/aeneas#1447` (`2a1dd75567517e078f90b1df746af7373fe24cbc`).
6. **`google/zerocopy` visibility, generality, and one-way `requires_dynamic_padding` (Cards 21–24):** `DstLayout` is `#[doc(hidden)]` and `validate_cast_and_convert_metadata` is `pub(crate)` inside `google/zerocopy`. The correspondence between `maxSliceElems` and `zerocopy`'s prefix-cast element count (Card 21's bridge) is established only for flat `#[repr(C)]` slice DSTs whose element alignment does not exceed `dstAlign d` — for which `zerocopy`'s normal form is `size_align = dstAlign d`, `size_phase = dstTailOffset d % dstAlign d` (nonzero when `dstAlign d ∤ dstTailOffset d`), and `size_base = dstTailOffset d - size_phase` — with `elem.size > 0`, no `usize`/`isize::MAX` overflow, an aligned base pointer, and a prefix cast. For a flat `packed(N)` DST whose element alignment exceeds `N`, `zerocopy`'s normal form has `size_align` equal to the element alignment; only the size formula is shown to agree in that case. Nested DSTs are not modeled. Moreover, `zerocopy` documents `DstLayout::requires_dynamic_padding` as a conservative test and proves only its safety-critical direction in Kani (`prove_requires_dynamic_padding`); Card 24's two-way iff concerns the model's `dstTrailingPadding`; it neither establishes nor refutes the corresponding claim about `requires_dynamic_padding`, which this package does not model.

### Escape Hatches and Qualified Agreement Regimes

1. **Bounded metadata escape hatch for Card 23 (`Toy.Layout.zst_tail_bounded_max_exists`):** Card 23's impossibility (`zst_tail_no_max_fitting_elems`) holds *only* because `IsMaxFittingElems` quantifies `k` over all of unbounded `Nat`. Replacing `k : Nat` with any bounded metadata domain `k ≤ B` (such as `B = usize::MAX` in real Rust) defeats the impossibility completely: whenever `d.elem.size = 0` and `dstSize d 0 ≤ bufferLen`, `Toy.Layout.zst_tail_bounded_max_exists` proves
   ```lean
   -- lean/Toy/Layout/Dst.lean:365-367
   theorem zst_tail_bounded_max_exists (d : SliceDstSpec) (bufferLen B : Nat)
       (h_zst : d.elem.size = 0) (h_fit0 : dstSize d 0 ≤ bufferLen) :
       dstSize d B ≤ bufferLen ∧ ∀ k : Nat, k ≤ B → dstSize d k ≤ bufferLen → k ≤ B
   ```
   (Here the substantive content is `dstSize d B ≤ bufferLen` since `dstSize d B = dstSize d 0`; the upper-bound conjunct `k ≤ B → ... → k ≤ B` is tautological from `k ≤ B`.) Thus `zerocopy`'s panic on `elem_size == 0` is a deliberate API design choice rather than a mathematical necessity on finite targets.
2. **Four-condition naive-division agreement regime for Card 25 (`Toy.Layout.maxSliceElems_eq_naive_of_no_trailing_padding`):** While Card 25 proves that naive `(bufferLen - dstTailOffset d) / d.elem.size` fails when `dstAlign d` fails to divide either `dstTailOffset d` or `d.elem.size`, `Toy.Layout.maxSliceElems_eq_naive_of_no_trailing_padding` proves that naive division agrees with `maxSliceElems` whenever all four conditions hold simultaneously:
   - `dstAlign d ∣ dstTailOffset d`,
   - `dstAlign d ∣ d.elem.size`,
   - `0 < d.elem.size` (cannot be dropped: `Toy.Layout.ce_naive_agrees_fails_zst`), and
   - `dstTailOffset d ≤ bufferLen` (cannot be dropped: `Toy.Layout.ce_naive_agrees_fails_short_buffer`, because truncating `Nat` subtraction gives `(2 - 4) / 4 = 0` when `maxSliceElems = none`).

### Boundary Classification

- **`known not to apply`:**
  - Pointer-sized bare `#[repr(C)]` enum tag heuristic (`usizeTag64`) on `x86_64-unknown-linux-gnu` (`EnumC` is `(8, 4)`, not `(16, 8)`; `Basis: execution`, probe `15`; Card 18).
  - Fixed 4-byte `c_int` bare `#[repr(C)]` enum tag heuristic (`cIntLayout32Bit`) on `thumbv7m-none-eabi` and `hexagon-unknown-none-elf` (`c_enum_min_bits = 8`: `EnumC` with discriminants `0, 1` is `(2, 1)`, not `(8, 4)`; `Basis: execution`, `support/crosscheck_short_enum_output.txt`; Card 18).
  - Naive `(bufferLen - dstTailOffset d) / d.elem.size` prefix-cast metadata calculation when `¬ (dstAlign d ∣ dstTailOffset d ∧ dstAlign d ∣ d.elem.size)`, `d.elem.size = 0`, or `bufferLen < dstTailOffset d` (Card 25).
  - Unconditional size monotonicity `(reprCStruct (.packed n) fields).size ≤ (reprCStruct .none fields).size` over arbitrary non-power-of-two `Nat` alignments (`Toy.Layout.ex_packed_non_pow2_increases_size`: `6` vs. `8`; Card 6).
  - Forward implication of homogeneous padding-freeness at `f.align = 0` (`Toy.Layout.ce_homogeneous_no_padding_iff_drop_align_pos`: `f = ⟨1, 0⟩`; Card 11).
- **`unsupported` (in the target Rust language / compiler):**
  - Zero-variant enums carrying `#[repr(C)]` (`r[layout.repr.c.constraint]`) or `#[repr(Int)]` (`r[layout.repr.primitive.constraint]`; `Basis: normative`), rejected by `rustc` with compile error `E0084` (`Basis: execution`, `support/e0084_zero_variant_enums_output.txt`; Cards 14–16).
  - Combining `#[repr(packed)]` with `#[repr(align)]` on the same struct or transitively nesting an `#[repr(align(N))]` type inside a `#[repr(packed)]` struct (`r[layout.repr.alignment.constraint-exclusive]`; `Basis: normative`, not probed; see `## Applicability` for the generic-instantiation behavior documented by `google/zerocopy`; Cards 5–7).
  - Field-less `#[repr(C)]` enum discriminants outside C `int` / `unsigned int`, disallowed by `r[layout.repr.c.enum.discriminant]` (`Basis: normative`) and accepted by both recorded compilers with the warning-level future-incompatibility lint `repr_c_enums_larger_than_int` (`rust-lang/rust#124403`; `Basis: execution`, `support/repr_c_big_discriminant_lint_output.txt`; Card 18).
- **`not examined`:**
  - Finite machine-word (`usize` / `isize::MAX` / `obj_size_bound`) overflow rejection in `rustc_abi` and bit-precise `usize` overflow guards in `zerocopy`.
  - Targets with `TargetDataLayout::aggregate_align > 1`.
  - Nested DSTs (a slice-tailed struct as the last field, including inside `#[repr(packed(N))]` wrappers), `dyn Trait` vtable DSTs, suffix casts, and runtime pointer-alignment checks.
  - The element-count correspondence with `zerocopy` for flat `packed(N)` slice DSTs whose element alignment exceeds `N` (Card 21's bridge covers only the size formula in that case).
  - `#[repr(C, align(N))]` on enums, `packed`/`align` on unions, `#[repr(transparent)]`, `#[repr(Rust)]` field reordering and niche optimizations, and function-call register ABIs (`FnAbi`).
- **Hypotheses with `unknown` tightness:** **None.** Every hypothesis of every result card in `results.json` is `tight` and paired with a kernel-checked canonical counterexample in `Toy.Layout`.
- **Disproved or withdrawn statements:** **None.** No statement in this package was disproved or withdrawn.

## Evidence

### Toolchain and Whole-Library Kernel Axiom Audit

- **Lean toolchain:** `leanprover/lean4:v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52` (`lean/lean-toolchain`, `lean/lakefile.toml`, zero external `[[require]]` dependencies, no Mathlib).
- **Whole-library `Lean.collectAxioms` audit (`audit/axioms.json`):** Across all **584** non-internal declarations in the `Toy` module hierarchy (`Toy.Layout.Core`, `Toy.Layout.Struct`, `Toy.Layout.Enum`, `Toy.Layout.Dst`, `Toy.Layout.CrossCheck`):
  - **412** declarations depend on **no axioms** (`[]`);
  - **70** declarations depend only on `propext`;
  - **93** declarations depend only on `propext`, `Quot.sound`;
  - **9** declarations depend only on `Classical.choice`, `Quot.sound`, `propext`.
  - Zero declarations use `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `admit`, `native_decide`, `unsafe`, `@[extern]`, `implemented_by`, or user-declared `axiom` / `opaque` constants.

### Statement and Definition-Closure Hash Ledger (81 Declarations)

The table below records every Lean declaration referenced by `results.json` (`lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample`s), its card role(s), its transitive kernel axioms from `audit/axioms.json`, and its `statement_sha256`, `closure_sha256`, and `closure_size` from `audit/statements.json` (`Basis: execution (Lean kernel check)`):

| Declaration | Role(s) | Axioms (`collectAxioms`) | `statement_sha256` | `closure_sha256` | `closure_size` |
| :--- | :--- | :--- | :--- | :--- | ---: |
| `Toy.Layout.ce_aligned_size_drop_fields_pow2` | Card 9 (`repr-c-aligned-size-composition`): tight counterexample (`h_fields`) | *(none)* | `19d7a9cc19219fad2322923fcd714e91c9ee530691acaa9645ccc8d85c4be32b` | `d5f4342d0a4be8c7deedcb318109aa316124654fdd8deeb4db0d7f4e910b4876` | 27 |
| `Toy.Layout.ce_aligned_size_drop_n_pow2` | Card 9 (`repr-c-aligned-size-composition`): tight counterexample (`h_n`) | `propext` | `89b004ea41a2402e26265f0f77d3fc43ba33b5cdfd69bc2544fc1041901691b6` | `a424dfc431524ccd133bc9c1427066e5b4e69171ee7ef13cf7a4aeb4aa3236f9` | 28 |
| `Toy.Layout.ce_dst_trailing_padding_breaks_naive_prefix_cast` | Card 25 (`ce-dst-trailing-padding-breaks-naive-prefix-cast`): main `counterexample` | `Quot.sound`, `propext` | `c4a9c6d8648775f21103e93afa0a8075adc88bd2d5a9ed8120c20efae8f93b0a` | `37ab54dd3d3f290e533a2632b26cc5288eb4d7440fcff66ee2660c930aa5fd82` | 34 |
| `Toy.Layout.ce_heterogeneous_u16_u8_has_trailing_padding` | Card 12 (`ce-heterogeneous-u8-u16-has-padding`): supporting lemma | `Quot.sound`, `propext` | `02e5eeed425e5526135144b9d2160748708f068c662f5c1c536cac7a7d0a69c8` | `5b820a210e02113ddd9036e7b9d2418bd7d691df0233795a6a3854f3ffcf10ab` | 32 |
| `Toy.Layout.ce_heterogeneous_u8_u16_has_padding` | Card 12 (`ce-heterogeneous-u8-u16-has-padding`): main `counterexample` | `Quot.sound`, `propext` | `566f6f2772d8b6bd391a9580803ff0a6e6dd5174eaf0e6cd624af46926e8f01e` | `5b820a210e02113ddd9036e7b9d2418bd7d691df0233795a6a3854f3ffcf10ab` | 32 |
| `Toy.Layout.ce_homogeneous_no_padding_iff_drop_align_pos` | Card 11 (`repr-c-homogeneous-no-padding-iff`): tight counterexample (`h_pos`) | `Quot.sound`, `propext` | `48df8bf8a36d7515b745383e0daf98d40c62e2a9f116900283620af8f20cb63f` | `4461d71932c8d84ad68623dbe9ae0fd2733505a81b83203cae820887ebd141d8` | 28 |
| `Toy.Layout.ce_maxSliceElems_none_drop_elem_pos` | Card 22 (`max-slice-elems-none-iff`): tight counterexample (`h_elem`) | `Quot.sound`, `propext` | `f396e82a478c539b5e0426835500b06caaaac1e8cbe23c1f5170bc5e0c4e821f` | `2a83096bb1d976d96877ae34f7023ec626f41eacdc50746dfaa9e1597d2b34d8` | 32 |
| `Toy.Layout.ce_naive_agrees_fails_short_buffer` | Card 25 (`ce-dst-trailing-padding-breaks-naive-prefix-cast`): supporting lemma | `propext` | `885a32e5abfef4c5905d75cfa8d7c4ea181a0b36d1866c96384b8aa78d5427f2` | `2a83096bb1d976d96877ae34f7023ec626f41eacdc50746dfaa9e1597d2b34d8` | 32 |
| `Toy.Layout.ce_naive_agrees_fails_zst` | Card 25 (`ce-dst-trailing-padding-breaks-naive-prefix-cast`): supporting lemma | `propext` | `efd73cd6f552681f16738a10e004c612b2fedd2d371cf2514a521247120929ea` | `f8fc1b548506cac947c9e7fb6f71019deb8696e26a01b9f881f82b358d36b2e6` | 31 |
| `Toy.Layout.ce_packed_noop_drop_ge` | Card 7 (`repr-c-packed-ge-fields-noop`): tight counterexample (`h_ge`) | *(none)* | `e64a0f17ab0c3cca6e22caaa86241f3da80eb1a1bbbcf54109397be64fe450b5` | `832c57b3e689566dd213428f137eed335cede18bb6c6c3e0759bff3e6159ca33` | 24 |
| `Toy.Layout.ce_reprCEnum_align_drop_tag_pow2` | Card 15 (`repr-c-enum-align-valid`): tight counterexample (`h_tag`) | `Quot.sound`, `propext` | `c990b563336a3357fd8e1e1e40c9cb226511f76ca3c1a44dde3bf1863b3bec5e` | `222aa0dd2629fb727e6b37087c1db65be73414b09604c0c7e633eb7fe73b4a0d` | 39 |
| `Toy.Layout.ce_reprCEnum_align_drop_vars_pow2` | Card 15 (`repr-c-enum-align-valid`): tight counterexample (`h_vars`) | `Quot.sound`, `propext` | `bbf203e24609b81e64584a95f61dcdbb45fe1fc9e17e7a1586696c84b5c33705` | `222aa0dd2629fb727e6b37087c1db65be73414b09604c0c7e633eb7fe73b4a0d` | 39 |
| `Toy.Layout.ce_reprCEnum_geometry_drop_vars_pow2` | Card 13 (`repr-c-enum-geometry`): tight counterexample (`h_vars`) | `Quot.sound`, `propext` | `ce26551f16376491fe02879962166e0b761acf7c37de723f8fcf446f653e9483` | `bbd077e3598e82cd4b8ee2eac0c7123a466f81d820d8b90b205efa75fc1b50c6` | 42 |
| `Toy.Layout.ce_reprCEnum_tag_sizing_divergence` | Card 18 (`ce-repr-c-enum-tag-sizing-targets`): main `counterexample` | *(none)* | `85271db3e3d0a25b99a6294726f360817015dc2a30bf206bab1ff10a1309198f` | `e372aee6f2a4d8139fd8135610f2cba94be83bb69e5de53bb7ac3c4525236649` | 52 |
| `Toy.Layout.ce_reprCEnum_tag_sizing_divergence_aligns` | Card 18 (`ce-repr-c-enum-tag-sizing-targets`): supporting lemma | *(none)* | `939ea689a312709ef64ad7e7e84299a327e426008f46fe6418a8450b237f1308` | `ff4b07eee81090c6cab0af35ab95ee08414b64293ee6e19c22c865079800bf36` | 48 |
| `Toy.Layout.ce_reprCStruct_align_dvd_drop_fields_pow2` | Card 3 (`repr-c-struct-align-pow2-divides`): tight counterexample (`h_fields`) | `Quot.sound`, `propext` | `8505cc9837eb93da6f06cf1e90b641985b71281bc0853d04ec2983466e878ca7` | `4f4645453d9645e1b102bfa596df4ad9208c4274d11bca6fa165cbf1313493a3` | 28 |
| `Toy.Layout.ce_reprCStruct_align_dvd_drop_mod_pow2` | Card 3 (`repr-c-struct-align-pow2-divides`): tight counterexample (`h_mod`) | `Quot.sound`, `propext` | `8b32e407d4bac164cf7ebc7e6d2c1fce455dae593011aa8fcbec270de5ce577e` | `772b6d4f97cebd94ba3363313971e032cab08c85ee5ba583b892a6290fdf6754` | 27 |
| `Toy.Layout.ce_reprCStruct_eq_iff_drop_fields_align_pos` | Card 2 (`repr-c-struct-characterization`): tight counterexample (`h_fields`) | `Quot.sound`, `propext` | `50cd0feadaf0279aaaea40995e8e5349fab262a3444de034cf34f611d8615606` | `c8512aec5686ed706e0b4a31c91078c4cba8ee9711e5a3093886c94bfc3f5038` | 38 |
| `Toy.Layout.ce_reprCStruct_eq_iff_drop_pack_pos` | Card 2 (`repr-c-struct-characterization`): tight counterexample (`h_pack`) | `Quot.sound`, `propext` | `6dd828740e5f21ac378828bd0b2dedf6f8502f6875268f3d97aa54269f3d294e` | `317e64f364863186d0d6fa55790ed716c544e84da696ba56d46c20f5d7fb6214` | 38 |
| `Toy.Layout.ce_reprCStruct_invariants_drop_fields_align_pos` | Card 1 (`repr-c-struct-invariants`): tight counterexample (`h_fields`) | `propext` | `7073310185f29fe9487a5fb90292bfbfbb80f56496f4b61804341d530d31e2de` | `8433045f8a3a16871efa6ba81d8a74cd9d9e86353a20a79af750bd391ef82f32` | 35 |
| `Toy.Layout.ce_reprCStruct_invariants_drop_pack_pos` | Card 1 (`repr-c-struct-invariants`): tight counterexample (`h_pack`) | `propext` | `0c2138d1a2a08eee2fa4d29254470ecaa5688a92ecc31fe07519d2380d26a648` | `a067e4bc125fa0ca6bde67a3fd253f375adfdd49ecce8268ad333676d47051c0` | 35 |
| `Toy.Layout.ce_reprIntEnum_align_eq_drop_nonempty` | Card 16 (`repr-int-enum-align-eq-repr-c-enum`): tight counterexample (`h_nonempty`) | *(none)* | `1c6913d0c736ad53738b325fadb44519ad01f3c294da7674f402b16c6c9b6ce8` | `bad42aa960f3ef9f4131b0d5607bae10d727b05b8800ae5af58e85488106a037` | 49 |
| `Toy.Layout.ce_reprIntEnum_geometry_drop_nonempty` | Card 14 (`repr-int-enum-geometry`): tight counterexample (`h_nonempty`) | `propext` | `c6b136f364cc171182bfd8da5f3b162f958887f55a06772d5f7f04b02e49b59d` | `bef28590f7e98132b9447fee985d3ba161c8ab000375708572f44287cc66b87c` | 55 |
| `Toy.Layout.ce_reprIntEnum_geometry_drop_vars_align_pos` | Card 14 (`repr-int-enum-geometry`): tight counterexample (`h_vars`) | `propext` | `4450051a04e10dddcdf6d5c8fba7aea6a35d5198f3b184b32a690736f800c8b7` | `19d46e76ee6bf0054b9d2ff675b4a38252b4f36c5c300e9ff459fdc200d8ed8e` | 43 |
| `Toy.Layout.ce_reprIntEnum_lt_reprCEnum_u8` | Card 19 (`ce-repr-int-strictly-smaller-than-repr-c-u8`): main `counterexample` | *(none)* | `de3f2a2068c4d0c77b18bf716d9343301715014294dfd1d6048e8d5874c8f48d` | `0d42cc243f60f211d12905078c100c4f19ed190a197441409aa7c1ff4206f30c` | 44 |
| `Toy.Layout.ce_reprInt_le_reprC_drop_tag_pow2` | Card 17 (`repr-int-enum-size-le-repr-c-enum-size`): tight counterexample (`h_tag`) | `propext` | `99b55364f2bef4431113b9385883ee1cee5f4e2f8339106df691ac54aea74de8` | `e8a2f4a3ca33531aec8e5b6c46679d87da2ccee6dcc996aac2e1ebb5109f8453` | 40 |
| `Toy.Layout.ce_reprInt_le_reprC_drop_vars_pow2` | Card 17 (`repr-int-enum-size-le-repr-c-enum-size`): tight counterexample (`h_vars`) | *(none)* | `bdec163965ed5fc309fc86e845320b3fa92aab0eb9a4303fb75abf5031ba88e0` | `e8a2f4a3ca33531aec8e5b6c46679d87da2ccee6dcc996aac2e1ebb5109f8453` | 40 |
| `Toy.Layout.dstInstantiated_eq_closed_form` | Card 20 (`dst-instantiated-eq-closed-form`): main `theorem` | `Quot.sound`, `propext` | `5606214611fa18aae1fc44010a2bacc8cb4e931614d9aa9eb5a44d3cfe35a94c` | `8e112346b4154bb2d860ccfe97a543ad86209d76fa8c228c641f9d0087c9b2c7` | 37 |
| `Toy.Layout.dstSize_eq_phase_normal_form` | Card 21 (`max-slice-elems-some-iff`): supporting lemma | `Quot.sound`, `propext` | `0d6496bfe7f7d1964f6b7250668ebadd7460933879fdfbcbea9d1af570a8f508` | `df9735dc34bfb8a84a4c689296ec7db7a35361cae95ddcc6c5fc25f122a11344` | 30 |
| `Toy.Layout.dstSize_eq_unphased_normal_form_of_dvd` | Card 21 (`max-slice-elems-some-iff`): supporting lemma | `Quot.sound`, `propext` | `2331cbd35a8549891185a4baf99effa740414a629713862cca5d69c70d948cac` | `df9735dc34bfb8a84a4c689296ec7db7a35361cae95ddcc6c5fc25f122a11344` | 30 |
| `Toy.Layout.dst_no_trailing_padding_all_iff` | Card 24 (`dst-no-trailing-padding-all-iff`): main `characterization` | `Quot.sound`, `propext` | `015520159532d7f210d616278552d606a76771863d0b98c2eed2d2cdf5e57222` | `98dfcde5b7fb4426a1c07a04b8169481386cb99eac2e643777382e779c55dd57` | 31 |
| `Toy.Layout.ex_homogeneous_non_dvd_has_padding` | Card 11 (`repr-c-homogeneous-no-padding-iff`): supporting lemma | `Quot.sound`, `propext` | `2f9b5f0924db6dbaefd8e3c6149ec80d5368d2ec29cde32cf98c934d75e5f3fe` | `689ceac9a304a339283a0c9d729992a6219952ac463f2cd178bb17d2ee9f17f3` | 29 |
| `Toy.Layout.ex_packed_non_pow2_increases_size` | Card 6 (`repr-c-packed-align-le`): supporting lemma | *(none)* | `ad3e1ec76bf1c0fbec1968e8a305d858c537926f1e01d20d97f58b53af7bb7e4` | `d1e643274355eb1e8ab69e35100f5792aafe83f69887b2d5935eabfd9603f239` | 25 |
| `Toy.Layout.maxSliceElems_eq_naive_of_no_trailing_padding` | Card 25 (`ce-dst-trailing-padding-breaks-naive-prefix-cast`): supporting lemma | `Quot.sound`, `propext` | `e2c8507decbc923e876c16b25e8c747726f844a7f1597cdaffb243cbbf00e71f` | `f8fc1b548506cac947c9e7fb6f71019deb8696e26a01b9f881f82b358d36b2e6` | 31 |
| `Toy.Layout.maxSliceElems_eq_phase_normal_form_capacity` | Card 21 (`max-slice-elems-some-iff`): supporting lemma | `Quot.sound`, `propext` | `4aeb23b9e66f3f218dc5ca31df7b6cc797becbc5c335a48d6727dec0dc303461` | `f8fc1b548506cac947c9e7fb6f71019deb8696e26a01b9f881f82b358d36b2e6` | 31 |
| `Toy.Layout.maxSliceElems_none_iff_of_elem_size_pos` | Card 22 (`max-slice-elems-none-iff`): main `characterization` | `Quot.sound`, `propext` | `c2ec9a8b043a5ba687721c856cb8cf878090776861b690a1fe1f4ba1ede299b9` | `2a83096bb1d976d96877ae34f7023ec626f41eacdc50746dfaa9e1597d2b34d8` | 32 |
| `Toy.Layout.maxSliceElems_some_iff` | Card 21 (`max-slice-elems-some-iff`): main `characterization` | `Quot.sound`, `propext` | `05acf55a349734bcecb283073b08282d42fb4fca10afd5b9d32a93b3f4f04e8c` | `e705dac2493cfaa21b3002c7d6889b8ecd7ccdb26d81c7e15bf686d14fa0e88e` | 33 |
| `Toy.Layout.nv_dstInstantiated_eq_closed_form` | Card 20 (`dst-instantiated-eq-closed-form`): non-vacuity witness | *(none)* | `d2dc6e776f3b68bee39d388076e2babc94f5cda46f1b35fd5f97b75ab8a6721f` | `8e112346b4154bb2d860ccfe97a543ad86209d76fa8c228c641f9d0087c9b2c7` | 37 |
| `Toy.Layout.nv_dst_no_trailing_padding_all_iff` | Card 24 (`dst-no-trailing-padding-all-iff`): non-vacuity witness | *(none)* | `a5c3151d3066f78183d48a702637d786ef20635304293cc2b4595794a35019da` | `bb771ec875c183d461957baf57097d466790b30436eb9661aad3f07936d06c3d` | 29 |
| `Toy.Layout.nv_maxSliceElems_none_iff_of_elem_size_pos` | Card 22 (`max-slice-elems-none-iff`): non-vacuity witness | `Quot.sound`, `propext` | `1670731e56a1943ae7690c8bdf7dec9e6418c1c2a835ce87067b03e3d27cfed7` | `2a83096bb1d976d96877ae34f7023ec626f41eacdc50746dfaa9e1597d2b34d8` | 32 |
| `Toy.Layout.nv_maxSliceElems_some_iff` | Card 21 (`max-slice-elems-some-iff`): non-vacuity witness | `Quot.sound`, `propext` | `3dce1676e9704f32334210c8ba46d12e5a7049ca828d6e40ac99467fb65278d7` | `e705dac2493cfaa21b3002c7d6889b8ecd7ccdb26d81c7e15bf686d14fa0e88e` | 33 |
| `Toy.Layout.nv_reprCEnum_align_valid_of_pow2` | Card 15 (`repr-c-enum-align-valid`): non-vacuity witness | `propext` | `1a87bff643fd9e00ff2c96aa5dfdc98cb4a57c5f0a97854beba4534615da7683` | `8666cf0277d02f68e7dfe2bd396375f413e4df5fcda77ac1619ead24f03a4bb6` | 16 |
| `Toy.Layout.nv_reprCEnum_geometry_of_vars_pow2` | Card 13 (`repr-c-enum-geometry`): non-vacuity witness | `propext` | `14b1764ec8440b8f5d25ce4f544f004931c86ba1355f3c120fe4f0cdcb9dd955` | `8bfc2fac7427bb31794e89a14c8b47ed70115011ffa97d327fc6b0aa7fab1abf` | 5 |
| `Toy.Layout.nv_reprCStruct_align_pow2_divides` | Card 3 (`repr-c-struct-align-pow2-divides`): non-vacuity witness | `propext` | `fba10a8251daf49781c7bce3f59df4299fe0942c87d8504a53c2bce702dadd59` | `4967e9816de3a05574f60ae4f8849f92a969205dcc23ec99e0e5f1199ef4c352` | 13 |
| `Toy.Layout.nv_reprCStruct_aligned_preserves_offsets` | Card 8 (`repr-c-aligned-preserves-offsets`): non-vacuity witness | *(none)* | `2b5f4f98316f907ad36fa1ed71159d8626762619e028b27f726f659cdaca0c3b` | `3886b9fa39e596c21d7feae9dfea03160875b869616f5e45c58f75ea8ee93394` | 27 |
| `Toy.Layout.nv_reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2` | Card 9 (`repr-c-aligned-size-composition`): non-vacuity witness | `propext` | `4575d0b9b17aa2a2b1b76b10901702757c77ba3ce259beb85c0bf48f3aa94ac5` | `8bfc2fac7427bb31794e89a14c8b47ed70115011ffa97d327fc6b0aa7fab1abf` | 5 |
| `Toy.Layout.nv_reprCStruct_eq_iff_of_align_pos` | Card 2 (`repr-c-struct-characterization`): non-vacuity witness | `propext` | `81053c96eb0ed02bf9ea2a6f77e70d1922d56b1be636e574dfec4a4a1385780c` | `1c20fdae4e0941caca24481cfddc5b84f3c07412c425b40c55b934fb6a235028` | 9 |
| `Toy.Layout.nv_reprCStruct_homogeneous_no_padding_iff_of_align_pos` | Card 11 (`repr-c-homogeneous-no-padding-iff`): non-vacuity witness | `propext` | `065e3cd510c11852d3245386cd2287fff8e17c731bf01276fc5220aed7bb0270` | `59dedbe309d435b36b03f53d1162dd41a50879879bbc24b0f1f660c19ded9b49` | 4 |
| `Toy.Layout.nv_reprCStruct_invariants_of_align_pos` | Card 1 (`repr-c-struct-invariants`): non-vacuity witness | `propext` | `dcc4688bb0ba9f04cea2ccdd2f87c7da31a90c731f78f5b17bd08471dad55cde` | `1c20fdae4e0941caca24481cfddc5b84f3c07412c425b40c55b934fb6a235028` | 9 |
| `Toy.Layout.nv_reprCStruct_no_padding_iff` | Card 10 (`repr-c-no-padding-iff-size-eq-sum`): non-vacuity witness | `Quot.sound`, `propext` | `8f6acfce201a7342c36c0c95a53853f256740fa99d8e741d01adf11967a506ed` | `4e66bcdd29784f2cac3d0aef31d07d25d815ce47c7e29ae5855c92abb8b2041d` | 29 |
| `Toy.Layout.nv_reprCStruct_packed_align_le` | Card 6 (`repr-c-packed-align-le`): non-vacuity witness | *(none)* | `73f25d2ed2a4966358b81740b57572992ea3cd8cfb5fc68bb3e1f2d3589ce7c3` | `80f8a4ca917a3540773e46536b3acadd9064e62e29d8765be3ed56632e9821e8` | 25 |
| `Toy.Layout.nv_reprCStruct_packed_ge_fields_noop` | Card 7 (`repr-c-packed-ge-fields-noop`): non-vacuity witness | `propext` | `561f3e8cde980a9f6be68f868d77c46ca17a024a852950de93ab23a5b8a4ef17` | `31b3b9cca0d3067d5a5db3704987eea43e1a57b0320ee4d83146554d1289d592` | 3 |
| `Toy.Layout.nv_reprCStruct_packed_one_no_padding` | Card 5 (`repr-c-packed-one-no-padding`): non-vacuity witness | *(none)* | `8f792c64f5bd354f6648ad4fcb10391f7b8802064e069810cca386b395dcb366` | `832c57b3e689566dd213428f137eed335cede18bb6c6c3e0759bff3e6159ca33` | 24 |
| `Toy.Layout.nv_reprIntEnum_align_eq_reprCEnum_align_of_nonempty` | Card 16 (`repr-int-enum-align-eq-repr-c-enum`): non-vacuity witness | *(none)* | `e66fae4f1c33fe41757e3949623201d44faf9d96aae4009078f064dff87247aa` | `38dd46306f16e54296ffd6605ddb2725a8aed9bf89b3c261b85ee98dfa73cea6` | 2 |
| `Toy.Layout.nv_reprIntEnum_geometry_of_nonempty_align_pos` | Card 14 (`repr-int-enum-geometry`): non-vacuity witness | `propext` | `3fa324ef4ee4b28c91216c0c856f07faf466cad77b77af42350137458a37676d` | `59dedbe309d435b36b03f53d1162dd41a50879879bbc24b0f1f660c19ded9b49` | 4 |
| `Toy.Layout.nv_reprIntEnum_size_le_reprCEnum_size_of_pow2` | Card 17 (`repr-int-enum-size-le-repr-c-enum-size`): non-vacuity witness | `propext` | `116a3bb7e7ec585f4d4d1ec26ef662898072ff163c2d1c64934de87aaf763015` | `5fb92b783ae0ec8501db55ceed5e38e65a51eccaa946aaca443cb169aac90437` | 6 |
| `Toy.Layout.nv_zst_tail_no_max_fitting_elems` | Card 23 (`zst-tail-no-max-fitting-elems`): non-vacuity witness | *(none)* | `587f05ad355c51f982ffef945ff33378e99a05de8c87c344701e10682e66ad29` | `9458a93c5dba1a4540214ad6760a473afba8f2b2f26bca689600f8c605929864` | 10 |
| `Toy.Layout.orderedNonOverlapping_implies_monotone_and_disjoint` | Card 1 (`repr-c-struct-invariants`): supporting lemma; Card 4 (`struct-invariants-mutually-independent`): supporting lemma | `Quot.sound`, `propext` | `a19eb7b66acbc084463a3df481b1cccb5e6ec8a93daacd02d1400b197cf009c9` | `c087fd90dbc2e02787fdae6f756b8e276562a818efb9fc6bf7256c10c5ac6f59` | 10 |
| `Toy.Layout.orderedNonOverlapping_without_length_not_monotone` | Card 1 (`repr-c-struct-invariants`): supporting lemma; Card 4 (`struct-invariants-mutually-independent`): supporting lemma | `propext` | `abe8c00b8db254b7a80042910c5d9a755adfa499059869cf468ef9349e48c859` | `1e267594f51d194e6428d9b977453ce67fb89ac34b04c77d5af2e5a14a3bcc59` | 8 |
| `Toy.Layout.pc_zst_tail_no_max_fitting_elems` | Card 23 (`zst-tail-no-max-fitting-elems`): positive control; Card 23 (`zst-tail-no-max-fitting-elems`): tight counterexample (`h_zst`) | `Quot.sound`, `propext` | `3890cdfbd392d19af5ccd3554aacd9ae87eb335e6dbe1aa1c110a249d9684f3d` | `df274dd25d28b59d84628b4abd99be799eebe437ee6b7dce773a6643669b8450` | 31 |
| `Toy.Layout.reprCEnum_align_valid_of_pow2` | Card 15 (`repr-c-enum-align-valid`): main `theorem` | `Classical.choice`, `Quot.sound`, `propext` | `03fb7870ac92679a9e2d21c2093c1c6cb80f537e1787e4eedb4c6afbafc6d8bf` | `222aa0dd2629fb727e6b37087c1db65be73414b09604c0c7e633eb7fe73b4a0d` | 39 |
| `Toy.Layout.reprCEnum_geometry_of_vars_pow2` | Card 13 (`repr-c-enum-geometry`): main `theorem` | `Classical.choice`, `Quot.sound`, `propext` | `1aba764a3425ae2e3dd9274fb6a2761abe8afe4461e02cc80414722d62078168` | `1e8e6dfc8d13cf6e5b82834c03a3aeb6af54df4d0bd600cf2fd120e82f45a036` | 44 |
| `Toy.Layout.reprCEnum_tagOffset_zero` | Card 13 (`repr-c-enum-geometry`): supporting lemma; Card 15 (`repr-c-enum-align-valid`): supporting lemma | `Quot.sound`, `propext` | `a4ff75fed9b7d5fa46e84d7bf4cf9d80038ae9a836c4c4a2550129421f365812` | `b0e703f494bbcf9e65c3b56386d139cc2632bf23128662eb6b697f275ce04665` | 37 |
| `Toy.Layout.reprCStruct_align_pow2_divides` | Card 3 (`repr-c-struct-align-pow2-divides`): main `theorem` | `Classical.choice`, `Quot.sound`, `propext` | `44db0920ef901fa32ae9e1311a5189d3d97c677bce8d2f15a79fc00bb594c2ea` | `1244ce54874c5eb95fe40bf21674593be1fbe0cc60a109dde5f21810fac58f4f` | 29 |
| `Toy.Layout.reprCStruct_aligned_preserves_offsets` | Card 8 (`repr-c-aligned-preserves-offsets`): main `theorem` | `propext` | `7c408566afb95e55cd6ae4e75d7cefe23a817d45e4bb8ce3a76843f272aa7772` | `146db0c3641d6d300670f9648717f8d72b073deecf1bf29c75e3bacd0cc43290` | 28 |
| `Toy.Layout.reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2` | Card 9 (`repr-c-aligned-size-composition`): main `theorem` | `Classical.choice`, `Quot.sound`, `propext` | `4761836f2c9fb0ef8c199521f4c0806eee7b38a39c9b5cb74c254a4c89892faf` | `a424dfc431524ccd133bc9c1427066e5b4e69171ee7ef13cf7a4aeb4aa3236f9` | 28 |
| `Toy.Layout.reprCStruct_eq_iff_of_align_pos` | Card 2 (`repr-c-struct-characterization`): main `characterization` | `Classical.choice`, `Quot.sound`, `propext` | `7e7ee580fabf65b0d7c65c686ce3918b137e9926b37ffca7be37ba9c1c57a7cd` | `e0b2b1e5706b22a4a618757f9231a6b85437d763ef44a491b275c0eaa53690e9` | 39 |
| `Toy.Layout.reprCStruct_homogeneous_no_padding_iff_of_align_pos` | Card 11 (`repr-c-homogeneous-no-padding-iff`): main `characterization` | `Quot.sound`, `propext` | `5d3ed7fab4e8dfb30f7e5e9cb7c0ae43cfe05f3007d87998537321910198cecd` | `689ceac9a304a339283a0c9d729992a6219952ac463f2cd178bb17d2ee9f17f3` | 29 |
| `Toy.Layout.reprCStruct_invariants_of_align_pos` | Card 1 (`repr-c-struct-invariants`): main `theorem` | `Quot.sound`, `propext` | `9ae0f13574b9aa71e75beded2d70130f5330bf82b05c3690d352533b084bf9b6` | `d371253c490e3f27d66dc14e4d72596d516ec9d1f37a9634273eada9856f55a2` | 36 |
| `Toy.Layout.reprCStruct_no_padding_iff_size_eq_sum` | Card 10 (`repr-c-no-padding-iff-size-eq-sum`): main `characterization` | `Quot.sound`, `propext` | `5d95bfe659dd19e126bbfea41773d83311f27fc091834239c0c9b2888b40be96` | `4e66bcdd29784f2cac3d0aef31d07d25d815ce47c7e29ae5855c92abb8b2041d` | 29 |
| `Toy.Layout.reprCStruct_packed_align_le` | Card 6 (`repr-c-packed-align-le`): main `theorem` | `Quot.sound`, `propext` | `e998ddbf4e30fa0e66105dc8c8be7482a71edc15da2cba0af6a301afe720158d` | `80f8a4ca917a3540773e46536b3acadd9064e62e29d8765be3ed56632e9821e8` | 25 |
| `Toy.Layout.reprCStruct_packed_ge_fields_noop` | Card 7 (`repr-c-packed-ge-fields-noop`): main `theorem` | `propext` | `fff9c5d85525d988bc4b049bda8d24f6fa08c64fba7e1abcf8a78114b1b1ccf4` | `832c57b3e689566dd213428f137eed335cede18bb6c6c3e0759bff3e6159ca33` | 24 |
| `Toy.Layout.reprCStruct_packed_one_no_padding` | Card 5 (`repr-c-packed-one-no-padding`): main `theorem` | `Quot.sound`, `propext` | `6a10608cbf34a1c39b692205114e2398eef63f31c1d95f75d0066775b7108f2f` | `5a50b5e7a8aeeae15602048584b066d6abd793a85162c9ac6be877925127a571` | 31 |
| `Toy.Layout.reprIntEnum_align_eq_reprCEnum_align_of_nonempty` | Card 16 (`repr-int-enum-align-eq-repr-c-enum`): main `theorem` | `Quot.sound`, `propext` | `d470af035782a191bd2db1aa65528ffe4ba0a56d4f495d227ca29c3c036009b0` | `5925a7e8102a1716bdb2595fb037235e60b740024162a759999cf00c2a06afb5` | 38 |
| `Toy.Layout.reprIntEnum_all_variants_tag_at_zero` | Card 14 (`repr-int-enum-geometry`): supporting lemma | `propext` | `d6c45bb8576f795c723c06ed1d0e928c0aabb356f6051a1d6a4393604ca65ae5` | `79743da6e7cbddf2968e997734a764b3d11b08c53781f86e33369c4ac99b7d9f` | 25 |
| `Toy.Layout.reprIntEnum_geometry_of_nonempty_align_pos` | Card 14 (`repr-int-enum-geometry`): main `theorem` | `Quot.sound`, `propext` | `689241676dcb0d1d0895b7e979d1f73af677ddb3ca67469b8c91694d1be48452` | `5951c14d9615780fa91a1bb407b9ebe6522130acadfb2498fc03a06db759a722` | 44 |
| `Toy.Layout.reprIntEnum_size_le_reprCEnum_size_of_pow2` | Card 17 (`repr-int-enum-size-le-repr-c-enum-size`): main `theorem` | `Classical.choice`, `Quot.sound`, `propext` | `6f869f23591369e0289ac83da6fe088fe487b1dc553cdaa7784a3ded1629dd79` | `e8a2f4a3ca33531aec8e5b6c46679d87da2ccee6dcc996aac2e1ebb5109f8453` | 40 |
| `Toy.Layout.reprIntEnum_tagOffset_zero` | Card 14 (`repr-int-enum-geometry`): supporting lemma | `Quot.sound`, `propext` | `0405924252199740319f70b5c743513d54dbf7e379338360450f836b8b8ee9bf` | `29be3f1c8566d24d8f023ee9acde83ab44a044b89a2792915c52b4a7565d91ca` | 38 |
| `Toy.Layout.struct_invariants_mutually_independent` | Card 4 (`struct-invariants-mutually-independent`): main `counterexample` | `Quot.sound`, `propext` | `fa3e5e2aca4a10ee77927b90a687fed8002a0aada238bfbe853e85a03f3610de` | `e9c410c62f1079618d65970797dbe3ab9f802947913f5d94c63c287fa4141530` | 42 |
| `Toy.Layout.zst_tail_bounded_max_exists` | Card 23 (`zst-tail-no-max-fitting-elems`): supporting lemma | *(none)* | `56cfabd8488136ca8b8c01cc1bbd8608e0e145432788b72a37af8efb61ae08f3` | `df9735dc34bfb8a84a4c689296ec7db7a35361cae95ddcc6c5fc25f122a11344` | 30 |
| `Toy.Layout.zst_tail_no_max_fitting_elems` | Card 23 (`zst-tail-no-max-fitting-elems`): main `impossibility` | `Quot.sound`, `propext` | `c4129456f91c517289b2755ca34b18a5ce976351867244601fd0888428cdab91` | `df274dd25d28b59d84628b4abd99be799eebe437ee6b7dce773a6643669b8450` | 31 |

### Empirical `rustc` Execution Cross-Check (Corroborative Evidence, Not Proof)

To test the `derived (modeling bridge)` on concrete Rust types and cross-compilation targets, the package preserves runnable Rust probes and their recorded compiler outputs under `support/` alongside kernel-checked model evaluations in `lean/Toy/Layout/CrossCheck.lean` (following the offset/size/alignment test-assertion pattern used by `rust-lang/rust-bindgen` at commit `e9a5f1fc501b55c3f7392a09ba8cd2a1041f7a33`, `bindgen/codegen/mod.rs` lines 2755–2840 and `bindgen/codegen/struct_layout.rs` lines 35–46):

- **Evidence boundary:** **This cross-check is empirical `execution` evidence, not a formal proof.** The Lean kernel checks only `Toy.Layout`'s arithmetic numbers (`xc_01_empty` through `xc_20_hexagon_short_enums`); the `rustc` numbers are transcribed from the recorded compiler outputs in `support/crosscheck_output.txt` and `support/crosscheck_short_enum_output.txt`.
- **Executed compiler (observed 2026-11-20; original probe capture on the pinned nightly):** `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65 2026-05-31)` (LLVM 22.1.6).
- **Re-run (observed 2026-11-20):** on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and on `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` (commit `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM 23.1.5), the output of `support/crosscheck.rs` is byte-identical to `support/crosscheck_output.txt` after its version header; `support/crosscheck_short_enum.rs` compiles for `thumbv7m-none-eabi` and `hexagon-unknown-none-elf`, both of which report `"c-enum-min-bits": 8`; the flipped negative control fails with E0308; and `support/e0084_zero_variant_enums.rs` and `support/repr_c_big_discriminant_lint.rs` behave as recorded in their output files.
- **Preserved files in `support/`:**
  - `support/crosscheck.rs` and `support/crosscheck_output.txt`: 25 concrete `#[repr(C)]` struct, `packed(N)`, `align(N)`, union, field-less and data-carrying enum, `#[repr(u8)]` vs. `#[repr(C, u8)]` enum, and flat slice-tailed DST probes executed with `rustc -O` on `x86_64-unknown-linux-gnu` (`c_int`: size 4, align 4; `usize`: size 8, align 8). Probe `14b` (`FieldlessCBigDiscr`, discriminants `0x1_0000_0000` and `0x1_0000_0001`) carries `#[allow(dead_code, repr_c_enums_larger_than_int)]` because out-of-`int`/`unsigned int`-range discriminants are non-conforming per `r[layout.repr.c.enum.discriminant]` and trigger the future-incompatibility lint `repr_c_enums_larger_than_int` (`rust-lang/rust#124403`).
  - `support/crosscheck_short_enum.rs` and `support/crosscheck_short_enum_output.txt`: `#![feature(no_core)] #![no_core]` compile-time layout assertions compiled with `--crate-type=rlib --emit=metadata` on `--target thumbv7m-none-eabi` and `--target hexagon-unknown-none-elf` (both reporting `"c-enum-min-bits": 8` in `rustc -Z unstable-options --print target-spec-json`), verifying `FieldlessC = (1, 1)`, `FieldlessC256 = (2, 2)`, and `EnumC = (2, 1)` (`3 × 2 = 6` target probes), plus a negative-control compile assertion (`size_of::<EnumC>() == 8`) that fails with `error[E0308]: mismatched types — expected an array with a size of 8, found one with a size of 2`.
  - `support/e0084_zero_variant_enums.rs` and `support/e0084_zero_variant_enums_output.txt`: zero-variant enums with `#[repr(C)]`, `#[repr(u8)]`, `#[repr(i32)]`, and `#[repr(usize)]`; compilation fails with exactly one `error[E0084]: unsupported representation for zero-variant enum` per enum (exit status 1) on both recorded compilers.
  - `support/repr_c_big_discriminant_lint.rs` and `support/repr_c_big_discriminant_lint_output.txt`: the enum of probe `14b` without the `#[allow]`; both recorded compilers accept it (exit status 0) and emit the `repr_c_enums_larger_than_int` warning, including the diagnostic text "this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!".
  - `support/zerocopy_flat_normal_form_probe.rs` and `support/zerocopy_flat_normal_form_probe_output.txt`: a unit-test module to append to `zerocopy/src/layout.rs` in `google/zerocopy` at `ec133ce4d7993775413d852f91c9e3eb2a2a0897`; it prints the `TrailingSliceLayout` fields produced by `DstLayout::for_repr_c_struct` for seven flat slice DSTs and the result of `validate_cast_and_convert_metadata` for aligned prefix casts of three of them. Recorded with `cargo +nightly-2026-09-30` (`rustc 1.101.0-nightly (5c543b0b8 2026-09-29)`, the crate's `pinned-nightly`) on 2026-11-20. Used by Card 21's bridge.
  - `support/crosscheck_comparison.txt`: full **31/31 exact match (`0` mismatches)** side-by-side table pairing every `rustc` observation with `Toy.Layout.xc_01_empty` .. `Toy.Layout.xc_20_hexagon_short_enums`.

### Primary Source Coordinates

All upstream repository coordinates below were inspected at immutable 40-character Git revisions:

1. **Lean 4 toolchain:** `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
2. **The Rust Reference:** `rust-lang/reference`, commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md`:
   - `r[layout.properties.align]` (line 19), `r[layout.properties.size]` (line 22), `r[layout.array]` (line 77), `r[layout.slice]` (line 82);
   - `r[layout.repr.rust.layout]` and `r[layout.repr.rust.struct]` (lines 174–183);
   - `r[layout.repr.c.constraint]` (lines 237–238), `r[layout.repr.c.struct]` (lines 240–353), `r[layout.repr.c.union]` (lines 361–396);
   - `r[layout.repr.c.enum.discriminant]` (line 402, lint note lines 407–408), `r[layout.repr.c.enum.size-align]` (line 411, `x86_64` example lines 422–426, "best guess" note lines 429–432), `r[layout.repr.c.adt]` (lines 438–499, verbatim tagged-union definition lines 441–447);
   - `r[layout.repr.primitive.constraint]` (lines 507–508), `r[layout.repr.primitive.adt]` (lines 518–568), `r[layout.repr.primitive-c]` (lines 570–628, including `EnumC` comment lines 621–622);
   - `r[layout.repr.alignment]` (lines 632–681: `constraint-alignment` lines 638–639, `align` lines 641–642, `packed` lines 644–645, `packed-fields` lines 647–648, `packed-padding` lines 650–651, `constraint-exclusive` lines 653–654).
3. **Rust RFC 2195 (`really_tagged_unions`):** `rust-lang/rfcs`, commit `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, `text/2195-really-tagged-unions.md` (`#[repr(Int)]` lines 195–235, `TwoCases` 4-byte vs. 6-byte example lines 257–300, `#[repr(C, Int)]` and bare `#[repr(C)]` lines 303–366, space-usage ordering line 408, C enum tag guessing line 437).
4. **`rustc` (executed cross-check and primary compiler source):** `rust-lang/rust`, commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`:
   - `compiler/rustc_abi/src/layout.rs`: `layout_of_enum` tagged branch (lines 817–864) and `LayoutCalculator::univariant_biased` (lines 1094–1328, `pack.is_some()` base-alignment reset at line 1108, `packed(1)` at lines 1278–1282, post-loop `repr.align` application at lines 1312–1320);
   - `compiler/rustc_middle/src/ty/layout.rs`: `discr_range_of_repr` (lines 77–120);
   - `compiler/rustc_target/src/spec/mod.rs`: `c_enum_min_size` initialization (lines 2190–2191);
   - `compiler/rustc_target/src/spec/base/arm_none.rs` (line 29) and `compiler/rustc_target/src/spec/targets/hexagon_unknown_none_elf.rs` (line 31): `c_enum_min_bits: Some(8)`;
   - `compiler/rustc_const_eval/src/util/alignment.rs`: `place_unalignment` (lines 9–50, `layout.align.abi <= pack` at lines 26–44), called from `compiler/rustc_mir_transform/src/check_packed_ref.rs` line 42;
   - `compiler/rustc_lint_defs/src/builtin.rs`: `REPR_C_ENUMS_LARGER_THAN_INT` (declaration lines 5395–5441 with `Warn` level and `fcw!(FutureReleaseError #124403)` at lines 5434–5440; lint-list entry line 94; tracking issue `rust-lang/rust#124403`);
   - `compiler/rustc_lint_defs/src/lib.rs`: `FutureIncompatibilityReason::FutureReleaseError` (lines 360–375, documented at line 361 as "This will be an error in a future release for all editions");
   - `compiler/rustc_abi/src/lib.rs`: default `aggregate_align: align(8)` (line 311), `TargetDataLayout::obj_size_bound` (lines 608–615), `Align::from_bytes` treating 0 as 1 byte (lines 1079–1083); `compiler/rustc_abi/src/layout.rs`: `SizeOverflow` check in `univariant_biased` (lines 1322–1323); target data-layout strings in `compiler/rustc_target/src/spec/targets/{x86_64_unknown_linux_gnu,aarch64_unknown_linux_gnu,thumbv7m_none_eabi,hexagon_unknown_none_elf}.rs`.
5. **`rustc` (post-refactor layout source):** `rust-lang/rust`, commit `4b5350e87e487aed08ab2f9f0160a4b2616438bc`:
   - `compiler/rustc_abi/src/layout.rs`: `layout_of_univariant_biased` (lines 591–823, `pack.is_some()` line 605, `packed(1)` lines 780–783, `repr.align` lines 811–819);
   - `compiler/rustc_abi/src/layout/enum_layout.rs`: `calculate_tagged_layout` (lines 339–415, `!repr.c()` branch lines 383–395);
   - `compiler/rustc_middle/src/ty/layout.rs`: `discr_range_of_repr` (lines 78–130);
   - `compiler/rustc_target/src/spec/mod.rs`: `c_enum_min_size` (lines 2078–2079).
6. **CompCert:** `AbsInt/CompCert`, commit `2685140bf72c959446981fb99b5e44a8975021bc`, `cfrontend/Ctypes.v` (`alignof_composite_two_p` lines 642–649, `field_offset_in_range_gen`/`field_offset_in_range` lines 748–770, `field_offset_no_overlap` lines 774–797, `field_offset_aligned_gen`/`field_offset_aligned` lines 812–830).
7. **`google/zerocopy`:** `google/zerocopy`, commit `ec133ce4d7993775413d852f91c9e3eb2a2a0897`:
   - `zerocopy/src/layout.rs`: `#[doc(hidden)] pub struct DstLayout` (lines 19–42), `TrailingSliceLayout` (lines 150–207), `max_trailing_bytes` (lines 236–341), `max_elems_for_bytes` (lines 827–859), `DstLayout::extend` and `pad_to_align` (lines 1199–1495), `requires_dynamic_padding` (lines 1518–1558), `pub(crate) const fn validate_cast_and_convert_metadata` (lines 1601–1852), `size_for_metadata_model` (lines 2409–2473), Kani harnesses `prove_max_trailing_bytes` (lines 4495–4508), `prove_max_trailing_bytes_components` (lines 4510–4527), `prove_slice_dst_validator_selected_size_fits` (lines 4529–4573), `prove_slice_dst_validator_rejects_larger_trailing_size` (lines 4575–4590), and `prove_requires_dynamic_padding` (lines 4742–4780, `cfg(kani_slow)`);
   - `zerocopy/src/layout.rs` (normal-form correspondence, Card 21): `TrailingSliceLayout` size formula (lines 190–194) and phase remark (line 205); `DstLayout::for_slice` (lines 1073–1121, fields at lines 1098–1118); `DstLayout::for_repr_c_struct` (lines 1123–1197; generic-instantiation note at lines 1135–1143); slice-field case of `DstLayout::extend` (lines 1324–1366); slice-DST case of `DstLayout::pad_to_align` (lines 1430–1486); contract of `validate_cast_and_convert_metadata` (lines 1672–1704); `proofs::max_trailing_bytes` (lines 4060–4067);
   - `zerocopy/src/util/macro_util.rs`: `struct_padding!` (lines 319–340).
8. **`Lokathor/bytemuck`:** `Lokathor/bytemuck`, commit `ea3616110b0134e9991fdb66be8892dbc427c5ac`, `derive/src/traits.rs`, `generate_assert_no_padding` (lines 1078–1115).
9. **MiniRust:** `minirust/minirust`, commit `063d784186d3252bee242217f218223205c0b568`, `spec/lang/types.md` (`TupleHeadLayout::{capped_tail_align, tail_offset, full_size_and_align}` lines 200–225, `LayoutStrategy::compute_size_and_align` lines 259–277).
10. **Additional prose-context references (not `REPORT.json` subjects):** unmerged pull request `AeneasVerif/aeneas#1447` (fork `JoJoDeveloping/aeneas`, commit `2a1dd75567517e078f90b1df746af7373fe24cbc`, `backends/lean/Aeneas/Data/Layout/ReprC.lean` lines 9–13, 86–115, 125–131, 163–176, 214–223 and `Properties.lean` lines 108, 124, 306–311); `rust-lang/rust` tracking issue `#124403` (`repr_c_enums_larger_than_int`); cross-check test-generation precedent `rust-lang/rust-bindgen` commit `e9a5f1fc501b55c3f7392a09ba8cd2a1041f7a33`.

## Revalidation

### Primary Self-Contained Package Revalidation

Requirements: `elan` (which automatically selects `leanprover/lean4:v4.34.1` from `lean/lean-toolchain`) and `python3` (standard library only). From the top-level package directory (`repr-c-layout-algebra-dst-tails-and-enum-tags/`), run:

```bash
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package directory: it copies `lean/` into a fresh temporary directory and checks four properties end-to-end (exiting `0` and printing `REVALIDATED` iff all pass):

1. **Clean kernel build:** `lake build` compiles the entire `Toy` library under `leanprover/lean4:v4.34.1`.
2. **Banned-token scan:** comment-stripped Lean sources contain no `sorry`, `admit`, `native_decide`, or `axiom` declarations.
3. **Whole-library axiom check:** `Lean.collectAxioms` on every non-internal `Toy.*` declaration uses at most `{propext, Classical.choice, Quot.sound}`.
4. **Exact statement and definition-closure hash verification:** for every Lean declaration referenced by `results.json` (`lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample`s) and recorded in `audit/statements.json`, `revalidate.py` hashes:
   - `statement_sha256`: the UTF-8 SHA-256 of `toString (repr ci.type)` (the Lean kernel `Expr` representation of the theorem's type, including binder names); and
   - `closure_sha256` (and `closure_size`): the UTF-8 SHA-256 of newline-joined, lexicographically sorted `"<name> : <repr type>"` (plus `" := <repr value>"` for every non-theorem definition, structure, or inductive; theorem proof bodies are excluded) over all `Toy.*` constants transitively reachable from `ci.type`, verifying exact agreement with `audit/statements.json`.

### Direct `elan`, `lake`, and `python3` Audit Using `lean/RevalidationAudit.lean`

To run the build, `collectAxioms` check, and SHA-256 comparison directly with `elan`, `lake`, and `python3` without `support/revalidate.py`, execute from the package root using the included standalone `lean/RevalidationAudit.lean` module (which lives outside the `Toy` library target):

```bash
(cd lean && lake build && lake env lean RevalidationAudit.lean) > /tmp/toy_layout_audit.out
python3 - /tmp/toy_layout_audit.out audit/statements.json audit/axioms.json <<'PY'
import hashlib, json, re, sys

raw = open(sys.argv[1], encoding="utf-8").read()
m = re.search(r"REVALIDATE_JSON (\{.*\})", raw)
assert m, f"missing REVALIDATE_JSON line in {sys.argv[1]}"
audit = json.loads(m.group(1))
expected_stmts = json.load(open(sys.argv[2], encoding="utf-8"))["statements"]
expected_axioms = json.load(open(sys.argv[3], encoding="utf-8"))["declarations"]
allowed = {"propext", "Classical.choice", "Quot.sound"}

decls = {d["name"]: sorted(d["axioms"]) for d in audit["decls"]}
bad_axs = {k: v for k, v in decls.items() if set(v) - allowed}
assert not bad_axs, f"disallowed axioms: {bad_axs}"
assert decls == expected_axioms, "declaration axiom map differs from audit/axioms.json"

got_stmts = {}
for s in audit["stmts"]:
    assert not s.get("missing"), f"missing declaration: {s['name']}"
    got_stmts[s["name"]] = {
        "statement_sha256": hashlib.sha256(s["type_repr"].encode("utf-8")).hexdigest(),
        "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode("utf-8")).hexdigest(),
        "closure_size": len(s["closure"]),
    }

assert got_stmts == expected_stmts, "statement/closure hashes differ from audit/statements.json"
print(f"OK: {len(decls)} declarations axiom-clean; {len(got_stmts)} statement/closure hashes verified.")
PY
```

### Re-Running the Empirical `rustc` Cross-Check Probes

To revalidate the `derived (modeling bridge)` against a newer `rustc` toolchain or an additional target (requires `rustc` nightly for `#![feature(no_core)]` in the freestanding cross-target probe):

```bash
rustc -O support/crosscheck.rs -o /tmp/crosscheck_bin && /tmp/crosscheck_bin | diff -u <(sed '1,/^---$/d' support/crosscheck_output.txt) -
rustc --crate-type=rlib --emit=metadata --target thumbv7m-none-eabi support/crosscheck_short_enum.rs -o /tmp/libxc_thumb.rmeta
rustc --crate-type=rlib --emit=metadata --target hexagon-unknown-none-elf support/crosscheck_short_enum.rs -o /tmp/libxc_hex.rmeta
```

The first command needs `bash` (process substitution); `sed` drops the recorded `rustc --version --verbose` header (everything up to the first `---` line), so `diff` exits `0` exactly when every printed layout matches. The two cross-target commands must succeed; changing the `EnumC` assertion `[(); 2]` to `[(); 8]` in a copy of `support/crosscheck_short_enum.rs` must make them fail with E0308.

The zero-variant and large-discriminant probes (run from the package root):

```bash
rustc --crate-type=lib support/e0084_zero_variant_enums.rs -o /tmp/e0084.rlib            # expected: exit 1, four error[E0084]
rustc --crate-type=lib support/repr_c_big_discriminant_lint.rs -o /tmp/big_discr.rlib    # expected: exit 0, repr_c_enums_larger_than_int warnings
```

The `zerocopy` normal-form probe (Card 21) requires a checkout of `google/zerocopy` at `ec133ce4d7993775413d852f91c9e3eb2a2a0897`: append `support/zerocopy_flat_normal_form_probe.rs` to `zerocopy/src/layout.rs`, then run `cargo +nightly-2026-09-30 test --lib flat_normal_form_probe -- --nocapture` from the checkout's `zerocopy/` directory and compare the printed lines with `support/zerocopy_flat_normal_form_probe_output.txt`. For a newer `zerocopy` revision, re-read the cited regions of `zerocopy/src/layout.rs` (`for_slice`, the slice-field case of `extend`, the slice-DST case of `pad_to_align`, and `proofs::max_trailing_bytes`) before re-running the probe.
