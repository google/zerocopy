<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Zerocopy Semi-Verification Proofs (`zerocopy/proofs`)

> [!WARNING]
> **This is alpha software!** Anneal (`0.2.0-alpha`, Stage 0) has not yet
> completed an independent TCB audit. The units below verify **530 distinct
> currently capturable scalar, unit, layout, generic, and sentinel
> functions/monomorphizations** in `../src/` under Profile v1 and **48
> byte-slice, fieldless-enum, raw-pointer, and generic array, slice, reference,
> and tuple functions/monomorphizations** under the experimental Profile v2
> (`x86_64-unknown-linux-gnu`, `-C opt-level=0`,
> `no_zerocopy_allocator_api_1_100_0` only). Passing CI here **does not** verify
> other pointer or slice operations (`Ref`, `Ptr`, `transmute!`), Cargo features
> (`alloc`, `simd`, `derive`), or the `unsafe impl` safety contracts of marker
> traits such as `FromBytes` (only the empty
> `only_derive_is_allowed_to_implement_this_trait` sentinel methods are checked
> today). Treat passing runs as experimental alpha checks under intact-host
> assumptions and human review of stated specifications (each unit's primary
> specification module—here `Spec.lean`, or a generated `Specs/zerocopy/*.lean`
> together with the inline attributes it is lowered from—plus any
> `specification`-role modules and their transitive meaning dependencies),
> `request.json`, CI workflows, and TCB audit logs (complete review-surface
> reporting remains under active development; see [alpha usage][alpha-doc] and
> [threat model][threat-doc]).

[alpha-doc]: ../../anneal/docs/alpha.md
[threat-doc]: ../../anneal/THREAT_MODEL.md

This directory contains Anneal formal specifications (out-of-line, or generated
from inline attributes in `../src/`) and kernel-checked Lean 4 proofs covering
those 530 distinct Profile v1 items (scalar, unit, layout, generic, and
marker-sentinel functions and monomorphizations) and 48 verbatim Profile v2
byte-slice, fieldless-enum, raw-pointer, and generic array, slice, reference,
and tuple items in `../src/`. Together they cover every non-generic function in
`../src/` that whole-crate capture currently admits.

The Profile v2 units (`06_*`, `08_*`, `16_*`, and `17_*`) rest on additional
assumptions, described in [Profile v2][profile-v2-doc]. Profile v2 has no
aliasing model: the theorems quantify only over entries whose reference
arguments are valid, initialized, and, for `&mut`, disjoint, and receipts record
these as assumptions. Receipts also mark `correspondence_provenance`
inapplicable, because the `lean-miri` correspondence covers only Profile v1
rules.

[profile-v2-doc]: ../../anneal/docs/alpha.md#experimental-mir-profile-v2-borrowed-slices-and-raw-pointers

`../Cargo.toml` excludes `/proofs` from crates.io packages so downstream
`zerocopy` users incur zero new dependencies, zero MSRV impact, and zero build
overhead. CI continuously enforces `request.json` schema and source
completeness (matching non-excluded `../src/**/*.rs` files, cross-unit
`compilation` parity, Receipt v3 bindings and source SHA-256 digests, and
verifying `env!`/`option_env!`/`CARGO_PKG*` tokens stay in module/item doc
attributes across compiled sources) and every proof unit in
`../../ci/checks.toml` (`anneal-installed-smoke`) via
`../../anneal/ci/verify_zerocopy.py`.

A unit's specification is either a hand-written `Spec*.lean` or, for
specifications written inline in `../src/` as
`#[cfg_attr(anneal, anneal::spec(..))]` attributes, the module
`Specs/zerocopy/<claim>.lean` that `anneal-spec-lower --format v2-module`
generates from them. Such a unit also has a `spec_sources.json` naming the
source files and the claim it lowers, and CI checks that the module is fresh
(see [`anneal-spec`][anneal-spec-doc]). Either way, the specification module
and `request.json` are what reviewers read.

[anneal-spec-doc]: ../../anneal/tools/anneal-spec/README.md

## Verified Units

| Unit | Verbatim `zerocopy/src/` Targets | Properties Proved | Axioms |
| --- | --- | --- | --- |
| `01_usize_pointer_metadata` | `<usize as PointerMetadata>::{from,to}_elem_count` (specified inline, claim `zc01_usize_pointer_metadata`) | Identity on all `2^64` `usize` inputs (so each round-trips through the other), terminating without panicking within at most 2 MIR steps; exact identities and safe signatures (`isUnsafe = false`) | `["propext"]` |
| `02_unit_pointer_metadata` | `<() as PointerMetadata>::{from,to}_elem_count` (specified inline, claim `zc02_unit_pointer_metadata`) | Universal constant `()` and `0usize` return; total execution; exact identities and safe signatures (`isUnsafe = false`) | `["propext"]` |
| `03_macros_unsafe` | `util::macros::__unsafe` (specified inline, claim `zc03_macros_unsafe`) | Exact identity and signature (`isUnsafe = true`, no parameters, `()` return); total execution returning `()` | `["propext"]` |
| `04_substantive_and_frombytes_markers` | All 5 substantive scalar/unit/macro items above plus 4 `u8` derive-only sentinel methods (`only_derive_is_allowed_to_implement_this_trait` for `Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`; does not verify `unsafe impl` soundness) | Compositional 9-body `BodiesVerified` dispatch and functional postconditions | `["propext"]` |
| `05_layout_add_scaled_metadata` | `layout::add_scaled_metadata` (`unsafe`; calls `core::num` `unchecked_mul` and `unchecked_add`; specified inline, claim `zc05_layout_add_scaled_metadata`) | Under its `# Safety` contract (`base + metadata * multiple <= usize::MAX` on a 64-bit target): no undefined behavior, termination, and an exact `base + metadata * multiple` return across both sysroot call frames, matching its Kani `ensures` contract. Covers the inherent `core::num` methods selected by Anneal's pinned toolchain, not the `util::polyfills::NumExt` fallback used on older toolchains | `["propext"]` |
| `05_sharded_tryfrombytes` | All 5 substantive items above plus 20 primitive derive-only sentinel methods (`u8`, `i8`, `u16`, `i16`, `usize`, incl. 101B `TryFromBytes for usize`; does not verify `unsafe impl` soundness) | Tarjan SCC 2-shard `.olean` split (`Proof.IdTree`, `Proof.Shard_000..001`, non-unfolding `BinChunkTree` assembly) | `["propext"]` |
| `06_byte_slice_into_byte_slice` | `<&[u8] as IntoByteSlice>::into_byte_slice`, `<&mut [u8] as IntoByteSlice>::into_byte_slice`, `<&mut [u8] as IntoByteSliceMut>::into_byte_slice_mut` | Profile v2 stability over all valid entries and caller memory: each body is well-formed and returns the same slice address and length with caller memory unchanged as its only terminal behavior | `["propext"]` |
| `08_byte_slice_split_at_unchecked` | `<&[u8] as SplitByteSlice>::split_at_unchecked` | Profile v2 (`UnitTheoremV2`) over all valid entries satisfying `mid <= len`, execution reaches a return of `(s[..mid], s[mid..])` (second slice at `addr + mid`, lengths summing to `len`) with caller memory unchanged | `["propext"]` |
| `10_byteorder_endian_wrappers` | 7 foundational `u8` trait markers (`impls.rs`, `lib.rs`) plus 168 concrete `--instantiate` monomorphizations across all 12 `byteorder` types (`U16`–`Usize`, `I16`–`Isize`, `F32`, `F64`) × `{BigEndian, LittleEndian}` × `{KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned}` | Selected 175-body MIR sealing-marker contracts (`ReturnsTotal` and arbitrary-`MemoryState` stepping); `Trusted.MirSemantics.{Bytes,Layout}` `u8` `⟨1, 0⟩` layout & endian invariance, `encodeUInt`/`decodeUInt` & 4-/8-byte raw bit-pattern round-trips, `IntWidth` `FromBytes`/`IntoBytes`, native `0 < alignLog2` (`w ≠ .i8`), `.unsupported` float lowering, and `Spec`-local `swapEndian` duality (`[u8; N]`/`#[repr(transparent)]` wrapper layout not lowered in Profile v1) | `["propext"]` |
| `11_primitive_bit_validity` | 77 trait sealing markers for the 15 non-float primitive types in `impls.rs` (`()`, `bool`, `char`, `u8`–`u128`, `i8`–`i128`, `usize`, `isize` across `Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`, `IntoBytes`, `Unaligned`) | Selected 77-body MIR sealing-marker contracts (`ReturnsTotal`); endian-parametric model-side `Trusted.MirSemantics.Bytes` bit-validity theorems (`IsFromZeros`, `IsFromBytes`, `IsIntoBytes`, `IsUnaligned`, `bool`/`char` `TryFromBytes` conditions; `is_safe` MIR bodies not captured) plus negative `FromBytes` (`bool` `0x02`, `char` `0xD800`) and `Unaligned` model refutations | `["propext"]` |
| `12_nonzero_niche_bit_validity` | 88 selected trait sealing markers for the 12 `NonZero<*>` and 12 `Option<NonZero<*>>` integer types in `impls.rs:226-295` (`u8`–`u128`, `i8`–`i128`, `usize`, `isize` across `Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`, `IntoBytes`, `Unaligned`) | Selected 88-body MIR sealing-marker contracts (`ReturnsTotal` and arbitrary-`MemoryState` stepping); endian- and signedness-parametric model-side `Trusted.MirSemantics.Bytes` non-zero characterization (`is_safe` MIR bodies not captured), `NonZero<*>` `FromZeros`/`FromBytes` model refutations and `IntoBytes` no-padding law, `Option<NonZero<*>>` Niche Partition Theorem, and `.i8` vs. multi-byte alignment model refutations | `["propext"]` |
| `13_float_str_and_atomic_bit_validity` | 61 selected trait sealing markers for `f32`, `f64` (`impls.rs:81-82`), `str` (`impls.rs:165-180`), and `AtomicBool` plus `Atomic{U,I}{8,16,32,64,size}` (`impls.rs:454-609`, excluding `KnownLayout`, `AtomicPtr<T>`, and feature-gated `f16`/`f128`/`simd`) | Selected 61-body MIR sealing-marker contracts (`ReturnsTotal` and arbitrary-`MemoryState` stepping); Spec-local IEEE `f32`/`f64` `AllocByte` bit-validity/layout definitions (`MirTy` lowers `Float`, `Str`, and ADTs to `.unsupported`; `is_safe` MIR bodies not captured), Spec-local RFC 3629 UTF-8 DFA/grammar equivalence (`StrFromZerosSound`, `StrIntoBytesSound`, and `[0xFF]`/`[0x80]`/`[0xC0, 0x80]`/`U+D800` `FromBytes` refutations), `Trusted.MirSemantics` bit-validity proofs for `Atomic*` backing scalars (linked via the `Spec`-local same-size/bit-validity correspondence `atomicBackingMirTy`, incl. `0x02` `FromBytes` refutation), the 1-byte-atomic `Unaligned` argument (a 1-byte layout whose size is a multiple of its alignment has alignment 1), primitive `w ≠ .i8` alignment above 1, and Spec-local `ContainsUnsafeCell` `ImmutableSound` classification | `["propext"]` |
| `14_known_layout_and_dst_layout` | 41 selected `KnownLayout` trait sealing markers (`11` concrete `Atomic*` types in `impls.rs:405,463`, `29` primitive and `NonZero<*>` types in `lib.rs:1221-1227`, and `str` in `lib.rs:1267-1270`, excluding generic `impls` such as `AtomicPtr<T>`, `LAYOUT` constants, `raw_from_ptr_len`/`pointer_to_metadata`, and feature-gated `f16`/`f128`/`simd`) | Selected 41-body MIR sealing-marker contracts (`isUnsafe = false`, `argumentCount = 0`, `ReturnsTotal` returning `()`, and arbitrary-`MemoryState` stepping); model-side 64-bit `DstLayout`/`TrailingSliceLayout`/`RoundingAlignAndPhase` theorems grounded in `M_anneal`'s 64-bit `isize`/`usize` layout (`layout.rs`/`util/mod.rs` Rust MIR bodies not captured): power-of-two bit-hack iff, `RoundingAlignAndPhase::{new,components,align}` round-trip and Kani postconditions, `size_offset` OR/ADD equivalence, `util::{padding_needed_for,round_down_to_next_multiple_of_alignment}`, `padding_for_elems` fast-vs-naive equivalence and `align ∣ elem_size` invariance, `max_trailing_bytes` Kani agreement and iff optimality, and `size_for_elems`/`size_for_elems_unchecked` Kani agreement and overflow-freedom | `["propext"]` |
| `15_generic_wrapper_and_array_markers` | `util::macros::__unsafe` (`1` non-generic root), `util::macro_util::must_use::<{bool,u32,u8,usize}>` (`4` substantive generic functions in `util/macro_util.rs:963-968`), and `85` concrete `--instantiate` trait sealing markers in `wrappers.rs`, `impls.rs`, and `lib.rs` across `Unalign<u32>`, `ReadOnly<{u32,u8,UnsafeCell<u32>}>`, `Wrapping<{u32,u8}>`, `ManuallyDrop<{u32,u8}>`, `core::mem::MaybeUninit<{u32,u8}>`, `wrappers::MaybeUninit<u32>`, `[u8; 4]`, `[u32; 4]`, `PhantomData<*const u8>`, `*const u8`, `*mut u8`, `AtomicPtr<u8>`, `UnsafeCell<u8>`, `Cell<u8>`, and `Option<{NonZero<u32>,&u8,NonNull<u8>}>` | Selected 90-body MIR contracts (`ReturnsTotal` and arbitrary-`MemoryState` stepping, including universal identity contracts over all `Bool`/`u32`/`u8`/`usize` inputs for `must_use::<*>`); direct `Trusted.MirSemantics.{Bytes,Layout,Memory}` theorems for `UnalignMemorySound` (alignment-1 `writeBytes`/`readBytes` at arbitrary offsets vs. `w ≠ .i8` `loadIndirect`/`storeIndirect` alignment faults at offset `1` and `u32` offset-1 round-trip), `MaybeUninitSound` (`initBytes? = none`, `decodeVal = .ok none`, and `encodeVal ≠ .ok` on `.uninit` buffers), 64-bit thin-pointer `decodeUInt` `is_zeroed` iff characterization (`1 :: replicate 7 0` refutation), and ZST `.unit` `0`-byte codec/`readBytes`/`writeBytes` laws; plus `Spec`-local `[T; N]` `encodeArray`/`decodeArray` lifting (`[bool; 4]` `0x02` `FromBytes` refutation; Profile v1 `layoutOfTy`/`encodeVal`/`decodeVal` do not handle `Struct`/`Union`/`Array`/raw pointers—`MirTy.array` is Profile v2 only—and inherent wrapper methods are uncaptured) | `["propext"]` |
| `16_enum_impls_and_pointer_to_metadata` | The derived `<byteorder::Order as Clone>::clone`, `<byteorder::Order as PartialEq>::eq`, and `<byteorder::Order as Eq>::assert_fields_are_eq` (`byteorder.rs:102`) and `<layout::CastType as Clone>::clone` (`layout.rs:862`), plus the 15 `<T as KnownLayout>::pointer_to_metadata` bodies for `()`, `u8`–`u128`, `i8`–`i128`, `usize`, `isize`, `bool`, and `char` generated by `impl_known_layout!` (`util/macros.rs:476`) | Profile v2 (`UnitTheoremV2`) over all valid entries and caller memory, with each safe body pinned to its identity: `clone` returns exactly the enum value `&self` points to, `eq` returns whether its two (possibly aliased) referents are the same variant, and `assert_fields_are_eq` and every `pointer_to_metadata` (for any `*mut Self`) return `()`; each with caller memory unchanged as its only terminal behavior | `["propext"]` |
| `17_slice_array_ref_tuple_instantiations` | `25` concrete `--instantiate` monomorphizations: `<[T; N] as KnownLayout>::pointer_to_metadata` (generated by `impl_known_layout!`, `util/macros.rs:476`) at `[u8; 0]`, `[u8; 4]`, `[u32; 0]`, and `[u32; 4]`, plus the `only_derive_is_allowed_to_implement_this_trait` sealing markers of the generic impls for `[T]` (`Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`, `IntoBytes`, `Unaligned`), `&T` and `&mut T` (`KnownLayout`, `Immutable`), `NonNull<T>` (`Immutable`), and `Option<&mut T>` (`TryFromBytes`, `FromZeros`) at `T = u8`, and for `(A,)` and `(A, B)` (`Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`) at `(u8,)` and `(u8, u32)` (`impls.rs`, `lib.rs`) | Profile v2 (`UnitTheoremV2`, required by the `*mut [T; N]` parameters) over all valid entries and caller memory, with each safe body pinned to its identity: every body returns `()` (for `pointer_to_metadata`, for any `*mut [T; N]`) with caller memory unchanged as its only terminal behavior | `["propext"]` |

## Reproducing Locally

Run the CI driver against unmodified `zerocopy/src/` from the repository root:

```sh
python3 -I -B anneal/ci/verify_zerocopy.py
```

Or run `cargo anneal verify` on an individual unit:

```sh
cargo anneal verify --request zerocopy/proofs/01_usize_pointer_metadata/request.json
```
