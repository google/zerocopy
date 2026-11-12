# Rust Reference layout guarantees, target ABI limits, and SemVer snares

## Summary

Sound verification of unsafe Rust and zero-copy type conversions requires
separating three sources of compilation variation that `rustc`'s concrete
`TyAndLayout` queries conflate:

1. **Compiler-internal layout nondeterminism within a fixed target and crate
   graph**: For default `#[repr(Rust)]` types, tuples, and unions, the Rust
   Reference guarantees only alignment lower bounds (`align(S) >= max_i align(F_i)`
   unless lowered by `packed`), size-multiple-of-alignment (`size % align == 0`),
   size upper bounds (`size <= isize::MAX`), aligned field offsets, pairwise
   non-overlapping field intervals in structs (`r[layout.repr.rust.layout.struct]`),
   and—since `rust-lang/reference@82da570b` (PRs #2262 and #2293)—zero size for
   all-ZST structs (`r[layout.repr.rust.struct-zst]`) and single-variant
   non-primitive all-ZST enums (`r[layout.repr.rust.enum-struct-like-zst]`). It
   does **not** guarantee `size_of::<Wrapper>() == size_of::<Field>()` or byte
   offset `0` for a single-field `#[repr(Rust)]` struct with a non-ZST field,
   does **not** guarantee `align == 1` for a `#[repr(Rust)]` ZST struct, and
   does **not** guarantee field order in `#[repr(Rust, packed(1))]` structs.
   Furthermore, `rustc`'s `-Z randomize-layout` flag is strictly weaker than
   Reference-admissible nondeterminism: `-Z randomize-layout` never randomizes
   single-field `#[repr(Rust)]` structs (`fields.len() > 1` guard in
   `LayoutCalculator::univariant_biased`), tuples (`ReprOptions::default()`), or
   `#[repr(Rust)]` unions (`FieldsShape::Union`), while it **does** randomize
   `1-ZST` field offsets inside `#[repr(transparent)]` structs because
   `ReprFlags::IS_TRANSPARENT` is absent from `FIELD_ORDER_UNOPTIMIZABLE`.
2. **Target specification parameters (`TargetDataLayout` and `TargetOptions`)**:
   Even for `#[repr(C)]` and `#[repr(transparent)]` types whose layout formulas
   are normatively fixed by the Reference relative to primitive layouts,
   primitive alignments (`u64`/`i64`, `u128`/`i128`, `f64`, pointers), pointer
   widths (`16`, `32`, `64` bits), endianness, and C `enum` widths vary across
   `rustc`'s 322 built-in targets. Across built-in targets with inline
   `data_layout`, `align_of::<u128>()` takes every power of two in
   `{1, 2, 4, 8, 16}` bytes, `align_of::<u64>()` and `align_of::<f64>()` take
   every power of two in `{1, 2, 4, 8}` bytes (and disagree with each other on
   `m68k-unknown-linux-gnu` and `powerpc64-ibm-aix`), and `i686-pc-windows-msvc`
   exhibits a Tier 1 ABI bug where `align_of::<u64>() == 8` exceeds the 4-byte
   guaranteed stack frame alignment (`rust-lang/unsafe-code-guidelines#461`).
   Moreover, if a custom target JSON sets aggregate alignment `a:16` or `a:32`
   (`dl.aggregate_align > 1`), `LayoutCalculator::univariant_biased` pads even
   `#[repr(C)] struct ReprCU8(u8)` and `#[repr(transparent)] struct TransU8(u8)`
   to `size = 4, align = 4` (`BackendRepr::Memory`), violating
   `r[layout.repr.c.struct.align]` and `r[layout.repr.transparent.layout-abi]`.
   Separately, `#[repr(C)]` sets `ReprFlags::ABI_UNOPTIMIZABLE`, suppressing
   single-field scalar ABI optimization so `#[repr(C)]` wrapper structs have
   incompatible `extern "C"` register/stack calling conventions (`PassMode`)
   relative to their inner primitive on `x86_64-pc-windows-msvc`,
   `i686-unknown-linux-gnu`, `x86_64-unknown-linux-gnu`, and
   `aarch64-unknown-linux-gnu`.
3. **Pre-MIR crate-graph, `#[cfg]`, and open-world dependency resolution
   (SemVer snares)**: Because inactive `#[cfg(...)]` branches are stripped at
   the token/AST level before name resolution, HIR lowering, type checking, or
   MIR construction—and because SemVer-minor upstream updates (adding private
   fields, raising alignment, changing a private 1-ZST, adding a trait
   implementation or inherent method, or unifying additive Cargo features in a
   diamond dependency) can silently alter downstream layout, trait selection, or
   method dispatch without any edit to downstream source files—universal
   pre-compilation verification over the open-world space of all future Cargo
   resolutions and `#[cfg]` configurations is both ill-defined and undecidable.
   Sound verification must instead certify a concrete resolved crate graph and
   active `#[cfg]` slice (binding certificates to upstream crate
   `StableCrateId`/SVH fingerprints or treating foreign non-`#[repr(C)]` types
   abstractly), universally quantify over all Reference-admissible compiler
   layout choices (`ReferenceAdmissible(tau)`), and either quantify over or
   specialize to target parameters satisfying an explicit `ValidTargetSpec(tau)`
   precondition.

## Applicability

This report examines and compares five pinned subjects:

- **The Rust Reference** at `rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`
  (bundled with stable `rustc 1.99.1 (58cf8f9c3 2026-10-13)`) and
  `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (bundled with
  `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`), defining the normative
  language-level layout and representation contract (`r[layout.*]`, `r[type.*]`,
  `r[dynamic-sized.*]`, `r[items.union.*]`).
- **Rust compiler and standard library** at
  `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly
  (2026-05-30)`) and `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`
  (`1.99.1 (2026-10-13)`), covering `compiler/rustc_abi`,
  `compiler/rustc_ty_utils`, `compiler/rustc_target`, `compiler/rustc_middle`,
  `compiler/rustc_codegen_ssa`, `compiler/rustc_const_eval`,
  `compiler/rustc_lint`, and normative standard library layout documentation in
  `library/core` and `library/alloc`.
- **zerocopy** at `google/zerocopy@8fb35253fbc703cb2cd0997f4efcda76cf9062b6`,
  whose soundness policy (`POLICIES.md`) and layout derivations (`src/layout.rs`,
  `zerocopy-derive/src/derive/*`) operationalize forwards-compatible verification
  against the Rust Reference rather than pinned compiler coincidences.

Execution evidence was gathered on `x86_64-unknown-linux-gnu` using both
`rustc 1.98.0-nightly (f8a08b688 2026-05-30)` and `rustc 1.99.1 (58cf8f9c3
2026-10-13)`, including cross-target `-Z print-type-sizes` and `#[rustc_abi(debug)]`
compilations across built-in and custom target specifications. Claims labeled
**normative** apply to any Rust implementation conforming to the cited Reference
or `core`/`alloc` specification revision; claims labeled **source** or
**execution** apply to the identified `rust-lang/rust` revisions unless
explicitly derived from normative rules.

## Findings

### 1. Universal Layout Invariants and Normative Delta Between `ad35aca4` and `82da570b`

`Basis: normative + source + execution`

#### 1.1 Universal Layout Properties Across All Rust Types

Across all `Sized` types and dynamically sized values (via `size_of_val` and
`align_of_val`), the Rust Reference and `rustc` enforce four foundational
invariants:

| Invariant | Normative Reference Guarantee | `rustc` Implementation (`rust-lang/rust@f8a08b688cbe`) |
| :--- | :--- | :--- |
| **Alignment domain** | `r[layout.properties.align]` (`type-layout.html:194-198`): Alignment is measured in bytes, is at least `1`, and is always a power of two ($2^k \ge 1$). | `Align` stores $\log_2(\text{align}) \in 0..=29$. `Align::max_for_target` (`compiler/rustc_abi/src/lib.rs:1013-1028`) caps alignment at $2^{29}$ (`536_870_912`) bytes on 32/64-bit targets and $2^{15}$ (`32_768`) bytes on 16-bit targets so `isize` can represent aligned offsets. Checked in `layout_sanity_check` (`compiler/rustc_ty_utils/src/layout/invariant.rs:15`). |
| **Size is a multiple of alignment** | `r[layout.properties.size]` (`type-layout.html:184-193`): Size in bits is `8 * size_in_bytes`, and `size_in_bytes` is always a multiple of alignment (including `0`). | Asserted for every `Sized` type in `compiler/rustc_ty_utils/src/layout/invariant.rs:19-28` (`layout.size.bytes().is_multiple_of(layout.align.abi.bytes())`) and enforced for unsized values by rounding up to `full_align` in `size_and_align_of_dst` (`compiler/rustc_codegen_ssa/src/size_of_val.rs:176-180` and `compiler/rustc_const_eval/src/interpret/eval_context.rs:483-485`). |
| **Maximum size bound (`isize::MAX`)** | `r[layout.properties.size-maximum]` (`type-layout.html:199-203`) and `r[type.numeric.int.size.isize]`: Since Rust 1.44, the size in bytes of any `Sized` type cannot exceed `isize::MAX` ($2^{\text{pointer\_bits}-1} - 1$). | `TargetDataLayout::obj_size_bound` (`compiler/rustc_abi/src/lib.rs:724-726`) returns `1 << (pointer_bits - 1)` (`isize::MAX as u64 + 1`). `layout/invariant.rs:15` asserts `layout.size.bytes() < dl.obj_size_bound()`. For unsized DSTs in CTFE/Miri, `eval_context.rs:485,503` aborts if `size >= dl.obj_size_bound()`. |
| **Static vs. dynamic layout** | `r[layout.properties.static]` & `r[layout.properties.dynamic]` (`type-layout.html:204-213`): All values of a `Sized` type share compile-time `size_of::<T>()` and `align_of::<T>()`; values of `?Sized` types have runtime `size_of_val` and `align_of_val` subject to the same alignment/multiple invariants. | `LayoutData::is_sized()` holds when `!self.is_unsized()`, i.e., `BackendRepr` is not `Memory { sized: false }`. |

#### 1.2 Normative Reference Changes Between `ad35aca4` (`1.98.0-nightly`) and `82da570b` (`1.99.1`)

Diffing `type-layout.html` between `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`
and `rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` identifies
three normative layout additions:

1. **`r[layout.repr.rust.struct-zst]` added in `82da570b` (`type-layout.html:421-424`,
   `rust-lang/reference#2262`)**:
   > *"If a struct has no fields, or if all of its fields have a size of 0, then
   > the struct itself is guaranteed to have a size of 0."*
   In `ad35aca4`, `type-layout.html` did not guarantee that `struct Empty;` or
   `struct ZstFields((), PhantomData<u64>);` had `size == 0` (only `()` had a
   normative zero-size guarantee via `r[layout.tuple.unit]`, and empty enums via
   `r[layout.enum.empty]`). However, `rust-lang/rust@f8a08b688cbe` already
   implemented and cited PR #2262 in `compiler/rustc_abi/src/lib.rs:96-99` and
   `compiler/rustc_abi/src/layout.rs:1112-1115`.
2. **`r[layout.repr.rust.enum-struct-like-zst]` added in `82da570b`
   (`type-layout.html:425-428`, `rust-lang/reference#2293`)**:
   > *"If an enum has a single variant, does not have a primitive
   > representation, and all of the fields of that variant have a size of 0,
   > then the enum itself is guaranteed to have a size of 0."*
   Also cited in `compiler/rustc_abi/src/lib.rs:97` at `f8a08b688cbe`.
3. **`r[layout.repr.c.struct.align]` clarified in `82da570b`
   (`type-layout.html:450-453`)**:
   Updated from *"The alignment of the struct is the alignment of the
   most-aligned field in it."* (`ad35aca4`) to *"The alignment of the struct is
   the alignment of the most-aligned field in it, **or one if there are no
   fields**."* (`82da570b`), aligning `r[layout.repr.c.struct.align]` with
   `r[layout.repr.c.struct.fieldless]`.

---

### 2. Complete Layout Taxonomy Across Rust Type Constructors

`Basis: normative + documentation + source + execution`

#### 2.1 Primitives and Pointers

| Type Constructor | Normative Reference / `core` Guarantee | `rustc` Implementation (`compiler/rustc_ty_utils/src/layout.rs`, `rustc_abi`) | Verified on `x86_64-unknown-linux-gnu` (`support/layout_probes_output.json`) |
| :--- | :--- | :--- | :--- |
| `bool` | `r[layout.primitive.size]`, `r[type.bool.layout]`, `r[type.bool.validity]`: `size = 1`, `align = 1`. Valid bit patterns: `0x00` (`false`) and `0x01` (`true`); `0x02..=0xFF` are immediate UB (`r[undefined.invalid]`). | `ty::Bool` (`layout.rs:344-349`): `Scalar::Initialized { value: Int(I8, false), valid_range: 0..=1 }`, `align = dl.i8_align` (`1`). | `size = 1`, `align = 1` |
| `u8` / `i8` | `r[layout.primitive.size]`, `r[layout.primitive.integer-alignment]`, `r[type.numeric.validity]`: `size = 1`; since `1 <= align <= size` and `size % align == 0`, `align = 1` on all targets. All $2^8$ initialized bit patterns are valid. | `Int(I8)` / `Uint(U8)` (`layout.rs:359-368`): `valid_range: 0..=0xFF`, `align = dl.i8_align` (`1`). | `size = 1`, `align = 1` |
| `u16`/`i16`, `u32`/`i32`, `u64`/`i64`, `u128`/`i128` | `r[layout.primitive.size]`, `r[layout.primitive.integer-alignment]`, `r[layout.primitive.platform-specific-alignment]`: `size` is `2`, `4`, `8`, `16` bytes respectively; `align_of::<uN>() == align_of::<iN>()`; alignment is target-specific in $\{1, \dots, \text{size}\}$. In particular, `u128`/`i128` alignment is **not** guaranteed to be `16`. | `Int(I16..I128)` (`layout.rs:359-368`): `align` read from `dl.i16_align`, `dl.i32_align`, `dl.i64_align`, `dl.i128_align`. On `x86_64`, `i128_align` rose from `8` to `16` in Rust 1.77 (LLVM 18). | `(2, 2)`, `(4, 4)`, `(8, 8)`, `(16, 16)` |
| `f32` / `f64` | `r[layout.primitive.size]`, `r[layout.primitive.platform-specific-alignment]`, `r[type.numeric.validity]`: `size = 4` (`align in {1, 2, 4}`) and `size = 8` (`align in {1, 2, 4, 8}`). All initialized bit patterns (including all NaN payloads) are bit-valid. | `ty::Float(F32 / F64)` (`layout.rs:370-372`): `Primitive::Float` with `valid_range: full`, `align = dl.f32_align` / `dl.f64_align`. | `f32`: `(4, 4)`; `f64`: `(8, 8)` |
| `char` | `r[layout.primitive.size]`, `r[layout.primitive.char-alignment]`, `r[type.char.value]`, `r[type.char.validity]`: `size = 4`, **`align_of::<char>() == align_of::<u32>()` on all targets**. Valid Unicode scalar values: `0x0000..=0xD7FF` and `0xE000..=0x10FFFF`. | `ty::Char` (`layout.rs:350-356`): `Scalar::Initialized { value: Int(I32, false), valid_range: 0..=0x10FFFF }`. Because `rustc_abi::Scalar` stores a single contiguous `WrappingRange`, the UTF-16 surrogate hole `0xD800..=0xDFFF` is **not** exposed as an enum niche range in `rustc_abi` (though Miri/CTFE enforces it during value validity checks). | `size = 4`, `align = 4` |
| `!` (Never) | `r[type.never.intro]`, `r[undefined.invalid]`: Uninhabited. `type-layout.html` does not explicitly state `size_of::<!>()` (unlike `r[layout.enum.empty]` for `enum Empty {}`), though `size = 0, align = 1` is required by `core`. | `ty::Never` (`layout.rs:148-158, 423`): `Variants::Empty`, `BackendRepr::Memory { sized: true }`, `align = dl.i8_align` (`1`), `size = Size::ZERO`. | `size = 0`, `align = 1` |
| `()` (Unit) | `r[layout.tuple.unit]` (`type-layout.html:312-315`): Guaranteed `size = 0`, `align = 1` on all targets. | `ty::Tuple` with 0 fields (`compiler/rustc_abi/src/layout.rs:943`): `size = 0`, `align = dl.i8_align` (`1`). | `size = 0`, `align = 1` |
| `usize` / `isize` | `r[layout.primitive.size-minimum]`, `r[layout.primitive.size-align]`, `r[layout.primitive.integer-alignment]`: Same size and alignment as thin data pointers (`*const ()`), `size >= 2` bytes (`>= 16` bits), `align_of::<usize>() == align_of::<isize>()`. | Mapped via `dl.ptr_sized_integer()` (`compiler/rustc_abi/src/lib.rs:733-740`) to `I16`, `I32`, or `I64` with `dl.pointer_align()`. | `size = 8`, `align = 8` |
| Thin data pointers (`*const T`, `*mut T`, `&T`, `&mut T` for `T: Sized`) | `r[layout.pointer.intro]`, `r[layout.pointer.thin]`, `r[layout.primitive.size-align]`: Identical size and alignment to each other and to `usize`. `&T` and `&mut T` have non-null validity (`1..=usize::MAX`). | `scalar_unit(Pointer(AddressSpace::ZERO))` (`layout.rs:375-419`); for `Ref`, `valid_range_mut().start = 1`. | `size = 8`, `align = 8` |
| Function pointers (`[unsafe] [extern "ABI"] fn(...) -> R`) | `r[type.fn-pointer]`, `library/core/src/option.rs:137,153-155`: Guaranteed non-null niche (`Option<fn(...)>` has the same size, alignment, and ABI as `fn(...)`, with all-zero bytes representing `None`). Note: `r[layout.pointer.thin]` omits `fn(...)` from its list of thin pointers guaranteed to match `usize` size/align. | `ty::FnPtr` (`layout.rs:431-435`): `scalar_unit(cx, Primitive::Pointer(dl.instruction_address_space))` with `valid_range.start = 1`. Uses `dl.instruction_address_space` (`AddressSpace(1)` on `avr-none`; `AddressSpace::ZERO` on all other built-in targets). | `size = 8`, `align = 8` |
| Wide pointers (`*const T`, `*mut T`, `&T`, `&mut T` for `T: ?Sized` DSTs) | `r[layout.pointer.intro]`: `*const T`, `*mut T`, `&T`, `&mut T` share size and alignment for a given `T: ?Sized`. **Internal Reference tension**: `r[layout.pointer.unsized]` (`type-layout.html:269-279`) states only `size >= size_of::<*const ()>()` and `align >= align_of::<*const ()>()`, whereas `r[dynamic-sized.pointer-types]` (`dynamically-sized-types.html:196-207`) normatively states that pointers to DSTs *"have twice the size of pointers to sized types"*. **Word order `(data_ptr, metadata)` vs. `(metadata, data_ptr)` is not guaranteed by the Reference.** | `LayoutData::scalar_pair(cx, data_ptr, metadata)` (`compiler/rustc_ty_utils/src/layout.rs:476-520`, `compiler/rustc_abi/src/layout.rs:285-315`): **`data_ptr` is always at byte offset `0` (word 0) and `metadata` (`len` or non-null `vtable` pointer) is always at byte offset `pointer_size` (word 1)**, with `size = 2 * pointer_size` and `align = pointer_align`. | `size = 16`, `align = 8`, `word0 == data_addr`, `word1 == len` |

#### 2.2 Arrays `[T; N]`, Slices `[T]`, and `str`

- **`[T; N]` (`r[layout.array]`, `type-layout.html:281-285`)**:
  $$\text{size}([T; N]) = \text{size}(T) \times N, \qquad \text{align}([T; N]) = \text{align}(T), \qquad \text{offset}(i) = i \times \text{size}(T)$$
  Because $\text{size}(T)$ is already a multiple of $\text{align}(T)$
  (`r[layout.properties.size]`), arrays have zero inter-element padding. For
  $N = 0$, $\text{size}([T; 0]) = 0$ while $\text{align}([T; 0]) = \text{align}(T)$
  (so `[u32; 0]` is a ZST with `align = 4`, not a 1-ZST).
  - **Opportunistic array niche propagation in `rustc_abi`**: In
    `LayoutData::array` (`compiler/rustc_abi/src/layout.rs:331-334`), `rustc`
    sets `largest_niche = if count != 0 { element.largest_niche } else { None }`.
    Consequently, `Option<[NonZeroU32; 2]>` has `size = 8, align = 4` in `rustc`
    (`support/layout_probes_output.json`), encoding `None` in element `0`. This
    niche propagation is an unguaranteed compiler optimization.
- **`[T]` (`r[layout.slice]`, `type-layout.html:286-297`)**: A slice of runtime
  length $N$ has the exact same layout as `[T; N]`:
  $\text{size\_of\_val}(s) = \text{size}(T) \times \text{len}(s)$ and
  $\text{align\_of\_val}(s) = \text{align}(T)$.
- **`str` (`r[layout.str]`, `type-layout.html:299-303`; `r[type.str.layout]`,
  `types/str.html:195-218`)**: `str` has the exact same layout as `[u8]`
  ($\text{size\_of\_val}(s) = \text{len}(s)$, $\text{align\_of\_val}(s) = 1$),
  and `&str` has the exact same layout as `&[u8]`.

#### 2.3 Tuples `(T_0, ..., T_k)` and Default `#[repr(Rust)]` Structs

- **Normative Reference Rules (`r[layout.tuple.def]`, `r[layout.tuple.unit]`,
  `r[layout.struct.def]`, `r[layout.repr.rust.*]`, `type-layout.html:308-320,
  400-432`)**:
  - Except for `()` (`size = 0, align = 1`), tuples and structs without a `repr`
    attribute use the `Rust` representation.
  - For any `#[repr(Rust)]` struct or non-unit tuple $S$ with fields
    $F_0, \dots, F_{n-1}$, the Reference guarantees **only**:
    1. $\text{align}(S) = 2^k \ge \max_i \text{align}(F_i)$ (when not lowered by
       `packed(P)`). Crucially, this is an inequality ($\ge$), **not** an
       equality ($=$).
    2. $\text{size}(S)$ is a multiple of $\text{align}(S)$ and
       $\text{size}(S) \le \text{isize::MAX}$.
    3. Every field offset satisfies
       $\text{offset}(F_i) \equiv 0 \pmod{\text{align}(F_i)}$ (when not lowered
       by `packed(P)`).
    4. For structs, field byte intervals
       $[\text{offset}(F_i), \text{offset}(F_i) + \text{size}(F_i))$ are
       pairwise disjoint (`r[layout.repr.rust.layout.struct]`), implying
       $\text{size}(S) \ge \sum_i \text{size}(F_i)$ (while allowing zero-sized
       fields to share offsets with other fields).
    5. Under `rust-lang/reference@82da570b` (`1.99.1`), if a struct has no
       fields or all of its fields have $\text{size}(F_i) = 0$, then
       $\text{size}(S) = 0$ (`r[layout.repr.rust.struct-zst]`).
- **Critical Non-Guarantees for `#[repr(Rust)]` Structs and Tuples**:
  1. **Single-field `#[repr(Rust)]` structs (`struct Single(u64)`) and 1-tuples
     (`(u64,)`) with a non-ZST field**: The Reference does **not** guarantee
     $\text{size}(\text{Single}) = \text{size}(\text{u64})$, does **not**
     guarantee $\text{align}(\text{Single}) = \text{align}(\text{u64})$, and
     does **not** guarantee $\text{offset}(0) = 0$. A conforming Rust compiler
     may insert arbitrary leading or trailing padding unless
     `#[repr(transparent)]` or `#[repr(C)]` is specified.
  2. **Alignment of `#[repr(Rust)]` ZST structs (`struct Empty;`,
     `struct ZstFields((), PhantomData<u64>);`)**: Even under
     `r[layout.repr.rust.struct-zst]`, only $\text{size}(S) = 0$ is guaranteed;
     $\text{align}(S) = 1$ is **not** guaranteed because `r[layout.repr.rust.layout]`
     only bounds $\text{align}(S) \ge \max_i \text{align}(F_i)$ from below.
  3. **Non-unit all-ZST tuples (`((), ())`)**: `r[layout.repr.rust.struct-zst]`
     is phrased in terms of *structs* and omits non-unit all-ZST tuples, even
     though `rustc_abi` routes both structs and tuples through
     `LayoutCalculator::layout_of_struct_or_tuple`
     (`compiler/rustc_abi/src/layout.rs:943, 1112-1115`).
- **How `zerocopy` (`google/zerocopy@8fb35253fb`) Differentiates Traits on
  `#[repr(Rust)]` Structs**:
  - `FromZeros`, `FromBytes`, and `TryFromBytes` are permitted on `#[repr(Rust)]`
    structs when all field types implement the trait, because field validity at
    arbitrary aligned offsets (plus arbitrary padding for `FromZeros`/`FromBytes`)
    is invariant under field permutation and extra padding.
  - `IntoBytes` (`zerocopy-derive/src/derive/into_bytes.rs:124-145`,
    `src/util/macro_util.rs:297-315`) is permitted on concrete `Sized`,
    non-generic `#[repr(Rust)]` structs by emitting a compile-time assertion
    `size_of::<S>() == size_of::<F_0>() + ... + size_of::<F_{n-1}>()`. By
    `r[layout.repr.rust.layout.struct]` (pairwise non-overlapping field
    intervals), equality between total struct size and the sum of field sizes
    proves by pigeonhole that `S` contains zero padding bytes regardless of
    field order.
  - `Unaligned` (`zerocopy-derive/src/derive/unaligned.rs:19-40`) is
    **rejected** on `#[repr(Rust)]` structs—even `struct Empty;` or
    `struct Wrap(u8);`—requiring `#[repr(C)]`, `#[repr(transparent)]`, or
    `#[repr(packed)]`, because `r[layout.repr.rust.layout]` only guarantees
    $\text{align}(S) \ge 1$, not $\text{align}(S) = 1$.

#### 2.4 `#[repr(C)]`, `#[repr(transparent)]`, `#[repr(packed(N))]`, and `#[repr(align(N))]`

- **`#[repr(C)]` Structs (`r[layout.repr.c.struct.*]`, `type-layout.html:449-574`)**:
  Given fields $F_0, \dots, F_{n-1}$:
  $$\text{align}(S) = \begin{cases} 1 & \text{if } n = 0 \\ \max_{0 \le i < n} \text{align}(F_i) & \text{if } n > 0 \end{cases}$$
  $$\text{offset}_0 = 0, \quad \text{field\_offset}(F_i) = \text{round\_up}(\text{offset}_i, \text{align}(F_i)), \quad \text{offset}_{i+1} = \text{field\_offset}(F_i) + \text{size}(F_i)$$
  $$\text{size}(S) = \text{round\_up}(\text{offset}_n, \text{align}(S))$$
  Zero-sized fields (`r[layout.repr.c.struct.zst]`, `type-layout.html:551-574`)
  participate in the exact same recurrence: a ZST field $F_i$ with
  $\text{align}(F_i) > 1$ (such as `[u32; 0]`) raises $\text{align}(S)$ to at
  least $\text{align}(F_i)$ and advances $\text{offset}_i$ to the next multiple
  of $\text{align}(F_i)$ while adding `0` to $\text{offset}_{i+1}$
  (`CWithZstAlign4 { a: u8, z: [u32; 0], b: u8 }` has `size = 8, align = 4,
  off_a = 0, off_z = 4, off_b = 4` in `support/layout_probes_output.json`).
- **`#[repr(transparent)]` (`r[layout.repr.transparent.*]`,
  `type-layout.html:917-958`)**:
  - Allowed on any struct or single-variant enum with any number of **1-ZST**
    fields (`size == 0 && align == 1`) and **at most one** other field $F_{\text{inner}}$
    (which may have arbitrary size, arbitrary alignment, and may be `?Sized`).
  - Cannot be combined with any other `repr` attribute (`E0692`).
  - Guarantees identical `size`, `align`, validity, niches (except for
    `UnsafeCell`/`UnsafePinned`, see §2.6), and function-call ABI (`PassMode`)
    as $F_{\text{inner}}$, with $\text{offset}(F_{\text{inner}}) = 0$.
- **Composition Matrix for `#[repr(packed(N))]` and `#[repr(align(N))]`
  (`r[layout.repr.alignment.*]`, `type-layout.html:855-916`)**:

| Composition | Alignment Equation | Field Offset & Size Equation | Normatively Guaranteed by Reference? |
| :--- | :--- | :--- | :--- |
| `#[repr(C, packed(N))]` struct | $\text{align}(S) = \min(N, \max_i \text{align}(F_i))$ (or $1$ if fieldless) | Each field $F_i$ in declaration order uses effective alignment $a'_i = \min(N, \text{align}(F_i))$: $\text{field\_offset}(F_i) = \text{round\_up}(\text{offset}_i, a'_i)$ and $\text{size}(S) = \text{round\_up}(\text{offset}_n, \text{align}(S))$. For $N = 1$, zero inter-field and trailing padding: $\text{field\_offset}(F_i) = \sum_{j < i} \text{size}(F_j)$, $\text{size}(S) = \sum_i \text{size}(F_i)$. | **Yes** (`r[layout.repr.c.struct]` + `r[layout.repr.alignment.packed]` + `r[layout.repr.alignment.packed-fields]`). |
| `#[repr(Rust, packed(N))]` struct | For $N = 1$: $\text{align}(S) = 1$. For $N > 1$: $\min(N, \max_i \text{align}(F_i)) \le \text{align}(S) \le N$. | **Field order is NOT guaranteed.** `packed(N)` lowers field alignments to $\min(N, \text{align}(F_i))$, eliminating padding when $N = 1$, **but `#[repr(Rust, packed(1))]` still reorders fields** (`!repr.inhibit_struct_field_reordering()`). | **Size and `align = 1` (for $N = 1$): Yes. Field order: No.** In `support/layout_probes_output.json`, `RustPacked1Het { a: u8, b: u32, c: u16 }` has offsets `(0, 1, 5)` by default, `(6, 2, 0)` at `seed=42`, and `(0, 3, 1)` at `seed=7`. |
| `#[repr(C, align(N))]` struct | $\text{align}(S) = \max(N, \max_i \text{align}(F_i))$ | Inter-field offsets are identical to `#[repr(C)]` ($\text{field\_offset}(F_i) = \text{round\_up}(\text{offset}_i, \text{align}(F_i))$); only final trailing padding is rounded up to the raised $\text{align}(S)$. | **Yes** (`r[layout.repr.c.struct]` + `r[layout.repr.alignment.align]`). Verified on `CAlign16Het`: `size = 16, align = 16, off_a = 0, off_b = 4, off_c = 8`. |
| `#[repr(Rust, align(N))]` struct | $\text{align}(S) \ge \max(N, \max_i \text{align}(F_i))$ | Raises the lower bound on $\text{align}(S)$; fields remain subject to arbitrary `repr(Rust)` reordering and padding. | **Only lower bound $\text{align}(S) \ge N$ and `size % align == 0`**. |

- **Generic Indirection Bypasses `r[layout.repr.alignment.constraint-packed-contains-align]` (`E0588`)**:
  - `r[layout.repr.alignment.constraint-packed-contains-align]` states that a
    `packed` type cannot transitively contain an `align(N)` type. Direct nominal
    containment (`#[repr(C, packed(2))] struct Direct { x: u8, inner: InnerCAlign16 }`)
    is rejected with `E0588` because `rustc_passes::check_attr` and
    `compiler/rustc_ty_utils/src/layout.rs:584` walk concrete nominal fields.
  - However, when `Outer` is generic (`#[repr(C, packed(2))] struct
    GenericOuterCPacked2<T> { x: u8, inner: T }`) and monomorphized as
    `GenericOuterCPacked2<InnerCAlign16>`, `rustc` accepts the type without
    error (`generic_outer_c_packed2_over_c_align16` in
    `support/layout_probes_output.json`): `InnerCAlign16` retains its internal
    `size = 16`, while `GenericOuterCPacked2` caps its field alignment to
    $\min(2, 16) = 2$, placing `inner` at `offset = 2` and yielding outer
    `size = 18, align = 2`. `zerocopy` (`src/layout.rs:1080-1088`) explicitly
    documents and relies on this composition rule via `r[layout.repr.intro]`
    (*"reprs do not change the layout of fields themselves"*).

#### 2.5 Unions (`#[repr(Rust)]` Union vs. `#[repr(C)]` Union)

- **Normative Reference Distinction**:
  - For a default `#[repr(Rust)]` union (`r[type.union.layout]`,
    `types/union.html:246-249`; `r[items.union.fields.offset]`,
    `items/unions.html:5050-5053`), the Reference explicitly states that
    **there is no guarantee that the fields of the union are all at offset 0**.
  - For a `#[repr(C)]` union (`r[layout.repr.c.union.size-align]`,
    `type-layout.html:584-592`), the Reference guarantees:
    $$\text{align}(U) = \max\!\left(1, \max_{0 \le i < n} \text{align}(F_i)\right), \quad \text{size}(U) = \text{round\_up}\!\left(\max_{0 \le i < n} \text{size}(F_i),\; \text{align}(U)\right), \quad \forall i,\; \text{offset}(F_i) = 0$$
- **Actual `rustc_abi` Implementation (`LayoutCalculator::layout_of_union`,
  `compiler/rustc_abi/src/layout.rs:395-520`)**:
  - Every union in `rustc` (`#[repr(Rust)]` and `#[repr(C)]` alike) is assigned
    `FieldsShape::Union(NonZero::new(fields.len())?)`, for which
    `FieldsShape::offset(i)` (`compiler/rustc_abi/src/lib.rs:948-950`)
    unconditionally returns `Size::ZERO`—even under `-Z randomize-layout`.
  - Both `#[repr(Rust)]` and `#[repr(C)]` unions compute the identical `size`
    and `align`, and both set `largest_niche = None`.
  - The **sole difference** between `#[repr(Rust)]` and `#[repr(C)]` unions in
    `rustc_abi` (`layout.rs:451-505`, `lib.rs:245-247`) is
    `repr.inhibits_union_abi_opt()` (`self.c()`): a `#[repr(C)]` union always
    gets `BackendRepr::Memory { sized: true }`, whereas a `#[repr(Rust)]` union
    is eligible for `BackendRepr::Scalar(Scalar::Union { value })`,
    `ScalarPair`, or `SimdVector` register passing when all non-ZST fields share
    a compatible primitive/vector representation.

#### 2.6 Enums, Discriminants, and Guaranteed vs. Opportunistic Niche Optimizations

- **Enum Representations (`r[layout.enum.empty]`, `r[layout.repr.c.enum.*]`,
  `r[layout.repr.primitive.*]`, `r[layout.repr.c-primitive.*]`)**:
  - **Empty `#[repr(Rust)]` enum (`enum Infallible {}`)**: Guaranteed
    `size = 0, align = 1` (`r[layout.enum.empty]`).
  - **Single-variant non-primitive `#[repr(Rust)]` enum with all-ZST fields**:
    Guaranteed `size = 0` (`r[layout.repr.rust.enum-struct-like-zst]` in
    `82da570b`).
  - **`#[repr(C)]` fieldless enum (`r[layout.repr.c.enum.fieldless]`)**: Same
    size and alignment as the target's default C `enum` type (`c_int` unless
    discriminants exceed `c_int` or `-fshort-enums` / `short_enums` applies;
    see §4.4).
  - **`#[repr(Int)]` fieldless enum (`r[layout.repr.primitive.fieldless]`)**:
    Same size, alignment, and valid discriminant bit patterns as `Int`.
  - **`#[repr(C)]` enum with fields (`r[layout.repr.c.enum.fields]`) vs.
    `#[repr(C, Int)]` enum with fields (`r[layout.repr.c-primitive]`) vs.
    `#[repr(Int)]` enum with fields (`r[layout.repr.primitive.fields]`)**:
    - Both `#[repr(C)]` and `#[repr(C, Int)]` enums with fields are laid out as
      a **2-field `#[repr(C)]` struct `(TagType, PayloadUnion)`**, where
      `PayloadUnion` is a `#[repr(C)]` union of per-variant `#[repr(C)]`
      structs. Consequently, **every variant's first payload field starts at
      $\text{round\_up}(\text{size}(\text{TagType}), \max_{v,f} \text{align}(F_{v,f}))$**.
      For `#[repr(C, u8)] enum CU8 { A(u8), B(u64) }`, `A.0` (`u8`) sits at
      **byte offset `8`** (after 1 byte tag and 7 bytes padding), not offset `1`!
    - By contrast, a `#[repr(Int)]` enum with fields (without `C`) is laid out
      as a **`#[repr(C)]` union of per-variant `#[repr(C)]` structs
      `(Int, F_{v,0}, F_{v,1}, ...)`**, each starting with the `Int` tag at
      offset `0`. Consequently, variant $v$'s first payload field $F_{v,0}$ sits
      at $\text{round\_up}(\text{size}(\text{Int}), \text{align}(F_{v,0}))$. For
      `#[repr(u8)] enum U8 { A(u8), B(u64) }`, `B.0` (`u64`) sits at **offset
      `8`**, whereas `A.0` (`u8`) sits at **offset `1`**!
- **Closed Set $\mathcal{N}_{\text{Option}}$ of Normatively Guaranteed `Option<T>`
  and `Result<T, 1-ZST>` Niche Optimizations (`library/core/src/option.rs:116-159`,
  `library/core/src/result.rs:232-259`)**:
  - `Option<T>` is normatively guaranteed to have the **exact same size,
    alignment, and function-call ABI** as `T` if and only if `T` belongs to the
    inductive family $\mathcal{N}_{\text{Option}}$:
    1. `Box<U, alloc::alloc::Global>` (for any `U: ?Sized`),
    2. `&U` (for any `U: ?Sized`),
    3. `&mut U` (for any `U: ?Sized`),
    4. `[unsafe] [extern "ABI"] fn(...) -> Ret` (any arity, safety, and ABI),
    5. `core::num::NonZero<Primitive>` (`NonZeroU8..=NonZeroU128`,
       `NonZeroI8..=NonZeroI128`, `NonZeroUsize`, `NonZeroIsize`, `NonZero<char>`),
    6. `core::ptr::NonNull<U>` (for any `U: ?Sized`),
    7. Any `#[repr(transparent)]` struct (including `ManuallyDrop<Inner>`)
       wrapping one field in $\mathcal{N}_{\text{Option}}$ and any number of
       1-ZST fields (`size == 0 && align == 1`)—**excluding `UnsafeCell` and
       `UnsafePinned` (and therefore `Cell`)**.
  - For all thin-pointer members of $\mathcal{N}_{\text{Option}}$ (`U: Sized` in
    1–3 and 6, plus all `fn` pointers, all `NonZero<Primitive>`, and
    `#[repr(transparent)]` wrappers around them), `option.rs:150-159`
    additionally guarantees that `transmute::<_, Option<T>>([0u8; size_of::<T>()])`
    is sound and produces `None`. (Wide pointers `U: ?Sized` are excluded from
    the all-zeros transmute guarantee because the metadata word at offset
    `pointer_size` is uninitialized in `None`.)
  - Furthermore, `library/core/src/result.rs:232-259` normatively guarantees
    that for every $T \in \mathcal{N}_{\text{Option}}$ and every **1-ZST** type
    $Z$ (`size == 0 && align == 1`), both `Result<T, Z>` and `Result<Z, T>` have
    the exact same size, alignment, and ABI as `Option<T>` (and `T`). If $Z$ has
    $\text{align}(Z) > 1$ (e.g., `Result<NonZeroU8, [u32; 0]>`), this guarantee
    does not apply (`size = 4, align = 4` in `support/layout_probes_output.json`).
- **Three Niche Traps and Opportunistic `rustc` Niches**:
  1. **`UnsafeCell<T>` and `Cell<T>` Strip Niches Despite `#[repr(transparent)]`**:
     Both `UnsafeCell<T>` (`library/core/src/cell.rs:2309`) and `Cell<T>`
     (`cell.rs:308`) carry `#[repr(transparent)]`. However,
     `compiler/rustc_ty_utils/src/layout.rs:717` sets
     `is_special_no_niche = def.is_unsafe_cell() || def.is_unsafe_pinned()` and
     calls `layout.without_niche(cx)` (`compiler/rustc_abi/src/layout.rs:1357-1369`)
     so interior mutation through `&Option<Cell<&u8>>` cannot clobber a
     niche-encoded discriminant. Thus `Option<UnsafeCell<&u8>>` and
     `Option<Cell<&u8>>` have `size = 16, align = 8` on 64-bit targets.
  2. **`MaybeUninit<T>` Strips Niches**: `MaybeUninit<T>`
     (`library/core/src/mem/maybe_uninit.rs:125-129`) is `#[repr(transparent)]`
     around a **`union`** (`ManuallyDrop<T>` and `()`), and unions have
     `largest_niche = None`, so `Option<MaybeUninit<&u8>>` has `size = 16, align = 8`.
  3. **Opportunistic (Non-Guaranteed) Niches vs. Exhausted Niches**:
     `rustc_abi` opportunistically niche-optimizes `Option<bool>` (`size = 1`),
     `Option<char>` (`size = 4`), `Option<cmp::Ordering>` (`size = 1`),
     `Option<Infallible>` (`size = 0`), `Option<(NonZeroU32, u32)>` (`size = 8`),
     and `Option<[NonZeroU32; 2]>` (`size = 8`), none of which are guaranteed by
     the Reference or `core`. Conversely, `Option<Option<&u8>>` has
     **`size = 16, align = 8`** because `&u8` has only a single niche value (`0`),
     which `Option<&u8>` consumes (`valid_range = 0..=u64::MAX`), leaving zero
     niches for the outer `Option`.

#### 2.7 Unsized / Dynamically Sized Structs (DSTs with `[T]`, `str`, or `dyn Trait` Tails)

- **Normative `#[repr(C)]` Slice-DST Equations (`r[layout.repr.c.struct.zst]`,
  `type-layout.html:551-555`, combined with `r[layout.repr.c.struct]`,
  `r[layout.slice]`, and `r[layout.repr.intro]`)**:
  - `r[layout.repr.c.struct.zst]` specifies that `#[repr(C)]` structs containing
    zero-sized types **or dynamically-sized types** are laid out according to the
    standard `#[repr(C)]` struct algorithm, and `r[layout.slice]` specifies that
    a slice `[T]` of dynamic length $N$ has the layout of `[T; N]`.
  - Therefore, for an unnested `#[repr(C)]` struct $S$ with `Sized` prefix
    fields $F_0, \dots, F_{k-1}$ ending at byte offset $\text{prefix\_end}$ with
    $\text{prefix\_align} = \max_{i < k} \text{align}(F_i)$ (or $1$ if $k = 0$)
    and trailing slice field $F_k : [T]$ of runtime length $N$:
    $$\text{align\_of\_val}(S) = \max(\text{prefix\_align}, \text{align}(T)), \qquad \text{offset}(\text{tail}) = \text{round\_up}(\text{prefix\_end}, \text{align}(T))$$
    $$\text{size\_of\_val}(S) = \text{round\_up}\!\left(\text{offset}(\text{tail}) + N \times \text{size}(T),\; \text{align\_of\_val}(S)\right)$$
- **Nested Packed Slice DSTs (`OuterPacked<InnerReprC<[T]>>`) and `zerocopy`'s
  `TrailingSliceLayout`**:
  - When an inner `#[repr(C)]` slice DST `Inner<[u32]>` (`b: u8, tail: [u32]`,
    which has 3 bytes of internal padding and alignment `4`) is nested inside an
    outer `#[repr(C, packed(2))]` struct `Outer { a: u8, inner: Inner<[u32]> }`,
    the outer `packed(2)` lowers `Inner`'s field alignment inside `Outer` to
    $\min(2, 4) = 2$ (placing `inner` at offset `2`), **without** removing
    `Inner`'s internal 3-byte padding or changing `Inner`'s internal rounding
    multiple of `4`. Consequently, `tail` sits at byte offset `2 + 4 = 6`, and
    for $N = 1$, $\text{size\_of\_val}(\text{Outer}) = 2 + (4 + 4 \times 1) = 10$
    with $\text{align\_of\_val}(\text{Outer}) = 2$
    (`outer_packed2_over_inner_c_dst_u32_len1` in
    `support/layout_probes_output.json`), which `zerocopy` tracks via
    `TrailingSliceLayout::size_rounding_align_and_phase`
    (`zerocopy/src/layout.rs:1090-1260`).
- **Compile-Time Prefix Layout vs. Runtime `size_and_align_of_dst` in `rustc`
  (`compiler/rustc_codegen_ssa/src/size_of_val.rs:92-183`,
  `compiler/rustc_const_eval/src/interpret/eval_context.rs:436-489`)**:
  - For an unsized struct $S$ with static `sized_size`, static `sized_align`,
    optional `packed(P)` cap, and static last-field offset
    `unsized_offset_unadjusted = offsets[n - 1]`:
    1. If the base tail is `[T]`/`str`, static layout already knows
       $\text{align}(T)$, so `offsets[n - 1]` already includes alignment to
       $\min(P, \text{align}(T))$ (`compiler/rustc_abi/src/layout.rs:1244-1260`).
    2. If the base tail is `dyn Trait`, static `ty::Dynamic` has `size = 0,
       align = 1` (`compiler/rustc_ty_utils/src/layout.rs:456-462`), so
       `offsets[n - 1]` stores the unadjusted prefix end. At runtime,
       `size_and_align_of_dst` reads `(unsized_size, unsized_align_raw)` from
       the vtable, caps $\text{unsized\_align} = \min(\text{unsized\_align\_raw}, P)$,
       computes $\text{full\_align} = \max(\text{sized\_align}, \text{unsized\_align})$,
       aligns $\text{offset}(\text{tail}) = \text{round\_up}(\text{unsized\_offset\_unadjusted}, \text{unsized\_align})$,
       and rounds $\text{full\_size} = \text{round\_up}(\text{offset}(\text{tail}) + \text{unsized\_size}, \text{full\_align})$.

---

### 3. Empirical `-Z randomize-layout` Behavior vs. Reference Non-Guarantees

`Basis: normative + source + execution`

Executing `support/randomize_layout_probe.rs` across default compilation and 16
seeds (`-Z randomize-layout -Z layout-seed=0..15`, captured in
`support/randomize_layout_probe.jsonl`) and `support/layout_probes.rs` across
stable `1.99.1`, nightly `1.98.0-nightly`, and seeds `7` and `42`
(`support/layout_probes_output.json`) establishes the exact boundary between what
`-Z randomize-layout` perturbs and what the Reference leaves unspecified:

| Type / Construct | Representation | Observed `(size, align)` Across Default & Seeds | Observed Field Offset / Niche Behavior Across Seeds | Randomized by `-Z randomize-layout`? | Guaranteed by Reference (`r[layout.*]`)? |
| :--- | :--- | :--- | :--- | :---: | :---: |
| `struct SingleRust(u64)` | `repr(Rust)` (1 field) | Always `(8, 8)` | Always `off0 = 0` | **No** | **No** (`r[layout.repr.rust.layout]`) |
| `struct SingleTrans(u64)` | `#[repr(transparent)]` | Always `(8, 8)` | Always `off0 = 0` | **No** | **Yes** (`r[layout.repr.transparent.layout-abi]`) |
| `struct SingleC(u64)` | `#[repr(C)]` | Always `(8, 8)` | Always `off0 = 0` | **No** | **Yes** (`r[layout.repr.c.struct.*]`) |
| `struct TransWithZst((), u64)` | `#[repr(transparent)]` | Always `(8, 8)` | `off0_zst in {0, 8}` (`0` in seeds `0..13`; `8` in default & seeds `14, 15`); `off1_u64 = 0` | **Yes (1-ZST offset only)** | **Yes** for `size = 8, align = 8, off1_u64 = 0`; 1-ZST offset is unspecified |
| `struct PairU32(u32, u32)` | `repr(Rust)` (2 equal fields) | Always `(8, 4)` | `(0, 4)` in default & `seed=42`; **`(4, 0)` in `seed=7`** | **Yes** | **No** |
| `struct MultiPaddedRust(u8, u16, u8)` | `repr(Rust)` (3 fields) | **`size in {4, 6}`**, `align = 2` (`4` in default & 11 seeds; **`6` in seeds `1, 4, 12, 14, 15`**) | 5 distinct `(off0, off1, off2)` tuples: `(2, 0, 3)`, `(0, 2, 1)`, `(1, 2, 0)` (`size = 4`); `(4, 2, 0)`, `(0, 2, 4)` (**`size = 6`**) | **Yes (both offsets and `size_of`)** | **No** |
| `struct TripleHet(u8, u32, u16)` | `repr(Rust)` (3 fields) | **`size in {8, 12}`**, `align = 4` (`8` in default & `seed=7`; **`12` in `seed=42`**) | `(6, 0, 4)` (`size = 8`) in default; **`(0, 4, 8)` (`size = 12`) in `seed=42`** | **Yes (both offsets and `size_of`)** | **No** |
| `#[repr(packed(1))] struct RustPacked1Het { a: u8, b: u32, c: u16 }` | `#[repr(Rust, packed(1))]` | Always `(7, 1)` | `(0, 1, 5)` in default; **`(6, 2, 0)` in `seed=42`**; **`(0, 3, 1)` in `seed=7`** | **Yes (field order)** | **Size & `align=1`: Yes; field order: No** |
| `struct WithUnsizableTail<T: ?Sized>(u8, u16, T)` at `T = u8` / `RustDst<[u16]>` | `repr(Rust)` (`StructKind::MaybeUnsized`) | `WithUnsizableTail<u8>`: **`size in {4, 6}`** (`4` in default & seeds `12, 14`; **`6` in 14 seeds**). `RustDst<[u16]>`: `off_tail in {6, 8}` | Tail field is pinned last in memory (`end = fields.len() - 1`), while prefix fields shuffle and shift the tail offset! | **Yes (prefix fields & tail offset)** | **No** |
| `(u8, u16, u8)` / `(u8, u32, u16)` | Tuple (`repr(Rust)`) | Always `(4, 2)` / `(8, 4)` | Always `(2, 0, 3)` / `(6, 0, 4)` across all seeds | **No** | **No** (`r[layout.tuple.def]`) |
| `union RustUnion { a: u8, b: u32, c: u16 }` | `repr(Rust)` union | Always `(4, 4)` | Always `(0, 0, 0)` across all seeds | **No** | **No** (`r[type.union.layout]`) |
| `struct NicheStructDiff(bool, NonZeroU8)` & `Option<...>` | `repr(Rust)` | Always `size = 2, opt_size = 2` | `(0, 1)` (`None` tag `2` at byte `0`, byte `1` uninit) vs. `(1, 0)` (`None` tag `2` at byte `1`, byte `0` uninit) | **Yes (niche offset)** | **No** |
| `struct NicheStructEqual(NonZeroU8, NonZeroU8)` & `Option<...>` | `repr(Rust)` | Always `size = 2, opt_size = 2` | `NicheBias::End` (`layout.rs:1244-1260`) picks whichever field lands last after shuffling (`off1 = 1` vs. `off0 = 1`) as the `Option` niche carrier | **Yes (which field carries niche)** | **No** |
| `enum MultiEnum { A(u8, u16, u8), B(u32, u8) }` | `repr(Rust)` enum | **`size in {8, 12}`**, `align = 4` (`8` in default & seeds `6, 9, 10, 11`; **`12` in 12 seeds**) | Shuffling variant fields expands variant `A` from `4` to `6` bytes, pushing the enum tag and expanding `MultiEnum` from `8` to `12` bytes | **Yes (`size_of` changes)** | **No** |

Three compiler mechanics in `rust-lang/rust@f8a08b688cbe` explain why
`-Z randomize-layout` is strictly weaker than Reference-admissible layout
nondeterminism:

1. **Single-field `#[repr(Rust)]` structs are skipped (`compiler/rustc_abi/src/layout.rs:1110-1140`)**:
   `LayoutCalculator::univariant_biased` guards field shuffling behind
   `if optimize_field_order && fields.len() > 1` and never synthesizes artificial
   leading or trailing padding. Consequently, `struct SingleRust(u64)` always
   receives `size = 8, align = 8, offset(0) = 0` in `rustc` even under
   `-Z randomize-layout`, despite having no normative size or offset guarantee
   under `r[layout.repr.rust.layout]`.
2. **Tuples never receive `ReprFlags::RANDOMIZE_LAYOUT`
   (`compiler/rustc_middle/src/ty/mod.rs:1593-1598` vs.
   `compiler/rustc_ty_utils/src/layout.rs:207-211, 571-576`)**:
   `RANDOMIZE_LAYOUT` is populated in `repr_options_of_def` for nominal ADT
   `DefId`s, whereas `ty::Tuple` calls `layout_of_struct_or_tuple` with
   `ReprOptions::default()`.
3. **`ReprFlags::IS_TRANSPARENT` is not in `FIELD_ORDER_UNOPTIMIZABLE`
   (`compiler/rustc_abi/src/lib.rs:98-101, 219-227`)**:
   `FIELD_ORDER_UNOPTIMIZABLE` contains only `IS_C | IS_SIMD | IS_SCALABLE |
   IS_LINEAR`. For `#[repr(transparent)] struct TransWithZst((), u64)`,
   `optimize_field_order` remains `true`, so `-Z randomize-layout` shuffles the
   1-ZST field `()` between offset `0` (before `u64`) and offset `8` (after
   `u64`), while `u64` remains at offset `0`.

---

### 4. Target Specification Spectrum, `#[repr(C)]` Divergences, and Calling-Convention (`PassMode`) Limits

`Basis: normative + documentation + source + execution`

#### 4.1 Programmatic Census of All 322 Built-In Targets (`support/target_matrix.json`)

Parsing all 322 target specifications in `compiler/rustc_target/src/spec/targets/*.rs`
at `rust-lang/rust@f8a08b688cbe` (`307` with inline `data_layout` strings and
`15` delegating via base target helper functions) using the exact rules of
`TargetDataLayout::parse_from_llvm_datalayout_string`
(`compiler/rustc_abi/src/lib.rs:376-563`) yields the following parameter
distributions:

| Parameter | Distribution Across Built-In Targets (`307` inline `data_layout`, `322` total) | Notable Target Examples & Architectural Consequences |
| :--- | :--- | :--- |
| **`endian`** | Little (`e`): `292`; Big (`E`): `15` | Big-endian targets include `m68k-unknown-linux-gnu`, `s390x-unknown-linux-gnu`, `powerpc-*`, `powerpc64-ibm-aix`, `mips-*`, `sparc64-*`, and `ebpf` variant. |
| **`pointer_size` & `pointer_align.abi`** | `(64b, 64b)`: `212`<br>`(32b, 32b)`: `92`<br>`(32b, 16b)`: `1`<br>`(16b, 16b)`: `1`<br>`(16b, 8b)`: `1` | • **16-bit pointers (`2` bytes)**: `msp430-none-elf` (`p:16:16`, `align = 2B`), `avr-none` (`p:16:8`, `align = 1B`!).<br>• **32-bit pointer with 2-byte ABI alignment**: `m68k-unknown-linux-gnu` (`p:32:16:32`, `size = 4B, align = 2B`!). |
| **`instruction_address_space`** | `AddressSpace(0)`: `306`<br>`AddressSpace(1)`: `1` (`avr-none`) | `avr-none` sets `-P1` in `data_layout`, placing function pointers `fn()` in Harvard program-flash address space `1`. |
| **`i64_align.abi` (`u64`/`i64`)** | `64b` (`8B`): `229`<br>`32b` (`4B`): `75`<br>`16b` (`2B`): `2`<br>`8b` (`1B`): `1` | • **`4B` (`32b`)**: 32-bit x86 SysV targets (`i686-unknown-linux-gnu`, `i64:32:64`), `xtensa`, `csky`, `wasm32`/`riscv32`/`mips` targets omitting `i64:` (since `TargetDataLayout::default()` sets `i64_align = 32b`), and `m68k-unknown-linux-gnu` (`i64:32:32`).<br>• **`8B` (`64b`) on 32-bit targets**: `i686-pc-windows-msvc`, `arm-unknown-linux-gnueabi`, `armv7-*`.<br>• **`2B` (`16b`)**: `msp430-none-elf`, `m68k-none-elf`.<br>• **`1B` (`8b`)**: `avr-none`. |
| **`i128_align.abi` (`u128`/`i128`)** | `128b` (`16B`): `168`<br>`64b` (`8B`): `122`<br>`32b` (`4B`): `13`<br>`16b` (`2B`): `2`<br>`8b` (`1B`): `1` | Takes **every power of two in $\{1, 2, 4, 8, 16\}$ bytes**:<br>• **`16B`**: `x86_64-*`, `aarch64-unknown-linux-gnu`, `riscv64*`.<br>• **`8B`**: `aarch64-pc-windows-msvc` (Windows ARM64 caps `i128` at 8B!), `s390x-unknown-linux-gnu`, `powerpc64-*`, `wasm32-*`, `riscv32*`.<br>• **`4B`**: `i686-unknown-linux-gnu`, `i686-pc-windows-msvc`, `m68k-unknown-linux-gnu`, `sparc-unknown-linux-gnu` (`i128:` omitted -> defaults to `32b`).<br>• **`2B`**: `msp430-none-elf`, `m68k-none-elf`.<br>• **`1B`**: `avr-none`. |
| **`f64_align.abi` (`f64`) vs. `i64_align.abi` (`u64`)** | `64b` (`8B`): `240`<br>`32b` (`4B`): `64`<br>`16b` (`2B`): `2`<br>`8b` (`1B`): `1` | Because `TargetDataLayout::default()` (`compiler/rustc_abi/src/lib.rs:384-396`) sets `i64_align = 32b` (`4B`) and `f64_align = 64b` (`8B`), **`align_of::<u64>() != align_of::<f64>()`** on multiple built-in targets:<br>• On `m68k-unknown-linux-gnu`: `align_of::<u64>() == 4`, `align_of::<f64>() == 8`.<br>• On `powerpc64-ibm-aix` (`-f64:32:64`): `align_of::<u64>() == 8`, `align_of::<f64>() == 4`. |
| **`min_global_align`** | `None`: `297`<br>`Some(16b)` (`2B`): `10` | `m68k-unknown-linux-gnu` and `s390x-*` set `-Fi16` or `-n...` global minimum alignment of 2 bytes. |
| **`c_int_width` & `c_enum_min_bits`** | `c_int_width = 32`: `320`; `16`: `2` (`avr-none`, `msp430-none-elf`).<br>`c_enum_min_bits`: `None` (`c_int`): `320`; `Some(8)`: `2` (`hexagon-unknown-none-elf`, `s390x-unknown-none-softfloat`). | On `avr-none` and `msp430-none-elf`, `#[repr(C)] enum { A, B }` has `size = 2, align = 1` / `align = 2`; on `hexagon-unknown-none-elf` (`short_enums: true`), `#[repr(C)] enum { A, B }` has `size = 1, align = 1`! |
| **`max_atomic_width`** | `None` (ptr width): `182`; `64`: `95`; `128`: `25`; `32`: `10`; `0`: `7`; `16`: `2`; `8`: `1` | `avr-none`, `msp430-none-elf`, and `riscv32i-unknown-none-elf` have `max_atomic_width = Some(0)` (no hardware atomic CAS). |

#### 4.2 Resolution of `TargetDataLayout.aggregate_align`: Built-In `-a:0:32` vs. Custom `-a:32`

`Basis: normative + source + execution`

- **Why all 322 built-in targets currently have `dl.aggregate_align == 1` byte**:
  64 built-in targets (`arm-*`, `thumb-*`, `m68k-*`, `xtensa-*`, `csky-*`)
  include `-a:0:32` or `-a:0:16` in their LLVM `data_layout` string. In LLVM
  datalayout syntax (`a:<abi>:<pref>`), the first number (`0`) is the ABI
  minimum aggregate alignment in bits, and the second number (`32` or `16`) is
  the preferred alignment. In `TargetDataLayout::parse_from_llvm_datalayout_string`
  (`compiler/rustc_abi/src/lib.rs:429-434, 495-503`), `parse_align_seq` parses
  `abi` (`0` bits) and `pref` (`32` bits), line 502 discards `_pref`
  (`dl.aggregate_align = abi`), and `Align::from_bits(0)` calls
  `Align::from_bytes(0)` (`compiler/rustc_abi/src/lib.rs:1079-1083`), which maps
  `0 => Align::ONE` (`1` byte).
- **What happens when `dl.aggregate_align > 1` (e.g., custom target JSON with
  `-a:32` or `-a:16:32`)**:
  In `LayoutCalculator::univariant_biased`
  (`compiler/rustc_abi/src/layout.rs:1106-1114`), every non-packed struct—including
  `#[repr(C)]` and `#[repr(transparent)]`—executes:
  ```rust
  if repr.pack.is_none() {
      align = align.max(dl.aggregate_align);
  }
  ```
  before rounding `size = offset.align_to(align.abi)` (`layout.rs:1265`) and
  checking `size != field.size` in the single-field scalar ABI optimization
  (`layout.rs:1303`)!
- **Empirical Verification (`support/custom_a32_target.json`,
  `support/probe_aggregate_align_clean.rs`,
  `support/probe_aggregate_align_output.txt`)**:
  Compiling `#[repr(C)] pub struct ReprCU8(pub u8)` and
  `#[repr(transparent)] pub struct TransU8(pub u8)` with `--target
  support/custom_a32_target.json` (`-a:32`, i.e., `dl.aggregate_align = 4`
  bytes) produces:
  ```text
  print-type-size type: `ReprCU8`: 4 bytes, alignment: 4 bytes
  print-type-size     field `.0`: 1 bytes
  print-type-size     end padding: 3 bytes
  print-type-size type: `TransU8`: 4 bytes, alignment: 4 bytes
  print-type-size     field `.0`: 1 bytes
  print-type-size     end padding: 3 bytes
  ```
  Both `ReprCU8` and `TransU8` receive **`size = 4, align = 4` (with 3 bytes of
  trailing padding) and `BackendRepr::Memory`**, directly violating
  `r[layout.repr.c.struct.align]` (which requires `align == 1, size == 1`) and
  `r[layout.repr.transparent.layout-abi]` (which requires `TransU8` to have the
  exact size, alignment, and ABI of `u8`).

#### 4.3 Known Target-ABI Compliance Failures (`rust-lang/unsafe-code-guidelines#461` & `zerocopy/POLICIES.md`)

`Basis: documentation + source + execution`

- **`i686-pc-windows-msvc` Stack Misalignment of 8-Byte-Aligned Types**:
  On `i686-pc-windows-msvc`, `data_layout` omits `i64:32:64`, so `dl.i64_align =
  8` bytes and `dl.f64_align = 8` bytes (`align_of::<u64>() == 8`,
  `align_of::<f64>() == 8` in `support/probe2_results.json`). However, the
  32-bit Windows x86 cdecl ABI only maintains 4-byte stack pointer (`ESP`)
  alignment and does not dynamically realign every stack frame containing `u64`
  or `f64` locals. `rustc` explicitly acknowledges this hardware/ABI limitation
  in `Target::max_reliable_alignment`
  (`compiler/rustc_target/src/spec/mod.rs:3862-3871`):
  ```rust
  pub fn max_reliable_alignment(&self) -> Align {
      if self.arch == Arch::X86 && self.os == Os::Windows {
          Align::from_bytes(4).unwrap()
      } else {
          Align::MAX
      }
  }
  ```
  Consequently, taking a reference `&x` to a stack-allocated `u64` or `f64` on
  `i686-pc-windows-msvc` can produce a pointer whose runtime address is only
  4-byte aligned while `align_of::<u64>() == 8`, violating
  `r[type.pointer.validity.alignment]` (`rust-lang/rust#112480`,
  `rust-lang/unsafe-code-guidelines#461`). `zerocopy/POLICIES.md` (`lines
  58-92`) explicitly cites `unsafe-code-guidelines#461` to place such
  non-compliant targets under a "Reference-conformance assumption": proofs
  derive soundness from the Reference's normative guarantees without working
  around target backends where `rustc`/LLVM fails to uphold the Reference.

#### 4.4 Seven `#[repr(C)]` Cross-Language and Cross-Target Hazards

`Basis: normative + documentation + source + execution`

Empirical compilation of `support/probe_repr_c_divergences.rs` across 9 targets
(`support/probe2_results.json`) and `support/probe_call_abi.rs` across 6 targets
(`support/probe_call_abi_results.json`), together with inspection of
`compiler/rustc_lint/src/types/improper_ctypes.rs`, establishes seven distinct
ways `#[repr(C)]` diverges across targets or from C/C++:

1. **Empty structs (`#[repr(C)] struct Empty;`)**:
   In Rust, `Empty` has `size = 0, align = 1` on all targets
   (`r[layout.repr.c.struct.fieldless]`). In ISO C99/C11 (`6.7.2.1p8`), a struct
   with no named members is a syntax/constraint violation (undefined behavior);
   GCC's C extension gives `struct Empty {}` `size = 0`, whereas C++ gives every
   empty class `size = 1, align = 1`. Passing `Empty` across FFI therefore
   corrupts parameter/field offsets against C++ or non-GNU C compilers
   (flagged by `improper_ctypes_definitions`,
   `compiler/rustc_lint/src/types/improper_ctypes.rs:285-351`).
2. **Zero-sized fields (`[T; 0]`, `PhantomData<T>`, ZST structs) inside
   `#[repr(C)]` structs**:
   - In Rust, a zero-sized field `z: [u64; 0]` contributes `0` bytes of size
     but contributes its alignment $\text{align}(\text{u64})$ to both its own
     offset and the enclosing struct's alignment (`#[repr(C)] struct
     WithAlignedZst { a: u8, z: [u64; 0], b: u8 }` has `size = 16, align = 8,
     offset(b) = 8` on `x86_64`, `size = 8, align = 4, offset(b) = 4` on
     `i686-unknown-linux-gnu`, and `size = 2, align = 1, offset(b) = 1` on
     `avr-none` in `support/probe2_results.json`).
   - Furthermore, on `aarch64-unknown-linux-gnu`, `rustc`'s Homogeneous
     Floating-Point Aggregate (HFA) classifier ignores 1-ZST fields:
     `#[repr(C)] struct HfaWithZst { x: f32, z: [u8; 0], y: f32 }` is passed in
     two floating-point registers (`S0, S1`, `CastTarget` of two `f32`s),
     whereas a C++ struct replacing the ZST with a 1-byte member (`struct
     TwoF32WithByte { x: f32, pad: u8, y: f32 }`) is passed packed in integer
     registers (`Int(I64)` + `Int(I32)` in `support/probe_call_abi_results.json`).
3. **`u64` / `i64` / `f64` alignment inside `#[repr(C)]` structs**:
   In `support/probe2_results.json`, `#[repr(C)] struct WithU64 { a: u8, b: u64 }`
   has:
   - `size = 16, align = 8, offset(b) = 8` on `x86_64-unknown-linux-gnu`,
     `aarch64-unknown-linux-gnu`, `i686-pc-windows-msvc`, and
     `powerpc64-ibm-aix`;
   - `size = 12, align = 4, offset(b) = 4` on `i686-unknown-linux-gnu` and
     `m68k-unknown-linux-gnu`;
   - `size = 10, align = 2, offset(b) = 2` on `msp430-none-elf`;
   - `size = 9, align = 1, offset(b) = 1` on `avr-none`.
   Meanwhile, `#[repr(C)] struct WithF64 { a: u8, b: f64 }` has `size = 16,
   align = 8` on `m68k-unknown-linux-gnu` (where `WithU64` is `12` bytes) and
   `size = 12, align = 4` on `powerpc64-ibm-aix` (where `WithU64` is `16` bytes)!
4. **`u128` / `i128` alignment and register/vector ABI mismatches**:
   `#[repr(C)] struct WithU128 { a: u8, b: u128 }` has `(size, align, offset(b))`
   equal to `(32, 16, 16)` on `x86_64-unknown-linux-gnu` and
   `aarch64-unknown-linux-gnu`, `(24, 8, 8)` on `powerpc64-ibm-aix` and
   `aarch64-pc-windows-msvc`, `(20, 4, 4)` on `i686-unknown-linux-gnu`,
   `i686-pc-windows-msvc`, and `m68k-unknown-linux-gnu`, `(18, 2, 2)` on
   `msp430-none-elf`, and `(17, 1, 1)` on `avr-none`. On
   `x86_64-pc-windows-msvc` (which has no C `__int128` type),
   `extern "C" fn(u128) -> u128` passes the argument via
   `PassMode::Indirect { on_stack: false }` and returns `PassMode::Cast` in a
   16-byte `Vector` register (`xmm0`) (`support/probe_call_abi_results.json`).
5. **`bool` and `char` vs. C `_Bool` and `wchar_t` / `uint32_t`**:
   `bool` (`size = 1, align = 1`, bit patterns `0`/`1`) matches C99 `_Bool` on
   all built-in targets (`dl.i1_align == 8b`), whereas `char` (`size = 4, align
   = align_of::<u32>()`, valid range excluding `0xD800..=0xDFFF` and
   `> 0x10FFFF`) has no C equivalent (`wchar_t` is 16-bit on Windows and lacks
   Unicode scalar validity restrictions; flagged by `improper_ctypes_definitions`).
6. **`#[repr(C)]` enum discriminant width & 16-bit custom target ICE**:
   In `LayoutCalculator::c_enum` (`compiler/rustc_abi/src/layout.rs:823-885`),
   a fieldless `#[repr(C)]` enum's size is `max(min_repr, c_enum_min_size)`:
   - On standard 32/64-bit targets (`c_int_width = 32, short_enums = false`),
     `CEnumSmall { A = 0, B = 1 }` is `4` bytes (`I32`), expanding to `8` bytes
     (`I64`) for `CEnumLarge { A = 0, B = 0x1_0000_0000 }`.
   - On `avr-none` and `msp430-none-elf` (`c_int_width = 16`), `CEnumSmall` is
     `2` bytes (`I16`).
   - On `hexagon-unknown-none-elf` (`short_enums = true`), `CEnumSmall` is `1`
     byte (`I8`).
   - **Compiler ICE on custom 16-bit target JSONs (`support/custom_16bit_cint32.json`,
     `support/probe_16bit_c_enum_ice.rs`,
     `support/probe_16bit_c_enum_ice_output.txt`)**:
     In `rustc_ty_utils::layout::repr_options_of_def` (`layout.rs:845-875`),
     when an enum discriminant expression has no explicit type annotation,
     typeck falls back to `c_int`, **clamping it to `isize` (`I16`)** when
     `c_int_width (32) > pointer_size (16)`. However, `LayoutCalculator::c_enum`
     (`compiler/rustc_abi/src/layout.rs:832-885`) reads `dl.c_int_size` (`I32`)
     without clamping to `isize` and then panics at
     `compiler/rustc_abi/src/layout.rs:877:13`:
     ```text
     thread 'rustc' panicked at /rustc-dev/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/layout.rs:877:13:
     layout decided on a larger discriminant type (I32) than typeck (I16)
     ```
7. **Calling Convention (`PassMode`) Diverges from In-Memory Layout (`size`,
   `align`) Because `#[repr(C)]` Sets `ReprFlags::ABI_UNOPTIMIZABLE`**:
   In `LayoutCalculator::univariant_biased`
   (`compiler/rustc_abi/src/layout.rs:1165-1208, 1344`), a single-field
   `#[repr(transparent)]` or `#[repr(Rust)]` struct inherits its field's
   `BackendRepr::Scalar(...)`, whereas a `#[repr(C)]` struct sets
   `ReprFlags::ABI_UNOPTIMIZABLE`, forcing `BackendRepr::Memory { sized: true }`.
   Target ABI classifiers (`compiler/rustc_target/src/callconv/*.rs`) then
   assign different `PassMode`s to types with identical `(size, align)`
   (`support/probe_call_abi_results.json`):

| Target | Function Signature A (`PassMode`) | Function Signature B with Identical `(size, align)` (`PassMode`) | Why Calling Conventions Are Incompatible |
| :--- | :--- | :--- | :--- |
| **`x86_64-pc-windows-msvc`** | `extern "C" fn(f32) -> f32`<br>Arg & Ret: `Direct` (`Scalar(f32)` in `xmm0`) | `extern "C" fn(WrapF32) -> WrapF32` (`#[repr(C)] struct WrapF32(f32)`)<br>Arg & Ret: `Cast(Int(I32))` (in integer registers `rcx` / `rax`!) | Win64 ABI (`compiler/rustc_target/src/callconv/x86_64.rs:367-429`) passes 1/2/4/8-byte structs in **integer registers (`rcx`)**, whereas primitive `f32` passes in **SSE float register `xmm0`**. `#[repr(transparent)] struct TransF32(f32)` preserves `xmm0`. |
| **`i686-unknown-linux-gnu`** | `extern "C" fn(u64) -> u64`<br>Ret: `Direct` (`edx:eax`) | `extern "C" fn(WrapU64) -> WrapU64` (`#[repr(C)] struct WrapU64(u64)`)<br>Ret: **`Indirect { on_stack: true }` (hidden `sret` stack pointer!)** | 32-bit x86 SysV ABI (`compiler/rustc_target/src/callconv/x86.rs:124-156`) returns aggregate `Memory` types via a caller-allocated hidden stack pointer (`sret`), popping `4` bytes from the stack on `ret $4`, whereas scalar `u64` returns in `edx:eax`! |
| **`x86_64-unknown-linux-gnu` & `aarch64-unknown-linux-gnu`** | `extern "C" fn(u64) -> u64`<br>Arg & Ret: `Direct` (`Scalar(u64)` in integer reg `rdi`/`rax` or `X0`) | `extern "C" fn(AlignedTwoF32) -> AlignedTwoF32` (`#[repr(C, align(8))] struct AlignedTwoF32(f32, f32)`, `size = 8, align = 8`)<br>Arg & Ret: `Cast(Float(F32)x2)` (in float regs `xmm0` or `S0, S1`!) | Even though `u64` and `AlignedTwoF32` both have `size = 8, align = 8`, SysV AMD64 and AAPCS64 classify `AlignedTwoF32` as an SSE/HFA float aggregate (`xmm0` / `S0, S1`) and `u64` as an integer (`rdi` / `X0`). |

---

### 5. SemVer Snares, Pre-HIR `#[cfg]` / `build.rs`, and the Three-Axis Verification Architecture

`Basis: documentation + source + derived`

#### 5.1 Taxonomy of Layout and Semantic SemVer Snares

Synthesizing Jack Wrenn's *SemVer Snares* and `rustc` layout/resolution rules
identifies two families of upstream SemVer-minor changes that alter or break a
downstream crate without any change to the downstream crate's own source files:

1. **Layout & Representation SemVer Snares**:
   - **Size snare**: Adding or modifying private fields in a foreign type (even
     a `#[repr(C)]` struct with private fields or `#[non_exhaustive]`) changes
     `size_of::<Upstream>()`, breaking downstream compile-time size assertions
     or `transmute`s.
   - **Sizedness snare**: Changing a private marker field from
     `PhantomData<*const T>` (`T: ?Sized`) to `PhantomData<T>` (`T: Sized`)
     silently tightens the inferred `Sized` bound on `Upstream<T>`.
   - **Alignment snare**: Because Rust provides no syntax to cap the maximum
     alignment of a non-packed type (`#[repr(align(N))]` only establishes a
     lower bound) and no `MaxAlign<N>` auto trait, any SemVer-minor upstream
     change can raise `align_of::<Upstream>()`, increasing padding in enclosing
     downstream `#[repr(C)]` structs or invalidating pointer alignment proofs.
   - **`#[repr(transparent)]` 1-ZST snare (`E0690` / `E0691`)**: Because
     `#[repr(transparent)]` permits at most one non-1-ZST field, an upstream
     dependency that adds a private `u8` field or `#[repr(align(2))]` to a
     previously `size == 0, align == 1` unit struct breaks downstream
     `#[repr(transparent)] struct Wrapper(UpstreamUnit, NonZeroU64)` with
     `E0690` (multiple non-zero-sized fields) or `E0691` (ZST field with
     alignment `> 1`).
2. **Semantic SemVer Snares (Silent Downstream MIR Changes Without Source Edits)**:
   - Adding a trait implementation (`impl Trait for UpstreamType`), adding an
     inherent method (`impl UpstreamType { pub fn f(&self) }`), or adding a new
     public item to a glob-imported upstream module can silently change method
     dot-call autoref resolution (`(&x).f()` vs. `x.f()`), shadow an extension
     trait method, or alter macro expansion—producing a **different THIR/MIR
     body** for a downstream function whose `.rs` source is unchanged.
   - **Additive Cargo feature unification in diamond dependencies**: When
     another crate in the build graph enables `dep/extra-feature`, Cargo unifies
     features across the dependency graph, activating `#[cfg(feature =
     "extra-feature")]` fields, enum variants, or trait implementations inside
     `dep` and altering layouts and trait selections observed by the verified
     crate.

#### 5.2 Pre-HIR `#[cfg(...)]` Stripping and Turing-Complete `build.rs`

In `rustc`'s compilation pipeline (`compiler/rustc_expand`), inactive
`#[cfg(...)]` attributes are stripped at the token/AST level **before** name
resolution (`rustc_resolve`), HIR lowering (`rustc_ast_lowering`), type checking
(`rustc_hir_typeck`), or MIR construction (`rustc_mir_build`). Unconfigured
`#[cfg]` branches routinely reference target-specific intrinsics
(`core::arch::x86_64::*`), OS-specific modules (`std::os::windows::*`),
optional dependency crates, or `build.rs`-generated bindings
(`include!(concat!(env!("OUT_DIR"), "/bindings.rs"))`) that do not exist and
cannot typecheck outside their active target/feature configuration. Consequently,
"verifying a Rust crate once over the open-world universe of all possible future
`#[cfg]` assignments, `build.rs` outputs, custom `--target foo.json` files, and
Cargo dependency resolutions" is both **ill-defined** (no HIR or MIR exists for
unconfigured branches) and **undecidable** (`build.rs` executes arbitrary Rust
code on the host).

#### 5.3 The Three-Axis Verification Partition for Forward-Compatible Rust Verification

A sound and tractable verification architecture partitions compilation variation
into three orthogonal axes:

| Axis | Sources of Variation | Stage Where Variation Arises | Verification Discipline (`Anneal` / `zerocopy`) |
| :--- | :--- | :--- | :--- |
| **(Axis A) Compiler-Internal Nondeterminism** | `repr(Rust)` field order, inter-field and trailing padding, `enum` tag placement and opportunistic niches, wide-pointer `(data_ptr, metadata)` word order, `#[repr(transparent)]` 1-ZST offsets, unspecified evaluation order | Within a fixed resolved crate graph and fixed target $\tau$, across `rustc` releases or flags (`-Z randomize-layout`) | **Always demonically quantified ($\forall \ell \in \text{ReferenceAdmissible}(\tau)$)**: Verification semantics must never rely on `rustc`'s observed `layout_of` choice where the Reference leaves layout unspecified (e.g., `tySizeStep` and `evalTransmuteCopy` must require `#[repr(transparent)]` or `#[repr(C)]` on non-ZST single-field structs rather than accepting default `#[repr(Rust)]`). |
| **(Axis B) Target Parameters ($\tau \in \text{ValidTargetSpec}$)** | `pointer_size`, `pointer_align`, `endian`, `i16`/`i32`/`i64`/`i128`/`f32`/`f64` ABI alignments, `c_char_signed`, `c_int_width`, `short_enums`, `max_atomic_width` | Across compilation targets (`--target <triple>`) for a fixed crate graph and `#[cfg]` slice | **Dual-mode (`Target-Portable` vs. `Target-Specialized`) gated by `ValidTargetSpec(\tau)`**:<br>• *Target-portable proofs* (e.g., `zerocopy` library code) quantify $\forall \tau \in \text{ValidTargetSpec}$.<br>• *Target-specialized proofs* (e.g., 64-bit or x86_64-specific code) bind $\tau = \tau_0$.<br>In both modes, the capture tool checks `ValidTargetSpec(\tau)`: (1) `dl.aggregate_align.abi == 1`, (2) `dl.c_int_size <= dl.pointer_size`, (3) `dl.instruction_address_space == AddressSpace::ZERO` (unless Harvard code pointers are modeled), and (4) `target.max_reliable_alignment() >= max_primitive_align` (excluding unpatched `i686-pc-windows-msvc` 8-byte stack alignment). |
| **(Axis C) Pre-MIR Crate-Graph, `#[cfg]`, and Dependency Resolution** | `#[cfg(...)]` stripping, Cargo feature unification, `build.rs` codegen, upstream SemVer-minor changes | **Before HIR/THIR/MIR construction** | **Per-Compilation Configuration Certification**: Certifies the concrete resolved crate graph and active `#[cfg]` slice (or a finite CI matrix of target/feature points). Cross-crate proof certificates must either treat foreign non-`#[repr(C)]` types as abstract/opaque layouts or cryptographically bind the certificate to the exact `StableCrateId` / SVH / `DefPathHash` fingerprints of all resolved dependencies. |

#### 5.4 Multi-Field `#[repr(Rust)]` Sub-Alignment Packing, Over-Alignment Freedom, and `TransmutePayload` (`exactBits` vs. `initBytes`)

When formalizing `#[repr(Rust)]` struct layouts and transmutation in a verification tool (`support/ReprRustPackingAndTransmutePayload.lean`, 30 kernel-checked Lean 4 theorems), five mathematical and semantic invariants govern field packing, alignment freedom, and byte-level initialization:

1. **Why Declaration-Order `#[repr(C)]` Size Cannot Serve as a `#[repr(Rust)]` Lower Bound (`reprC_base_size_excludes_rustc_sandwich_size`)**:
   If a semantic model computes the base size of a `#[repr(Rust)]` struct using declaration-order sequential aligned placement (`foldReprCLayout`) and adds a non-negative padding parameter `adtPad : Nat`, then for `#[repr(Rust)] struct Sandwich { a: u8, b: u16, c: u8 }`, declaration-order placement yields `foldReprCLayout [(1, 1), (2, 2), (1, 1)] 0 1 = (6, 2)` (with 1 byte of inter-field padding at offset `1` and 1 byte of trailing padding at offset `5`). Because `adtPad + 6 >= 6`, no choice of `adtPad : Nat` can equal `4`—excluding `rustc`'s actual compiled layout (`size = 4, align = 2`, offsets `b: 0, a: 2, c: 3`) from the model's state space and falsifying `const { assert!(size_of::<Sandwich>() == 4) }` at `adtPad = 0`.

2. **Power-of-2 Descending-Alignment Zero-Inter-Field-Padding Theorem (`foldReprCFields_sorted_eq_alignUp_sum`)**:
   Because every Rust type has a power-of-2 alignment $a_i = 2^{k_i} \ge 1$ (`r[layout.properties.align]`) and a size that is a multiple of its alignment $a_i \mid s_i$ (`r[layout.properties.size]`), sorting a struct's fields in non-increasing alignment order $a_1 \ge a_2 \ge \dots \ge a_n$ (`DescendingAlignedChain`) guarantees $a_{i+1} \mid a_i \mid \sum_{j \le i} s_j$ at every step (`foldReprCLayout_chain_exact_sum`). Consequently:
   - Sequential placement in descending alignment order inserts **zero inter-field padding** (`alignUp offset a_i = offset` for every field $i$).
   - Every non-ZST field occupies a contiguous region inside $[0, \sum_{i=1}^n s_i)$, and the only padding in the sorted layout is the trailing alignment rounding at the end of the struct:
     $$\text{size}_{\text{sorted}} = \text{alignUp}\!\left(\sum_{i=1}^n s_i,\, \max_i a_i\right)$$
   - When `repr.align` and `repr.pack` are absent and `-Z randomize-layout` is disabled, `rustc_abi::layout::univariant_biased` (`compiler/rustc_abi/src/layout.rs:1087–1255`) achieves this exact minimum size `alignUp (sumFieldSizes fields) (maxFieldAlign fields)` across **every** `#[repr(Rust)]` struct and tuple (`support/univariant_packing_probe.rs` and `support/univariant_packing_probe_output.txt`), including:
     - `StructKind::AlwaysSized` with niche-Placement bias (`optimizing.sort_by_key(|&x| (!niche_at_start, cmp::Reverse(f.align.abi), f.size))`): Because every 1-byte-aligned field has $1 \mid s$, any field with a start-of-field niche (such as `(bool, u8)` in `NicheBiasStruct { a: u32, b: (bool, u8), c: u16 }`) placed after higher-aligned fields still preserves zero inter-field padding (`size = 8 = alignUp 8 4`, offsets `(0, 6, 4)`).
     - `StructKind::MaybeUnsized` (all non-empty tuples and `T: ?Sized` tail structs, where `univariant_biased` excludes the last field $f_{n-1}$ from sorting and places it at the end): Even when placing $f_{n-1}$ last introduces inter-field padding between the sorted prefix of size $P$ and $f_{n-1}$ (for example, `([u8; 3], u16, u16)` has prefix `[u16, [u8; 3]]` of size $P = 5$, 1 byte of inter-field padding at byte `5`, and tail `u16` at bytes `6..8`), because $a_{n-1} \mid s_{n-1}$ and $a_{n-1} \mid \text{maxAlign}$, any inter-field gap before the tail trades off 1-for-1 against trailing padding (`alignUp_tail_invariance`):
       $$\text{alignUp}(\text{alignUp}(P, a_{n-1}) + s_{n-1}, \text{maxAlign}) = \text{alignUp}(P + s_{n-1}, \text{maxAlign})$$

3. **Bijection Over Reference-Admissible `#[repr(Rust)]` Layouts (`reprRustLayout_sound`, `reprRustLayout_complete`, `reprRustLayout_injective`)**:
   Under `r[layout.properties.align]`, `r[layout.properties.size]`, `r[layout.repr.rust.alignment]`, `r[layout.repr.rust.layout.struct]`, and `r[layout.repr.rust.struct-zst]`, a pair `(sz, al)` is a Reference-admissible layout for a `#[repr(Rust)]` struct with field sum `sum`, maximum field alignment `maxFieldAlign`, and optional `#[repr(align(N))]` / `#[repr(packed(P))]` (`ReferenceAdmissibleStructLayout`) if and only if it is in the image of the two-parameter family `(pad, alignShift) : Nat × Nat` (`reprRustLayout`):
   - For `#[repr(Rust, packed(P))]`: `al = max 1 (min maxFieldAlign P)` and `sz = if sum == 0 then 0 else alignUp sum al + pad * al`.
   - For unpacked `#[repr(Rust)]`: `minAlign = max maxFieldAlign (reprAlign.getD 1)`, `al = minAlign * 2^alignShift`, and `sz = if sum == 0 then 0 else alignUp sum al + pad * al`.
   Furthermore, `(0, 0)` recovers `rustc`'s default `univariant` layout (`reprRustLayout_zero_zero`), all-ZST `#[repr(Rust)]` structs (`sum = 0`, such as `struct RustZst((), ())`) have guaranteed size `0` regardless of `pad` or `alignShift` (`rust_zst_and_trans_with_zst_verified`), and `alignShift > 0` propagates into outer `#[repr(C)]` structs containing nested `#[repr(Rust)]` fields (`sandwich_and_outer_c_under_overalignment`).

4. **Inevitable Padding vs. Field-Order-Invariant `TransmutePayload` (`exactBits` vs. `initBytes`)**:
   - **Inevitable Padding (`sumFieldSizes < alignUp sumFieldSizes al`)**: Whenever `sumFieldSizes fields < structSz`—even at `(pad = 0, alignShift = 0)`, as in `InevitablePad { a: [u8; 3], b: u32 }` (`sum = 7 < 8`), `TwoU24 { a: [u8; 3], b: [u8; 3], c: u32 }` (`sum = 10 < 12`), and `Mixed { a: u8, b: u64 }` (`sum = 9 < 16`)—the struct contains `structSz - sumFieldSizes > 0` bytes of uninitialized padding under *every* field permutation and is rejected as a transmutation source to byte/integer types (`inevitable_padding_sizes_and_transmute_rejection`).
   - **2-Constructor `TransmutePayload` (`exactBits` vs. `initBytes`)**: Modeling transmutation payloads with two constructors—`TransmutePayload.exactBits sizeBytes bits` (deterministic byte sequence) and `TransmutePayload.initBytes sizeBytes` (all `sizeBytes` bytes are initialized, but their relative order is compiler-dependent)—cleanly separates:
     1. `#[repr(C)]`, `#[repr(C, packed)]`, `#[repr(transparent)]` (peeling arbitrary 1-ZST siblings via `findTransparentPayloadField`), primitives, arrays, and 1-non-ZST-field `#[repr(Rust)]` structs with `structSz = fieldSz` (`single_field_rust_exact_bits_when_unpadded`), which yield `.exactBits sz bits` and support value-preserving transmutation to both `[u8; sz]` and scalars/composites; and
     2. Multi-field `#[repr(Rust)]` and `#[repr(Rust, packed)]` structs whose runtime world satisfies `sumFieldSizes = structSz` (such as `Sandwich(u8, u16, u8)` or `Pair(u32, u32)` when guarded by `const { assert!(size_of::<T>() == sumFieldSizes) }`), which yield `.initBytes sz`. `reconstructFromPayload (.initBytes sz)` succeeds when the destination is `[u8; sz]` or a nested array of `u8`/`i8` (`IntoBytes` soundness, `sandwich_transmute_to_bytes_after_size_guard`), but returns `none` when the destination is `u32`/`u64` or `#[repr(C)] struct CPair(u32, u32)` (`pair_repr_rust_transmute_discrimination` and `c_packed_exact_bits_vs_rust_packed_init_bytes`).

## Boundaries

- **Known not to apply — `-Z randomize-layout` as a completeness test for
  `r[layout.repr.rust.*]` compliance**: Passing tests under `rustc -Z
  randomize-layout` does **not** establish that code is free of reliance on
  unspecified `#[repr(Rust)]` layouts, because `rustc`'s `-Z randomize-layout`
  never perturbs single-field `#[repr(Rust)]` structs, tuples, `#[repr(Rust)]`
  unions, or wide-pointer word order, and never injects synthetic padding into
  already-aligned structs.
- **Known not to apply — `#[repr(C)]` size/alignment equivalence as `extern "C"`
  function-signature equivalence**: Two `#[repr(C)]` types (or a `#[repr(C)]`
  wrapper and its inner primitive) having identical `size_of` and `align_of` is
  **known not to imply** compatible `extern "C"` calling conventions (`PassMode`),
  because `#[repr(C)]` sets `ReprFlags::ABI_UNOPTIMIZABLE` (`BackendRepr::Memory`),
  altering register vs. stack/integer passing on `x86_64-pc-windows-msvc`,
  `i686-unknown-linux-gnu`, `x86_64-unknown-linux-gnu`, and
  `aarch64-unknown-linux-gnu`. Only `#[repr(transparent)]` guarantees `FnAbi`
  equivalence.
- **Known not to apply — `#[repr(transparent)]` niche transitivity on
  `UnsafeCell<T>` and `Cell<T>`**: Although `UnsafeCell<T>` and `Cell<T>` carry
  `#[repr(transparent)]`, `rustc` strips their niches via `is_special_no_niche`
  (`compiler/rustc_ty_utils/src/layout.rs:717`), so `Option<UnsafeCell<&T>>` and
  `Option<Cell<&T>>` do not undergo null-pointer optimization.
- **Known not to apply — Standard Reference layout guarantees on custom target
  JSONs with `a:16`/`a:32` or `c_int_width > target_pointer_width`**:
  `r[layout.repr.c.struct.align]` and `r[layout.repr.transparent.layout-abi]`
  fail to hold when a custom target JSON sets `dl.aggregate_align > 1` (`-a:32`),
  and `LayoutCalculator::c_enum` panics (`ICE`) when `c_int_width >
  target_pointer_width`.
- **Not examined — SIMD vector (`#[repr(simd)]`) and scalable vector
  (`#[repr(scalable)]`) target ABIs**: Target-specific vector register widths
  (`dl.vector_align`) and `#[repr(simd)]` calling conventions across AVX-512,
  NEON, and SVE targets were not examined in this investigation.

## Evidence

### Normative Specifications and Upstream Documentation

- **The Rust Reference (`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`
  and `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`)**:
  - `type-layout.html`: `r[layout.properties.*]` (`lines 184-213`),
    `r[layout.primitive.*]` (`lines 218-255`), `r[layout.pointer.*]` (`lines
    256-279`), `r[layout.array]` (`lines 281-285`), `r[layout.slice]` (`lines
    286-297`), `r[layout.str]` (`lines 299-303`), `r[layout.tuple.*]` (`lines
    308-315`), `r[layout.struct.def]` (`lines 316-320`), `r[layout.enum.empty]`
    (`lines 321-327`), `r[layout.union]` (`lines 328-334`),
    `r[layout.repr.rust.*]` (`lines 400-432`, including `r[layout.repr.rust.struct-zst]`
    and `r[layout.repr.rust.enum-struct-like-zst]` added in `82da570b`),
    `r[layout.repr.c.struct.*]` (`lines 449-574`), `r[layout.repr.c.union.*]`
    (`lines 584-592`), `r[layout.repr.c.enum.*]` (`lines 596-660`),
    `r[layout.repr.primitive.*]` (`lines 667-745`),
    `r[layout.repr.c-primitive.*]` (`lines 746-853`),
    `r[layout.repr.alignment.*]` (`lines 855-916`), and
    `r[layout.repr.transparent.*]` (`lines 917-958`).
  - `dynamically-sized-types.html`: `r[dynamic-sized.kind.struct]` (`lines
    54-60`), `r[dynamic-sized.pointer-types]` (`lines 196-207`).
  - `types/{boolean,numeric,char,str,never,union,function-pointer}.html` and
    `items/unions.html:5050-5053` (`r[items.union.fields.offset]`).
- **Rust Standard Library (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`)**:
  - `library/core/src/option.rs:116-159` (`# Representation` — closed set
    $\mathcal{N}_{\text{Option}}$ and all-zeros `None` transmute guarantee).
  - `library/core/src/result.rs:232-259` (`# Representation` — `Result<T, ZST>`
    and `Result<ZST, T>` guarantee for 1-ZSTs).
  - `library/core/src/cell.rs:308, 2223-2230, 2309` (`Cell` and `UnsafeCell`
    `#[repr(transparent)]` declarations and niche-suppression rationale).
  - `library/core/src/mem/{manually_drop.rs:81, maybe_uninit.rs:125-129}`.
- **`zerocopy` (`google/zerocopy@8fb35253fbc703cb2cd0997f4efcda76cf9062b6`)**:
  - `POLICIES.md:1-119` (forwards-compatible soundness policy, Reference
    authority, `rust-lang/unsafe-code-guidelines#461` Reference-conformance
    assumption, and safety-comment exceptions).
  - `src/layout.rs:1068-1440` (`DstLayout`, `TrailingSliceLayout`,
    `size_rounding_align_and_phase`, and generic `packed` over `align`
    assumption at `lines 1080-1088`).
  - `zerocopy-derive/src/derive/{into_bytes.rs:124-145, unaligned.rs:19-40,
    known_layout.rs:31-75}` and `src/util/macro_util.rs:297-315`.

### Compiler Implementation Source (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`)

- `compiler/rustc_abi/src/lib.rs`:
  - `L96-L101, L212-L247`: `ReprFlags::RANDOMIZE_LAYOUT` (citing Reference PRs
    #2262 and #2293), `FIELD_ORDER_UNOPTIMIZABLE` (omitting `IS_TRANSPARENT`),
    `ReprOptions::inhibit_struct_field_reordering`, and
    `ReprOptions::inhibits_union_abi_opt`.
  - `L376-L563`: `TargetDataLayout::default` (`i64_align = 32b`,
    `i128_align = 32b`, `f64_align = 64b`, `aggregate_align = 1B`) and
    `TargetDataLayout::parse_from_llvm_datalayout_string` (`parse_align_seq`
    ignoring `pref` on `a:0:32`).
  - `L724-L740`: `TargetDataLayout::obj_size_bound` and `ptr_sized_integer`.
  - `L948-L950`: `FieldsShape::Union(_) => Size::ZERO`.
  - `L1013-L1028, L1079-L1083`: `Align::max_for_target` and `Align::from_bytes(0) => Align::ONE`.
- `compiler/rustc_abi/src/layout.rs`:
  - `L285-L362`: `LayoutData::scalar_pair`, `LayoutData::array` (`largest_niche`
    propagation when `count != 0`), and `LayoutData::slice`.
  - `L395-L520`: `LayoutCalculator::layout_of_union`.
  - `L640-L940`: `layout_of_niche_filling_enum`, `layout_of_tagged_enum`, and
    `LayoutCalculator::c_enum` (`L823-L885`, including the assertion at `L877`
    that panics when `dl.c_int_size > typeck_discr_size`).
  - `L943-L1380`: `LayoutCalculator::layout_of_struct_or_tuple` and
    `univariant_biased` (`L1108` `align = align.max(dl.aggregate_align)`,
    `L1110` `fields.len() > 1` shuffle guard, `L1165-L1208` single-field scalar
    ABI optimization suppressed by `ABI_UNOPTIMIZABLE` at `L1344`, and `L1357-L1369`
    `without_niche`).
- `compiler/rustc_ty_utils/src/layout.rs`:
  - `L344-L520`: Primitive, pointer, array, slice, `str`, `dyn Trait`, and
    wide-pointer `layout_of_uncached` rules.
  - `L571-L576`: `ty::Tuple` passing `ReprOptions::default()`.
  - `L717`: `is_special_no_niche = def.is_unsafe_cell() || def.is_unsafe_pinned()`.
  - `L845-L875`: `repr_options_of_def` clamping unannotated `c_int` enum
    discriminants to `isize`.
- `compiler/rustc_target/src/spec/mod.rs:3862-3871`
  (`Target::max_reliable_alignment` capping 32-bit Windows x86 at 4 bytes) and
  `compiler/rustc_target/src/callconv/{x86_64,x86,aarch64,riscv}.rs`.
- `compiler/rustc_codegen_ssa/src/size_of_val.rs:92-183` and
  `compiler/rustc_const_eval/src/interpret/eval_context.rs:436-489`
  (`size_and_align_of_dst`).
- `compiler/rustc_lint/src/types/improper_ctypes.rs:285-351`.

### Preserved Reproducible Artifacts (`support/`)

All execution probes and generated datasets are preserved in `support/`:

- [`support/layout_probes.rs`](support/layout_probes.rs) and
  [`support/layout_probes_output.json`](support/layout_probes_output.json):
  Comprehensive probe program and JSON output comparing sizes, alignments,
  field offsets, wide-pointer word layouts, niche sizes/tags, and DST
  `size_of_val`/`align_of_val`/tail offsets across `rustc 1.99.1`, `rustc
  1.98.0-nightly` (default), and `rustc 1.98.0-nightly -Z randomize-layout` with
  `layout-seed=42` and `layout-seed=7`.
- [`support/randomize_layout_probe.rs`](support/randomize_layout_probe.rs) and
  [`support/randomize_layout_probe.jsonl`](support/randomize_layout_probe.jsonl):
  17-run sweep (`default_no_randomize` plus `-Z randomize-layout -Z
  layout-seed=0..15`) on `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`.
- [`support/target_matrix.json`](support/target_matrix.json): Extracted
  `TargetDataLayout` and `TargetOptions` parameters for all 322 built-in target
  specifications in `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`.
- [`support/probe_repr_c_divergences.rs`](support/probe_repr_c_divergences.rs)
  and [`support/probe2_results.json`](support/probe2_results.json):
  `-Z print-type-sizes` output across 9 built-in targets (`x86_64-unknown-linux-gnu`,
  `i686-unknown-linux-gnu`, `i686-pc-windows-msvc`, `aarch64-unknown-linux-gnu`,
  `m68k-unknown-linux-gnu`, `avr-none`, `msp430-none-elf`,
  `hexagon-unknown-none-elf`, `powerpc64-ibm-aix`).
- [`support/probe_call_abi.rs`](support/probe_call_abi.rs) and
  [`support/probe_call_abi_results.json`](support/probe_call_abi_results.json):
  `#[rustc_abi(debug)]` `FnAbi` (`PassMode`) dumps across 6 built-in targets
  (`x86_64-unknown-linux-gnu`, `x86_64-pc-windows-msvc`,
  `i686-unknown-linux-gnu`, `i686-pc-windows-msvc`,
  `aarch64-unknown-linux-gnu`, `riscv64gc-unknown-none-elf`).
- [`support/custom_a32_target.json`](support/custom_a32_target.json),
  [`support/probe_aggregate_align_clean.rs`](support/probe_aggregate_align_clean.rs),
  and
  [`support/probe_aggregate_align_output.txt`](support/probe_aggregate_align_output.txt):
  Minimal reproducer demonstrating that `-a:32` (`dl.aggregate_align = 4`)
  forces `#[repr(C)] struct ReprCU8(u8)` and `#[repr(transparent)] struct
  TransU8(u8)` to `size = 4, align = 4` (`BackendRepr::Memory`).
- [`support/custom_16bit_cint32.json`](support/custom_16bit_cint32.json),
  [`support/probe_16bit_c_enum_ice.rs`](support/probe_16bit_c_enum_ice.rs), and
  [`support/probe_16bit_c_enum_ice_output.txt`](support/probe_16bit_c_enum_ice_output.txt):
  Minimal reproducer triggering the `LayoutCalculator::c_enum` ICE at
  `compiler/rustc_abi/src/layout.rs:877:13` when `target-pointer-width` is `16`
  and `target-c-int-width` defaults to `32`.
- [`support/ReprRustPackingAndTransmutePayload.lean`](support/ReprRustPackingAndTransmutePayload.lean):
  Standalone, zero-`sorry`, zero-axiom Lean 4 mechanization (`v4.34.1`, 30
  kernel-checked theorems) proving the Power-of-2 Descending-Alignment
  Zero-Inter-Field-Padding Theorem (`foldReprCFields_sorted_eq_alignUp_sum`),
  the `StructKind::MaybeUnsized` Tail-Invariance Theorem
  (`alignUp_tail_invariance`), the `(adtPad, adtAlignShift)` soundness,
  completeness, and bijection theorems over `ReferenceAdmissibleStructLayout`
  (`reprRustLayout_sound`, `reprRustLayout_complete`,
  `reprRustLayout_injective`, `reprRustLayout_zero_zero`), and the 2-constructor
  `TransmutePayload` (`exactBits` vs. `initBytes`) holdout theorems.
- [`support/univariant_packing_probe.rs`](support/univariant_packing_probe.rs)
  and
  [`support/univariant_packing_probe_output.txt`](support/univariant_packing_probe_output.txt):
  Empirical probe verifying `size_of`, `align_of`, and `offset_of!` across
  `Sandwich`, `CSandwich`, `OuterCWithSandwich`, `InevitablePad`, `TwoU24`,
  `Mixed`, `NicheBiasStruct`, `TupleTailInvariance`, `Pair`, `CPair`,
  `SingleFieldRust`, `TransWithZst`, `RustZst`, `CPackedSandwich`, and
  `RustPackedSandwich`.

## Revalidation

To revalidate the findings in this package against a newer `rustc` toolchain or
Reference revision without repeating the full source crawl:

1. **Rerun the host layout and `-Z randomize-layout` probes**:
   ```console
   rustc support/layout_probes.rs -o ./layout_probes && ./layout_probes
   rustc -Z randomize-layout -Z layout-seed=42 support/layout_probes.rs -o ./layout_probes_s42 && ./layout_probes_s42
   rustc -Z randomize-layout -Z layout-seed=7 support/layout_probes.rs -o ./layout_probes_s7 && ./layout_probes_s7
   ```
   Compare the emitted JSON against `support/layout_probes_output.json`. Check
   whether `SingleU64`, `TupleHet`, or `RustUnion` begin randomizing under
   `-Z randomize-layout`, and whether `Option<UnsafeCell<&u8>>` and
   `Option<Cell<&u8>>` remain `16` bytes.
2. **Rerun the cross-target `#[repr(C)]` layout and `FnAbi` probes**:
   ```console
   rustc --crate-type=lib -Z unstable-options -Z print-type-sizes --target i686-unknown-linux-gnu support/probe_repr_c_divergences.rs --emit=metadata --out-dir /tmp
   rustc --crate-type=lib -Z unstable-options --target x86_64-pc-windows-msvc support/probe_call_abi.rs --emit=metadata --out-dir /tmp
   ```
   Compare the output against `support/probe2_results.json` and
   `support/probe_call_abi_results.json`.
3. **Rerun the custom target `aggregate_align` and 16-bit `c_enum` probes**:
   ```console
   rustc --crate-type=lib -Z unstable-options -Z print-type-sizes --target support/custom_a32_target.json support/probe_aggregate_align_clean.rs --emit=metadata --out-dir /tmp
   RUSTC_ICE=0 rustc --crate-type=lib -Z unstable-options --target support/custom_16bit_cint32.json support/probe_16bit_c_enum_ice.rs --out-dir /tmp
   ```
   Check whether `LayoutCalculator::univariant_biased` still applies
   `dl.aggregate_align` to `#[repr(C)]` and `#[repr(transparent)]` structs and
   whether `LayoutCalculator::c_enum` still panics when `c_int_width >
   target_pointer_width`.
4. **Diff upstream normative and implementation anchors**:
   - In `rust-lang/reference`: diff `src/type-layout.md` and
     `src/dynamically-sized-types.md`.
   - In `rust-lang/rust`: diff `compiler/rustc_abi/src/{lib.rs,layout.rs}`,
     `compiler/rustc_ty_utils/src/layout.rs`, and
     `library/core/src/{option.rs,result.rs,cell.rs}`.
