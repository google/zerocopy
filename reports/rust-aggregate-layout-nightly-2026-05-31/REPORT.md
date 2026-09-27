# Rust struct, enum, and union layout rules relevant to unsafe code at nightly-2026-05-31

## Summary

Rust's aggregate layout contract at the Anneal-era toolchain has one central dividing line: **the default `Rust` representation deliberately promises very little, while `repr(C)`, primitive enum representations, `repr(transparent)`, and alignment modifiers add specific guarantees without erasing Rust validity rules.** Unsafe code must reason from the representation actually attached to the nominal type rather than from source declaration order or from a compiler layout observed once.

For a default-representation struct, Rust guarantees that every field offset satisfies that field's alignment, that the containing type is aligned at least as strongly as its fields, and that non-zero-sized fields do not overlap. It does **not** guarantee declaration-order layout. Zero-sized fields may share an address with other fields. No other default-representation data-layout guarantee is given.

`#[repr(C)]` fixes substantially more structure. Struct fields occur in declaration order with the usual alignment padding, and the final size is rounded to the struct alignment. `repr(C)` union fields all begin at offset zero; the union alignment is the maximum field alignment and its size is the maximum field size rounded up to that alignment. A `repr(C)` enum with fields is represented as a C-layout struct containing a tag and a C-layout union of C-layout variant payload structs. A primitive enum representation such as `repr(u8)` instead uses a C-layout union whose variant structs begin with that fixed-width tag. Combining `repr(C, u8)` keeps the C tagged-union shape but fixes the tag representation to `u8`.

Those layout guarantees do not imply broader validity guarantees. A Rust fieldless `repr(C)` enum still permits only its Rust discriminants even though a C enum object can generally contain other integer values. A union has no active-field tag: reading a field interprets the stored bits as that field's type and is undefined when those bits are invalid for the chosen type. The Reference also permits non-C union fields to have nonzero offsets, so code that requires every union field at byte zero needs `repr(C)` rather than merely the `union` keyword.

`repr(packed(N))` lowers field-positioning alignment without changing a field type's own layout. It can therefore place a field at an address that is invalid for an ordinary reference to that field type. Rust explicitly forbids creating references to such unaligned fields; raw pointers plus unaligned read/write operations are the relevant primitive. `repr(align(N))` raises aggregate alignment but, by itself, does not establish field order. At this Reference revision, `align` and `packed` cannot appear on the same type, and a packed type cannot transitively contain an aligned type.

`repr(transparent)` delegates both layout and ABI to its sole field that is not simultaneously zero-sized and alignment-one, or to unit if there is no such field. This is stronger than merely matching size/alignment. By contrast, equal size and alignment between two arbitrary aggregate types do not imply equal layout, ABI, field offsets, validity, or safe transmutability.

No fresh compiler or target-layout execution was performed. This report records the exact normative layout contract and its direct unsafe-code consequences. It intentionally does not reverse-engineer the compiler's unspecified default-layout choices or niche optimization strategy.

## Applicability

The active Anneal/Charon toolchain pin selects `nightly-2026-05-31`; the corresponding Rust source revision used throughout the neighboring primitive-semantics corpus is `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. The normative aggregate-layout rules examined here come from `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

The report covers sized structs, unions, fieldless enums, fieldful enums, and the following representation forms documented at that Reference revision:

- default/explicit `repr(Rust)`;
- `repr(C)`;
- primitive enum representations such as `repr(u8)` and `repr(i32)`;
- combinations such as `repr(C, u8)` on fieldful enums;
- `repr(align(N))` and `repr(packed(N))`; and
- `repr(transparent)`.

It focuses on guarantees that unsafe code can soundly depend on. Where the Reference deliberately leaves layout unspecified, this report preserves that absence rather than substituting the current compiler's implementation choice.

The report does not own the complete semantics of padding initialization, niches, discriminant validity, transmute, raw-pointer access, DST tails, or FFI calling conventions. It states their interaction with aggregate layout only where that boundary changes what a layout guarantee means.

## Findings

### `repr(Rust)` gives only soundness-required layout guarantees

The Reference defines `Rust` as the default representation for nominal types without another representation attribute. Writing `repr(Rust)` explicitly is guaranteed to mean the same thing as omitting the attribute.

For fields under this representation, the normative guarantees are deliberately minimal:

1. every field offset is divisible by that field's alignment; and
2. the aggregate's alignment is at least the maximum alignment of its fields.

For structs, one additional guarantee applies: fields do not overlap when considered in some ordering. That ordering need not match declaration order.

The Reference then closes the set explicitly: there are no other default-representation data-layout guarantees.

For unsafe code, this rules out several common shortcuts. Source order does not imply address order. A compiler-observed offset is not a language-stable offset for a future compilation. Equal declarations instantiated in another compilation need not preserve an unspecified ordering merely because the source text is unchanged.

Basis: **normative**.

### Zero-sized struct fields can share addresses

The default struct non-overlap guarantee does not imply distinct addresses for all fields. The Reference explicitly warns that zero-sized fields may have the same address as other fields in the struct.

This matters when unsafe code uses addresses as field identities. Pointer equality between addresses derived from different zero-sized fields does not prove that the fields are the same logical field, and distinct logical fields need not receive distinct byte ranges when one occupies no bytes.

The result also prevents a stronger inference from the non-overlap rule: “all field starts are distinct” is not guaranteed.

Basis: **normative + derived** unsafe-code consequence.

### Representation attributes apply to the nominal type, not recursively to its fields

The Reference states that changing an outer type's representation can change inter-field padding but does not change the layout of the field types themselves. A `repr(C)` outer struct that contains a `repr(Rust)` inner struct does not convert that inner struct into C layout.

It also states that representation is an attribute of the item and does not depend on generic parameters. `Foo<Bar>` and `Foo<Baz>` therefore use the same representation **kind**, even though their instantiated field sizes, alignments, and resulting numeric layouts can differ.

For unsafe code, nested layout reasoning must recurse through each field's own representation and instantiated type. An outer `repr(C)` is not a blanket promise that every byte-level detail of nested Rust-representation fields is C-stable.

Basis: **normative + derived**.

### `repr(C)` structs use declaration order with explicit padding rules

For a `repr(C)` struct, the Reference gives a complete size/offset algorithm at the level relevant here:

1. begin at offset zero;
2. visit fields in declaration order;
3. before each field, add the minimum padding required to make the current offset a multiple of that field's alignment;
4. place the field at that offset and advance by its size; and
5. round the final size up to a multiple of the struct alignment.

The struct alignment is the alignment of its most-aligned field, subject to separate alignment modifiers.

The final rounding creates tail padding when necessary. Thus the end of the final declared field need not equal `size_of::<Struct>()`. Code that serializes “from first field through end of last field” and code that copies `size_of::<Struct>()` bytes are operating on potentially different byte sets.

The Reference warns that its illustrative pseudocode ignores integer-overflow concerns and recommends `Layout` for actual layout computations. A verifier should therefore model the semantic result, not literally inherit overflow-prone pseudocode arithmetic.

Basis: **normative + derived** tail-padding consequence.

### `repr(C)` unions put every field at offset zero and round size to union alignment

The C representation gives unions a stronger guarantee than the default representation.

For `repr(C)` unions:

- every field lives at byte offset zero;
- alignment is the maximum alignment of all fields; and
- size is the maximum field size rounded up to that union alignment.

The field that determines maximum size need not be the field that determines maximum alignment. The Reference includes an example where a six-byte field determines the preliminary size while a four-byte-aligned field forces the final union size to eight.

This is the layout contract unsafe code normally expects from a C union. It should not be projected onto an unannotated Rust union.

Basis: **normative**.

### A default Rust union does not guarantee zero field offsets

The unions chapter gives the general semantic property that union fields share common storage, but its field-access rules explicitly say that fields may have a nonzero offset **except when the C representation is used**.

This is a high-value distinction for unsafe code. The syntax `union U { ... }` alone does not justify treating `&raw const u.field` as numerically equal to a pointer to the union base. `repr(C)` provides the zero-offset guarantee; the default representation does not.

The union also has no active-field concept. A write chooses which field's type determines the bits written, but later reads do not consult a tag recording that choice.

Basis: **normative**.

### Union reads reinterpret storage under the selected field type

The Reference states that reading a union field reads the relevant bits as that field's type. The programmer must ensure those bits constitute a valid value of the read field type; otherwise the read has undefined behavior. Consequently, union field reads require `unsafe`.

For a `repr(C)` union, where every field begins at offset zero, the Reference characterizes a write through one field followed by a read through another as analogous to a `transmute` between the written and read field types. This analogy carries the same essential warning: layout overlap alone does not make every bit pattern valid for every field type.

Writes to union fields are safe because they overwrite storage and union fields cannot require implicit drop glue. This safety distinction is about the write operation, not a promise that any subsequent field read will be valid.

Basis: **normative**.

### Fieldless `repr(C)` enums match target C enum size/alignment, not C value validity

For a fieldless Rust enum, `repr(C)` selects the size and alignment of the target platform's default C enum representation. The Reference labels this correspondence a “best guess” because C enum representation is implementation-defined and compiler flags can alter it.

More importantly, the same section warns that Rust and C have different value-validity models. A C enum object can generally hold integer values beyond the named constants. A Rust fieldless enum may legally contain only its Rust discriminant values; other values are undefined behavior.

Thus:

```text
C-compatible size/alignment  !=  C-like set of valid values
```

This distinction is central to FFI and unsafe byte reinterpretation. Layout compatibility does not authorize arbitrary C enum integers as Rust enum values.

Basis: **normative**.

### Fieldful `repr(C)` enums have an explicit tagged-union representation

The Reference defines a fieldful `repr(C)` enum as a `repr(C)` struct with two conceptual fields:

- a `repr(C)` fieldless version of the enum as the tag; and
- a `repr(C)` union of `repr(C)` structs containing each variant's payload fields.

This is an explicit layout decomposition, not merely an analogy. It lets unsafe code derive the tag and payload placement from the C struct/union rules, subject to the target's C enum representation for the tag.

A unit variant can be represented by a zero-sized payload struct, and the Reference notes that a single-field variant can equivalently place the field directly in the payload union because the surrounding C-layout struct adds no distinct layout effect in that case.

The layout guarantee does not erase Rust enum validity. A raw tag/payload byte sequence still has to describe a valid Rust enum value before it can be treated as such.

Basis: **normative + derived** validity boundary.

### Primitive enum representations fix tag geometry

Primitive representations—`u8`, `u16`, `u32`, `u64`, `u128`, `usize`, and signed counterparts—apply only to enums.

For a fieldless enum, a primitive representation makes size and alignment equal to the corresponding primitive integer type. Discriminants must fit that representation.

For an enum with fields, the Reference defines the layout as a `repr(C)` union of `repr(C)` variant structs. Each variant struct begins with the primitive-representation form of the fieldless enum as its tag, followed by that variant's fields.

This differs structurally from plain fieldful `repr(C)`, whose tag and payload union are separate top-level struct fields. A proof that reasons about tag location should therefore branch on the actual representation form instead of treating all explicitly represented enums as one layout pattern.

Basis: **normative**.

### `repr(C, primitive)` preserves the C tagged-union shape but fixes the tag representation

For a fieldful enum, combining `repr(C)` with a primitive representation modifies the C representation by replacing the target-default C enum tag with the chosen primitive tag.

For example, `repr(C, u8)` still uses the C-style top-level tag-plus-payload layout, but the discriminant enum has one-byte `u8` size and alignment. The Reference demonstrates that this can materially change the total enum size compared with plain `repr(C)`.

This form is useful when unsafe or FFI code requires the C tagged-union organization but cannot tolerate the target-dependent default C enum width.

Basis: **normative**.

### `repr(align(N))` and `repr(packed(N))` change alignment without supplying field order

The alignment modifiers alter a `Rust` or `C` representation; they are not independent field-order representations.

`align(N)` raises aggregate alignment when `N` exceeds the unmodified alignment. If `N` is smaller, it has no effect.

`packed(N)` lowers field alignment for placement to `min(N, field_alignment)`. When `N` exceeds the unmodified type alignment, it has no effect. Inter-field padding is then the minimum required by those possibly lowered placement alignments. In particular, `packed(1)` guarantees no inter-field padding.

Neither modifier, by itself, determines struct field order or enum-variant layout. `repr(packed)` on an otherwise Rust-representation struct therefore does **not** make source declaration order stable. If code needs both a specified field order and packing behavior, it must rely on a representation combination whose rules actually provide those properties, such as the allowed `C` plus packing form at this revision.

Basis: **normative + derived**.

### Packed placement can make ordinary field references invalid

Packing changes where a field is placed; it does not change the field type's own required alignment or internal layout. A packed aggregate can therefore contain a field at an address that is insufficiently aligned for an ordinary `&Field` or `&mut Field`.

The Reference calls this out directly: references to unaligned fields are not allowed because they are undefined behavior. Its recommended patterns are to copy the field value when ordinary field access can do so without forming a reference, or to take a raw pointer with `&raw` and use unaligned pointer operations.

For a verifier, the crucial fact is that the aggregate's effective field-placement alignment and the field type's own reference alignment are different quantities. Lowering the former does not weaken the latter.

Basis: **normative + derived** proof obligation.

### Alignment-modifier composition is restricted at this revision

The exact Reference revision imposes several constraints:

- alignment arguments are powers of two from 1 through `2^29`;
- omitted `packed` means `packed(1)`;
- `align` and `packed` cannot be applied to the same type;
- a packed type cannot transitively contain an aligned type; and
- the modifiers apply only to the `Rust` and `C` representations.

`align` can also be applied to an enum; its effect on enum alignment is defined as if the enum were wrapped in a newtype struct carrying the same alignment modifier.

These are exact-pin rules. They should be revalidated rather than projected onto a later layout-feature revision.

Basis: **normative**.

### `repr(transparent)` delegates both layout and ABI to one effective field

At this Reference revision, `repr(transparent)` may be applied to a struct or single-variant enum that contains:

- any number of fields whose size is zero **and** whose alignment is one; and
- at most one additional field.

The transparent aggregate has the same layout **and ABI** as that one additional field, or as unit when no such field exists.

The conjunction in the zero-sized exception matters. A zero-sized field with alignment greater than one is not in the freely repeatable size-zero/alignment-one category; it counts toward the “at most one other field” constraint.

Transparent layout is also stronger than an accidental equality of `size_of` and `align_of`. The Reference explicitly delegates ABI as well as layout. Conversely, two unrelated types that merely happen to have equal size/alignment gain no such guarantee.

Basis: **normative + derived** interpretation of the field constraint.

### Representation does not by itself settle validity, padding initialization, or ABI compatibility

Aggregate representation answers layout questions: field offsets/order where specified, total size/alignment rules, and explicit enum tag/payload geometry where guaranteed. Several adjacent properties remain separate.

First, layout and validity differ. The `repr(C)` enum warning and union-read rules show this directly: bytes can fit a layout while failing to represent a valid Rust value.

Second, layout and initialization differ. A C-layout algorithm can identify padding regions, but the fact that bytes lie within an object's extent does not itself make padding initialized or safely readable.

Third, the Reference states that even types with the same layout can differ in function-call ABI compatibility. `repr(transparent)` is notable precisely because it explicitly delegates ABI; ordinary equality of aggregate size, alignment, or offsets does not.

Unsafe code should therefore treat a layout proof as one input to a larger argument, not as a substitute for value validity, initialization, provenance, or call-ABI reasoning.

Basis: **normative + derived** separation of concerns.

## Boundaries

**No compiler-layout reverse engineering.** The report does not inspect rustc's chosen field order, niche placement, tag elision, or other implementation details for default `repr(Rust)` aggregates. Where the Reference says “no other guarantees,” this report leaves the layout unspecified.

**Niches are separate.** Default enum niche optimization, niche eligibility, and bit-validity are intentionally outside this report. They are tracked as a separate #3720 subject.

**Padding initialization is separate.** The `repr(C)` algorithms identify where padding exists but do not establish whether padding bytes are initialized or safely observable.

**DST aggregate tails are separate.** This report does not derive the complete layout algorithm for dynamically sized trailing fields. The dedicated DST/slice subject should own that behavior.

**FFI call ABI is separate.** `repr(C)` provides the documented data representation. It does not by itself establish every calling-convention or toolchain compatibility property, and the Reference explicitly distinguishes data layout from function-call ABI compatibility.

**C enum width can depend on external C compiler configuration.** Rust's plain `repr(C)` fieldless-enum choice is a target-ABI best guess; C flags can differ. `repr(C, primitive)` can fix Rust's tag representation but does not control arbitrary external C compiler settings.

**Union validity is not an active-field discipline.** The Reference expressly says Rust unions have no active field. This report does not import C++ active-member rules into Rust.

**No claim that default union fields begin at zero.** The Reference says the opposite boundary explicitly: nonzero union field offsets are possible except under C representation.

**No claim from equal geometry to safe transmutation.** Equal size/alignment is insufficient to establish field mapping, initializedness, valid bit patterns, provenance, or ABI.

**No adjacent-version continuity.** Every representation restriction and guarantee should be checked again when the Rust/Reference subject changes.

## Evidence

Normative language-layout subject: `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/type-layout.md`, blob `2ee902aef043f4d299e009f6a69d1815d862e69e` — default `Rust` guarantees; outer-versus-inner representation; `repr(C)` struct, union, and enum layouts; primitive enum representations; `repr(C, primitive)`; alignment/packing modifiers; transparent representation; general layout-versus-ABI boundary.
- `src/items/unions.md`, blob `c330b037007ff36dc2e8475daefc96e176121914` — common union storage, absence of an active field, possible nonzero field offsets outside C representation, read validity, and write/read safety distinction.

Toolchain context:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` is the exact compiler/library revision used by the neighboring Anneal primitive-semantics reports for `nightly-2026-05-31`; its commit was re-read during this run.
- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `rust-toolchain`, blob `4e348edab20d6bd5b195e758afe20f9d8258a3e1`, directly selects `nightly-2026-05-31`.

No execution evidence is included. The report deliberately prefers the normative guarantee surface over an observed compiler layout for cases where Rust leaves implementation freedom.

## Revalidation

For another Rust/Reference revision, revalidation should begin with a focused diff of `src/type-layout.md` and `src/items/unions.md` rather than with a broad compiler crawl.

Check, in order:

1. the complete guarantee set under `repr(Rust)`, especially field ordering, non-overlap, and zero-sized-field address behavior;
2. the `repr(C)` struct field-placement/final-rounding algorithm;
3. C-union field offsets, maximum-size/alignment rules, and whether default unions still permit nonzero offsets;
4. fieldless and fieldful `repr(C)` enum models and the warning about C enum validity;
5. primitive enum and combined `repr(C, primitive)` representations;
6. `align`/`packed` range, composition, transitive-containment, and packed-reference restrictions; and
7. the exact `repr(transparent)` field constraint and whether both layout and ABI delegation remain stated.

If Anneal needs to depend on a compiler choice that remains unspecified—for example the current field order of a `repr(Rust)` struct or the niche layout of an enum—do not strengthen this report by observation alone. Instead, either redesign the verified code to depend only on a language guarantee, add an explicit representation that supplies the needed guarantee, or create a separately scoped exact-compiler report/probe whose applicability is intentionally narrower.

A cheap execution probe can still protect implementation-sensitive integration code. On every supported target, preserve `size_of`, `align_of`, and `offset_of!` output for a small matrix containing:

- the same fields under default, `repr(C)`, packed, and aligned representations;
- zero-sized fields, including an over-aligned zero-sized type;
- a C union whose maximum-size and maximum-alignment fields differ;
- fieldless `repr(C)` and primitive-repr enums;
- fieldful `repr(C)`, primitive-repr, and `repr(C, primitive)` enums; and
- valid transparent wrappers.

Treat such output as **execution evidence about that exact compiler/target**, not as a replacement for the normative boundary recorded here.
