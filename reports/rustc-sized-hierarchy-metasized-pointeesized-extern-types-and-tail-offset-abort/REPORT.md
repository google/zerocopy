# Rust's `Sized` / `MetaSized` / `PointeeSized` hierarchy, `extern type` tails, and the run-time abort on non-zero-offset tail projection

## Summary

- On the examined nightly compilers, sizedness is a three-level trait chain
  declared in `core::marker`: `Sized: MetaSized`, `MetaSized: PointeeSized`,
  `PointeeSized`. `Sized` types have a compile-time size; `MetaSized` types
  (`[T]`, `str`, `dyn Trait`, and structs or tuples ending in one) have a size
  and alignment computable from pointer metadata; `extern type`s, and structs
  ending in one, implement only `PointeeSized`. The two new traits are unstable
  (`sized_hierarchy`). The proposal they come from, Rust RFC pull request 3729,
  was **open and unmerged** on 2026-11-22 and names the traits `SizeOfVal` and
  `Pointee`, not `MetaSized` and `PointeeSized`.
- `?Sized` lowers to a `MetaSized` bound. Consequently `size_of_val`,
  `align_of_val`, `Box<T>`, any `fn f<T: ?Sized>`, and any trait without an
  explicit sizedness supertrait reject `extern type`s **at compile time**
  (`E0277`). This statically removes the run-time panic that RFC 1861 allowed
  for `size_of_val` on extern types.
- Pointer width does not identify the tier. Pointers to `extern type`s and to
  structs ending in one are thin (8 bytes on the 64-bit host), exactly like
  pointers to `Sized` types; only the middle tier has wide (16-byte) pointers.
- The static discipline has one hole that the compiler closes at run time
  instead: projecting to an `extern type` tail field at a **non-zero static
  offset** (`&h.tail`, or `&raw const h.tail`) type-checks without any
  sizedness obligation, also inside `#[forbid(unsafe_code)]` code, and the
  generated code calls `panic_nounwind("attempted to compute the size or
  alignment of extern type …")`, i.e. the process aborts. Miri reports
  `unsupported operation: extern type field does not have a known offset` for
  the same projection. Offset-0 tails (`#[repr(transparent)]` wrappers, a
  zero-sized prefix) project fine. This is deliberate upstream behaviour pinned
  by a `run-crash` UI test; it is a missing static check, not undefined
  behaviour.
- `#[repr(C, packed)]` does not help in the implementation, although it could:
  the tail offset is independent of the unknown foreign alignment exactly when
  the static prefix offset is 0, or the struct is `packed(N)` with `N` dividing
  that offset (always true for `packed(1)`). Both code generation and the
  interpreter special-case only offset 0, so a `packed(1)` header still aborts.
  For unpacked structs the abort coincides exactly with the uncomputable case.
- Miri: Stacked Borrows cannot retag a pointee without a dynamic size; it skips
  the retag and warns once. Tree Borrows retags the statically known prefix and
  initialises everything else lazily, so references to a bare `extern type` or
  to an offset-0 wrapper run with zero warnings. With default flags, however,
  Tree Borrows fails with the "unknown offset" error already when a reference
  to a struct with a non-zero-offset extern tail is *created*, because its
  precise interior-mutability walk projects to the tail;
  `-Zmiri-tree-borrows-no-precise-interior-mut` removes that failure.
- The unsizing coercion for tuples (`unsized_tuple_coercion`) was removed in
  1.87.0. Unsized tuple *types* such as `(u8, [u32])` still exist, are
  `MetaSized`, have wide pointers, and can only be reached through raw-pointer
  casts.
- Anneal's trusted MIR semantics at the examined revision admit none of this:
  `TyKind::Foreign`, slices, `str`, `dyn`, struct ADTs, every non-empty place
  projection and every reference-creating rvalue fail closed as unsupported.
- A kernel-checked Lean 4 model (60 theorems, `propext` the only axiom) proves
  the layout-totality characterisation of `MetaSized`, the tail-offset
  computability criterion, the agreement of a prefix-only Tree Borrows retag
  with a retag over the true extent for extern-tailed pointees, and three
  sharpness counterexamples.

## Applicability

**Subjects and how they relate.** The report is about one behaviour family in
`rust-lang/rust` (compiler, `core`, and the in-tree Miri under
`src/tools/miri`), examined at three revisions, read against two RFC texts, and
then related to what Anneal's trusted layer admits.

| Subject | Revision | What was done |
| :--- | :--- | :--- |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (2026-05-31) | Source audited; `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (LLVM 22.1.6) and its Miri **executed**. The toolchain's bundled `rust-src` / `rustc-src` files that were spot-checked have the same Git blob hashes as the files at this revision. |
| `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (2026-11-11) | Cited source regions compared with the first revision. Not executed for this report; a preserved earlier output record from `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` corroborates. |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (default-branch head, 2026-11-22) | Cited source regions compared only. |
| `rust-lang/rfcs` | `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` | Merged RFC 1861 text read. The tree at this revision contains no file for RFC 3729. |
| `rust-lang/rfcs` | `1bb22f00880cb6d24192af4041585683b56e9b3a` | Head commit of open pull request 3729; proposal text read. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean` and two files of the vendored `vendor/lean-miri` tree read. |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Used to check the Lean model. |

**Exact observation.** All execution results are from the first revision's
toolchain on `x86_64-unknown-linux-gnu` (64-bit pointers), LLVM backend,
edition 2021 unless a case says otherwise, with the unstable features
`extern_types`, `sized_hierarchy` and (one case) `freeze`. Native runs used
opt-level 0 and opt-level 3. Miri was run in four modes: default (Stacked
Borrows), `-Zmiri-tree-borrows`,
`-Zmiri-tree-borrows -Zmiri-tree-borrows-no-precise-interior-mut`, and
`-Zmiri-disable-stacked-borrows`.

**Extension to the two later revisions (derived).** Each cited source region
was extracted at all three revisions by anchor and brace matching
(`support/source_region_continuity.json`). Between the first and second
revision, 20 of 32 regions are byte-identical, among them the three trait
items, `size_of_val`, `align_of_val`, the interpreter's `project_field`, the
builtin-impl tables, the removed-feature entry and all but one of the upstream
test files. The
other regions differ by refactoring that leaves the cited logic in place, as
read from the diffs: a `Span` parameter threaded through
`size_and_align_of_dst`; `layout.align.abi` shortened to `layout.align`; the
local `this` renamed to `ecx` in the Miri functions; a helper call replacing an
accessor chain in `NewPermission::new`; the relaxed-bound validation moved out
of `add_implicit_sizedness_bounds`; one test directive line dropped. Between
the second and third revision every region is identical except the three
builtin tables, each of which gained handling for a new `ty::View` kind
(grouped with `ty::Foreign` in one of them) while the `ty::Foreign` handling
is unchanged. On this basis the source findings are stated
for all three revisions. Execution findings are *observed* for the first
revision only; for the second they are supported by the preserved earlier
record (same error codes, same abort message, same Miri diagnostics), and for
the third they are an inference from unchanged source, not an observation.

**Scope limits that matter.** Pointer widths (8 / 16 bytes) and the offsets
quoted are for the 64-bit host. Everything involving `MetaSized`,
`PointeeSized` or `extern type` is nightly-only. The Lean development is a
standalone abstract model; it imports nothing, in particular none of Anneal's
`Trusted.*` modules, and its relation to the compiler source is by the
correspondence table in the findings, not by a machine-checked link.

**Relation to another report in this corpus.** The package
`const-generics-ctfe-packed-provenance-extern-types-and-array-init-cursors`
lists as unknown whether stabilising the sizedness hierarchy will turn
`size_of_val` on an `extern type` into a compile-time error. On the three
(unstable, nightly) revisions examined here it already is one; stabilisation
itself remains outside this report.

## Findings

Scenario names and case labels such as `b01` are keys of
`support/probe_results_rustc_1_98_0_nightly_2026_05_31.json`, where the
complete source of each case and its diagnostics are recorded. Line numbers
without a revision refer to the first `rust-lang/rust` revision.

### 1. The three traits

`library/core/src/marker.rs` at the first revision, lines 145–192 (the same
text at the same lines at the second revision and at lines 146–193 at the
third):

```rust
#[lang = "sized"]
#[fundamental]
#[rustc_specialization_trait]
#[rustc_deny_explicit_impl]
#[rustc_dyn_incompatible_trait]
// `Sized` being coinductive, despite having supertraits, is okay as there are no user-written impls,
// and we know that the supertraits are always implemented if the subtrait is just by looking at
// the builtin impls.
#[rustc_coinductive]
pub trait Sized: MetaSized {}

/// Types with a size that can be determined from pointer metadata.
#[unstable(feature = "sized_hierarchy", issue = "144404")]
#[lang = "meta_sized"]
#[rustc_coinductive]
pub trait MetaSized: PointeeSized {}

/// Types that may or may not have a size.
#[unstable(feature = "sized_hierarchy", issue = "144404")]
#[lang = "pointee_sized"]
#[rustc_coinductive]
pub trait PointeeSized {}
```

(Abridged: documentation, `#[stable]`, `#[diagnostic::on_unimplemented]` and,
on the two new traits, `#[fundamental]`, `#[rustc_specialization_trait]` and
`#[rustc_deny_explicit_impl]` are omitted.) All three are lang items, all three
are coinductive, none can be implemented by users. The implementing change is
`rust-lang/rust` pull request 137944 "Sized Hierarchy: Part I" (merged
2025-06-17, merge commit `86d0aef80403f095d8bbabf44d9fdecfcd45f076`);
`rust-lang/rust` tracking issue 144404 was open on 2026-11-22.

Basis: source (three revisions) + execution (using either new trait without
`#![feature(sized_hierarchy)]` is `E0658`, probe case `b17`).

### 2. Which types sit in which tier

Three independent places in the compiler agree, for `SizedTraitKind::{Sized,
MetaSized}`:

- `Ty::has_trivial_sizedness` (`compiler/rustc_middle/src/ty/sty.rs:1929-1974`):
  `ty::Str | ty::Slice(_) | ty::Dynamic(_, _)` is `false` for `Sized`, `true`
  for `MetaSized`; `ty::Foreign(..)` is `false` for both; a tuple defers to its
  last element; an ADT defers to its `sizedness_constraint`.
- `sizedness_constraint_for_ty` (`compiler/rustc_ty_utils/src/ty.rs:20-79`):
  commented "Never `Sized`" / "Always `MetaSized`" for `str`, slices and
  `dyn`, and "Never `MetaSized` or `Sized`" for `ty::Foreign(..) => Some(ty)`.
- `assemble_builtin_sized_candidate`
  (`compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:1240-1307`):
  "`MetaSized` but not `Sized`" for `ty::Str | ty::Slice(_) | ty::Dynamic(..)`
  and "Not `MetaSized` or `Sized`" for `ty::Foreign(..) => {}`.

There is no `PointeeSized` predicate inside the type system: both trait
solvers treat reaching one as a compiler bug ("`PointeeSized` is removed during
lowering": `bug!` at `candidate_assembly.rs:109-110`, `unreachable!` at
`compiler/rustc_next_trait_solver/src/solve/assembly/mod.rs:594-595`), and
`compiler/rustc_hir_analysis/src/hir_ty_lowering/mod.rs:971-982` drops such
bounds because they "aren't represented in the middle::ty IR". Writing
`T: PointeeSized` therefore means "no sizedness obligation", and every type
satisfies it by construction.

| Type | `Sized` | `MetaSized` | `PointeeSized` |
| :--- | :---: | :---: | :---: |
| integers, references, raw pointers, arrays, closures, `!` | yes | yes | yes |
| `[T]`, `str`, `dyn Trait` | no | yes | yes |
| `extern type` | no | no | yes |
| tuple | as its last element | as its last element | yes |
| struct | as its last field | as its last field | yes |

`extern type`s also implement no auto trait: the auto-trait arm for
`ty::Foreign(..)` (`candidate_assembly.rs:774-785`) adds no candidate ("Since
the contents of foreign types is unknown, we don't add any `..` impl"). They
are observed to be `!Unpin`, `!Freeze`, `!Send` and `!Sync`, and a struct
ending in one is observed to be `!Unpin` and `!Freeze`.

Basis: source + execution (probe part A1 compiles one generic tier witness per
row; cases `b12`, `b13` show the chain is strict in both steps; cases
`b23`–`b27`, `b34`, `b35` for the auto traits).

### 3. How written bounds lower: `?Sized` is `MetaSized`

`add_implicit_sizedness_bounds`
(`compiler/rustc_hir_analysis/src/hir_ty_lowering/bounds.rs:162-235` at the
first revision, `172-227` at the others) decides, per bound site:

- a `?Sized` (or negative `Sized`) bound with no other explicit sizedness bound
  adds a `MetaSized` clause, with the comment "`?Sized` is equivalent to
  `MetaSized` (but only add the bound if there aren't any other explicit
  ones)";
- with no sizedness bound at all, a type parameter, associated type or opaque
  type gets `Sized`, and a **trait definition gets a default `MetaSized`
  supertrait**;
- no default supertrait is ever added to `PointeeSized` itself or to auto
  traits.

Basis: source (three revisions) + execution: `fn f<T: ?Sized>() {
need_meta::<T>() }` compiles (`b14`); `fn f<T: PointeeSized>() {
need_meta::<T>() }` and `fn f<T: MetaSized>() { need_sized::<T>() }` are
`E0277` (`b12`, `b13`).

### 4. What this rejects at compile time

All on the executed toolchain, all `error[E0277]`, each naming the missing
trait:

| Program fragment | Diagnostic (abridged) | Case |
| :--- | :--- | :--- |
| `size_of_val(p)` with `p: &OpaqueExtern` | the trait `MetaSized` is not implemented for `OpaqueExtern` | `b01` |
| `align_of_val(p)` | same | `b02` |
| `fn legacy<T: ?Sized>(_: &T)` called with `&OpaqueExtern` | same | `b03` |
| `need_meta(h)` with `h: &Hdr`, `Hdr { tag: u32, tail: OpaqueExtern }` | within `Hdr`, the trait `MetaSized` is not implemented for `OpaqueExtern` | `b04` |
| `size_of_val(h)` for the same `Hdr` | same | `b22` |
| `fn f(_: Box<OpaqueExtern>)` | `MetaSized` not implemented | `b19` |
| `impl Describe for OpaqueExtern` where `trait Describe { … }` | `MetaSized` not implemented (default supertrait) | `b15` |
| `size_of::<OpaqueExtern>()`; an `extern type` field that is not last | `Sized` not implemented | `b20`, `b06` |

Accepted: `need_pointee(h)` and `need_pointee(o)` for `T: PointeeSized`
(`b05`); `impl Describe for OpaqueExtern` once the trait is declared
`trait Describe: PointeeSized` (`b16`); defining `#[repr(C, packed)]` structs
with an extern tail (`b09`). `core::mem::size_of_val` is declared
`pub const fn size_of_val<T: ?Sized>(val: &T) -> usize`
(`library/core/src/mem/mod.rs:401-404`): its written bound is still `?Sized`,
and the rejection comes entirely from the lowering in finding 3. Upstream pins the same
behaviour in `tests/ui/extern/extern-types-size_of_val.rs` with the expected
output "the trait `MetaSized` is not implemented for `A`".

`core::mem::offset_of!(Hdr, tail)` is also rejected (`E0277`, `Sized` not
implemented), but equally for a `[u16]` tail (`b28`, `b30`): it demands a
`Sized` field and so does not distinguish the two unsized tiers.

Basis: source + execution.

### 5. Pointer metadata and pointer width

`Ty::ptr_metadata_ty_or_tail` returns unit for `ty::Foreign(..)` with the
comment "Extern types have metadata = ()"
(`compiler/rustc_middle/src/ty/sty.rs:1758-1759`),
and pointer layout returns a single data-pointer scalar when the struct tail is
`ty::Foreign(..)` (`compiler/rustc_ty_utils/src/layout.rs:467-472`).
`core::ptr::Pointee` is declared `pub trait Pointee: PointeeSized`, and
`pub trait Thin = Pointee<Metadata = ()> + PointeeSized;`
(`library/core/src/ptr/metadata.rs:59,85`). RFC 1861 specifies this: "For extern
types the metadata is simply `()`" and "if we store an extern type at the end
of a container (such as a struct or tuple) pointers to that container will also
be identical to raw pointers".

Observed `size_of` of `*const T` on the 64-bit host:

| `OpaqueExtern` | `HeaderWithExtern` | `WrapExtern` | `u32` | `[u32]` | `str` | `dyn Tr` | `(u8, [u32])` |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| 8 | 8 | 8 | 8 | 16 | 16 | 16 | 16 |

A thin pointer therefore says "`Sized` **or** `PointeeSized`-only"; a consumer
that equates "thin" with "has a static size" is wrong for extern tails.

Basis: normative (RFC 1861) + source + execution (part A1).

### 6. Run-time layout is total exactly on `MetaSized`

The interpreter's `size_and_align_from_meta`
(`compiler/rustc_const_eval/src/interpret/eval_context.rs:432-518`) is
documented "This can fail to provide an answer for extern types": sized layouts
return their static size and alignment; slices multiply the length metadata;
`dyn` reads the vtable; `ty::Foreign(_) => interp_ok(None)`; a struct or tuple
recurses into its last field and returns `None` if that does ("A field with an
extern type. We don't know the actual dynamic size or the alignment"),
otherwise caps the tail alignment at the pack value, takes the maximum with the
static alignment, and rounds
`unsized_offset_unadjusted.align_to(unsized_align) + unsized_size` up to it.
Code generation's `size_and_align_of_dst`
(`compiler/rustc_codegen_ssa/src/size_of_val.rs:15-184`) has the same shape,
except that its `ty::Foreign(_)` arm emits a call to the `PanicNounwind` lang
item with the message "attempted to compute the size or alignment of extern
type `{t}`".

Observed dynamic `(size, align)`: `(u8, [u16])` with length 3 gives `(8, 2)`;
`(u8, [u32])` with length 0 gives `(4, 4)`; `dyn Tr` over a `u64` gives
`(8, 8)`; `[u32]` of length 2 gives `(8, 4)`. (Tuple layout is unspecified;
these are observations, not guarantees.)

Because finding 3 makes `MetaSized` the bound of every `?Sized` API, the
`Foreign` arms are unreachable from `size_of_val` and `align_of_val` in
type-checked code. They remain reachable from field projection (finding 8).

Basis: source + execution; the totality statement is also proved for the model
(finding 15, `runtime_layout_total_iff_metaSized`).

### 7. Tuple unsizing is gone; unsized tuple types remain

`compiler/rustc_feature/src/removed.rs:296-297`:

```rust
(removed, unsized_tuple_coercion, "1.87.0", Some(42877),
 Some("The feature restricts possible layouts for tuples, and this restriction is not worth it."), 137728),
```

`rust-lang/rust` pull request 137728 "Remove unsizing coercions for tuples"
merged on 2025-03-05 (merge commit `257b4947ed14795a8411df53b6cf6d5a57b56240`). Observed:
`#![feature(unsized_tuple_coercion)]` is `error[E0557]: feature has been
removed` with the note "removed in 1.87.0" (`b07`); without the feature,
coercing `&(u8, [u32; 2])` to `&(u8, [u32])` is `E0308` (`b08`). The *type*
`(u8, [u32])` still exists, is `MetaSized`, and has a wide pointer (findings 2,
5); part A1 builds references to it only by casting a `*const [T]`.

Basis: source + execution.

### 8. Projecting to an `extern type` tail: what the compiler does

Type checking and MIR building impose no sizedness obligation on a field place.
The MIR of the safe projections is just (from `-Zunpretty=mir`; the `//`
annotations are added here):

```text
_0 = &((*_1).2: OpaqueExtern);             // &h.tail, repr(C) header
_0 = &raw const ((*_1).2: OpaqueExtern);   // &raw const h.tail, packed header
_0 = &((*_1).0: OpaqueExtern);             // repr(transparent) wrapper
_0 = &((*_1).1: OpaqueExtern);             // zero-sized prefix
```

Code generation, `PlaceRef::project_field`
(`compiler/rustc_codegen_ssa/src/mir/place.rs:166-248` at the first revision,
`175-258` later), condensed:

```rust
// Simple cases, which don't need DST adjustment:
//   * known alignment - sized types, `[T]`, `str`
//   * offset 0 -- rounding up to alignment cannot change the offset
match field.ty.kind() {
    _ if field.is_sized() => return simple(),
    ty::Slice(..) | ty::Str => return simple(),
    _ if offset.bytes() == 0 => return simple(),
    _ => {}
}
// …
// Get the alignment of the field
let (_, mut unsized_align) = size_of_val::size_and_align_of_dst(bx, field.ty, meta);
// For packed types, we need to cap alignment.
if let ty::Adt(def, _) = self.layout.ty.kind() && let Some(packed) = def.repr().pack { /* min */ }
// Bump the unaligned offset up to the appropriate alignment
let offset = round_up_const_value_to_alignment(bx, unaligned_offset, unsized_align);
```

For an `extern type` tail at a non-zero static offset the call to
`size_and_align_of_dst` emits the non-unwinding panic *before* the pack cap is
looked at. The interpreter's `project_field`
(`compiler/rustc_const_eval/src/interpret/projection.rs:150-201`, identical at
all three revisions) has the same case split (condensed):

```rust
match self.size_and_align_from_meta(&base_meta, &field_layout)? {
    Some((_, align)) => { /* cap for packed, then */ (base_meta, offset.align_to(align)) }
    None if offset == Size::ZERO => {
        // If the offset is 0, then rounding it up to alignment wouldn't change anything,
        // so we can do this even for types where we cannot determine the alignment.
        (base_meta, offset)
    }
    None => {
        // We cannot know the alignment of this field, so we cannot adjust.
        throw_unsup!(ExternTypeField)
    }
}
```

`ExternTypeField` prints "`extern type` field does not have a known offset"
(`compiler/rustc_middle/src/mir/interpret/error.rs:717`).

The unoptimised LLVM IR of the probe's safe library confirms the split
(mangled symbol prefixes shortened to `…`):

```llvm
define ptr @…tail_of_header(ptr align 4 %h) unnamed_addr #0 {
start:
; call core::panicking::panic_nounwind
  call void @…core9panicking14panic_nounwind(ptr @str.0, i64 72) #2
  %_0 = getelementptr inbounds i8, ptr %h, i64 6
  ret ptr %_0
}
define ptr @…tail_of_transparent(ptr %w) unnamed_addr #0 {
start:
  ret ptr %w
}
```

The 72-byte string is the abort message (its text for `OpaqueExtern` is 72
bytes long). The `getelementptr … i64 6` after the call is the static offset of
the tail (`u32` at 0, `u16` at 4, tail at 6) rounded with the placeholder
alignment 1 that `size_and_align_of_dst` returns after emitting the call ("This
function does not return so we can now return whatever we want"); it is never
reached at run time. `tail_of_packed` contains the same call; `tail_of_zero_prefix`,
`tail_of_slice_header`, `tail_of_dyn_header` and `magic_of_header` contain no
call to `panic_nounwind`.

Two side conditions on *how* the place may be borrowed:

- `&p.tail` on a `packed` struct is rejected with `error[E0793]: reference to
  field of packed struct is unaligned` ("this struct is 1-byte aligned, but the
  type of this field may require higher alignment"), because
  `place_unalignment` (`compiler/rustc_const_eval/src/util/alignment.rs:9-51`)
  treats an unsized tail other than a slice or `str` as possibly unaligned
  (`b10`). The raw borrow `&raw const p.tail` is accepted, also under
  `#![forbid(unsafe_code)]` (`b11`).
- In edition 2021 a `#![forbid(unsafe_code)]` crate may itself declare the
  extern type with a plain `extern "C" { type T; }` block (`b18`). An
  `unsafe extern` block trips the `unsafe_code` lint (`b31`), and edition 2024
  requires `unsafe extern` (`b32`), so there the declaration must live outside
  the lint's scope; the projection still compiles inside
  `#[forbid(unsafe_code)]` (`b33`).

Upstream documents and pins the behaviour: `tests/ui/extern/extern-types-field-offset.rs`
is a `//@ run-crash` test whose comments read "Projecting to the newtype works,
because it is always at offset 0", "Accessing sized fields is perfectly fine,
even at non-zero offsets" and "This needs to compute the field offset, but we
don't know the type's alignment, so this panics", with expected stderr
"attempted to compute the size or alignment of extern type `Opaque`" followed
by "thread caused non-unwinding panic. aborting."; Miri's
`tests/fail/extern-type-field-offset.rs` expects "does not have a known
offset".

Basis: source + execution.

### 9. Native execution matrix

A library crate compiled with `#![forbid(unsafe_code)]` (exit 0, no warnings)
exports the projecting functions; a second crate creates the references from a
`[u32; 4]` buffer with `unsafe` and calls them. Results are the same at
opt-level 0 and opt-level 3.

| Scenario | Operation | Result |
| :--- | :--- | :--- |
| `header_ref_only` | create `&HeaderWithExtern`, read `h.magic` | exit 0, `magic=0xdeadbeef` |
| `header_tail_ref` | safe `&h.tail`, `#[repr(C)] { u32, u16, tail }` | **SIGABRT** |
| `header_tail_raw_no_ref` | `&raw const (*p).tail` through a raw pointer | **SIGABRT** |
| `packed_tail_raw` | safe `&raw const h.tail`, `#[repr(C, packed)]` | **SIGABRT** |
| `transparent_tail_ref` | safe `&w.inner`, `#[repr(transparent)]` | exit 0, `offset=0` |
| `zero_prefix_tail_ref` | safe `&z.tail` behind a `()` field | exit 0, `offset=0` |
| `opaque_reborrow`, `opaque_mut_reborrow` | `&*o`, `&mut *o` on a bare extern type | exit 0 |
| `slice_tail_control` | safe `&h.tail`, `[u16]` tail, same prefix | exit 0, `offset=6 len=2` |
| `dyn_tail_control` | safe `&h.tail`, `dyn Tr` tail over `u64` after a `u8` | exit 0, `offset=8 get=7` |

Abort stderr (thread id normalised):

```text
thread 'main' (<TID>) panicked at /rustc/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/panicking.rs:225:5:
attempted to compute the size or alignment of extern type `OpaqueExtern`
note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace
thread caused non-unwinding panic. aborting.
```

The type is printed as `a2_safe_lib::OpaqueExtern` when the projection is
compiled in a crate other than the one declaring the type. The two controls
show both paths working for `MetaSized` tails: the slice tail takes the static
path (offset 6), and the `dyn` tail takes the dynamic path and lands at offset
8, the static offset 1 rounded up to the alignment 8 read from the vtable.

Basis: execution.

### 10. When is the tail offset computable at all?

Let `off` be the static offset the layout assigns to the tail field and let the
foreign type's true alignment be an unknown power of two `a`. The tail then
lives at `round_up(off, cap(a))`, where `cap` is the identity for an unpacked
struct and `min(·, N)` for `packed(N)`. Call the offset *static* if this value
is the same for every power of two `a`.

- **Criterion.** The offset is static if and only if `off = 0`, or the struct
  is `packed(N)` and `N` divides `off`. (Lean:
  `extern_tail_offset_static_iff`.)
- **The two layouts a compiler fast path can key on.** For an unpacked or
  `packed(1)` struct this reads: static iff `off = 0` or the struct is
  `packed(1)`. (Lean:
  `extern_tail_offset_static_iff_zero_prefix_or_packed1_specialization`.) The
  dichotomy is not complete for larger pack values: offset 4 under `packed(2)`
  is static, offset 6 under `packed(4)` is not (`packedN_examples`).
- **Unpacked structs: the abort is exact.** For an unpacked struct the compiled
  projection aborts if and only if the offset is not static
  (`unpacked_foreign_tail_aborts_iff_not_static`), and whenever it returns an
  offset that offset is correct for every admissible alignment
  (`codegen_foreign_tail_value_is_true_offset`). For the probe's header the
  tail would sit at 6, 8 or 16 for foreign alignments 2, 4 or 16
  (`ce2_nonzero_prefix_extern_tail_requires_unknown_align`).
- **Packed structs: the abort is not forced.** For `packed(1)` and any
  non-zero `off`, the offset is static and equals `off`, yet the compiled
  projection aborts and the interpreted one is unsupported
  (`packed1_foreign_tail_static_but_refused`; observed in scenario
  `packed_tail_raw`). A projection that additionally returns `off` when
  `packed(N)` with `N` dividing `off` is correct on every answer and refuses
  exactly the non-static cases (`specialized_projection_sound_and_complete`).

`N` is a power of two, as `packed(N)` requires. The first bullet's "if"
direction for packed structs relies on the cap: every capped alignment is a
power of two at most `N`, so it divides `N` and hence `off`.

Basis: derived (kernel-checked for the model; the model's projection functions
are transcriptions of the two case splits quoted in finding 8) + execution for
the `packed(1)` instance.

### 11. Miri: Stacked Borrows, Tree Borrows, and the precise walk

Single-file variant of the same program; the projecting functions sit in a
`#[forbid(unsafe_code)]` module. "unsupported" means exit 1 with `error:
unsupported operation: extern type field does not have a known offset`.

| Scenario | Stacked Borrows (default) | Tree Borrows | Tree Borrows, no precise interior mut | No borrow tracker |
| :--- | :--- | :--- | :--- | :--- |
| `header_ref_only` | ok, 1 warning | **unsupported, at the reference creation** | ok | ok |
| `header_tail_ref` | 1 warning, then unsupported at `&h.tail` | unsupported, at the reference creation | unsupported at `&h.tail` | unsupported at `&h.tail` |
| `header_tail_raw_no_ref` | unsupported | unsupported | unsupported | unsupported |
| `packed_tail_raw` | 1 warning, then unsupported | unsupported, at the reference creation | unsupported | unsupported |
| `transparent_tail_ref`, `zero_prefix_tail_ref` | ok, 1 warning | ok, 0 warnings | ok | ok |
| `opaque_reborrow`, `opaque_mut_reborrow` | ok, 1 warning | ok, 0 warnings | ok | ok |
| `slice_tail_control`, `dyn_tail_control` | ok | ok | ok | ok |

Mechanisms, from `src/tools/miri/src` at the first revision:

- **Stacked Borrows** (`borrow_tracker/stacked_borrows/mod.rs:824-853`,
  `sb_retag_place`): `size_and_align_of_val(place)` is `None`, and the code
  says "If we cannot determine the size (because the unsized tail is an `extern
  type`), bail out -- we cannot reasonably figure out which memory range to
  reborrow"; it emits `ExternTypeReborrow` once per process (a static
  `AtomicBool`) and returns the place with its **old** tag. The diagnostic text
  is "reborrow of a reference to `extern type` is not properly supported" with
  the help lines "`extern type` are not compatible with the Stacked Borrows
  aliasing model implemented by Miri; Miri may miss bugs in this code" and "try
  running with `MIRIFLAGS=-Zmiri-tree-borrows` …". The referenced design issue,
  `rust-lang/unsafe-code-guidelines` 276 "Stacked Borrows cannot properly
  handle `extern type`", was open on 2026-11-22.
- **Tree Borrows range** (`borrow_tracker/tree_borrows/mod.rs:444-475`,
  `tb_retag_place`): "when `extern type` is involved we use the size of the
  known prefix", implemented as
  `size_and_align_of_val(place)?.map(|(size, _)| size).unwrap_or(place.layout.size)`.
  `tb_reborrow` then does a real retag even for size 0 ("Unlike SB, we *do* a
  proper retag for size 0 if can identify the allocation. After all, the
  pointer may be lazily initialized outside this initial range") and records an
  `outside_perm` in the new tree node for everything beyond the range.
- **Tree Borrows precise walk**: with `precise_interior_mut` (default `true`,
  `bin/miri.rs`; switched off by `-Zmiri-tree-borrows-no-precise-interior-mut`)
  `tb_reborrow` calls `visit_freeze_sensitive` (`helpers.rs:444-588`). For a
  pointee that is not `Freeze`, not a union and has a single variant, its
  visitor calls `walk_value`, which projects **every** field through the
  interpreter's `project_field`
  (`compiler/rustc_const_eval/src/interpret/visitor.rs`, the
  `FieldsShape::Arbitrary` loop). A struct with an extern tail is never
  `Freeze`, so the walk reaches the tail projection and raises
  `ExternTypeField` — at the retag, i.e. where the reference is created. Stacked
  Borrows never gets that far because it bails out first. The ablation column
  confirms the attribution: without the precise walk, the reference is created
  and only the explicit `&h.tail` fails.

So "Tree Borrows handles `extern type` with zero warnings" is true for bare
extern types and offset-0 wrappers, and false, under default flags, for
references to structs whose extern tail is at a non-zero offset.

Basis: source + execution (including the ablation).

### 12. Tree Borrows permission choice for extern-tailed pointees

`NewPermission::new` (`borrow_tracker/tree_borrows/mod.rs:126-229`) computes
three permissions from the pointee type (condensed and reordered; `part` ranges
over inside-frozen, inside-`UnsafeCell` and outside):

```rust
if matches!(ref_mutability, Some(Mutability::Mut) | None if !ty_is_unpin) {
    // Mutable reference / Box to pinning type: retagging is a NOP.
    return None;
}
// Outside bytes are frozen only if the entire type is frozen.
let frozen = match part { InsideFrozen => true, InsideUnsafeCell => false, Outside => ty_is_freeze };
match ref_mutability {
    Some(Mutability::Not) => if frozen { Permission::new_frozen() } else { Permission::new_cell() },
    /* &mut and Box: new_unique / new_reserved_frz / new_reserved_im */
}
```

and `Permission::associated_access` (`tree_borrows/perms.rs:311-319`) returns
`None` for `Cell`, a write for `Unique`, a read otherwise. A pointee with an
extern tail is neither `Freeze` nor `Unpin` (finding 2; cases `b23`, `b24`,
`b34`, `b35`). Hence:

- `&mut` and `Box` retags of such a pointee are no-ops;
- a shared retag installs `Cell` both for non-frozen bytes inside the range and
  as `outside_perm`, and creating `Cell` implies no access to the parent.

A retag that knows only the prefix therefore leaves each byte — in the prefix,
in the unknown tail, and beyond — in the same state (permission and
"accessed" flag) as a retag told the true extent would, provided the foreign
bytes are given the non-frozen permission. That proviso is how the
implementation treats non-`Freeze` data it cannot look into (its imprecise mode
labels the whole range non-frozen; its `outside_perm` uses `frozen =
ty_is_freeze`). Without the `Unpin` early exit the *permissions* still agree
whenever the pointee is not `Freeze` and implicit writes are off; with
`-Zmiri-tree-borrows-implicit-writes` a protected `&mut` gets `Unique` inside
and `ReservedFrz` outside, so the agreement genuinely needs that hypothesis.

A Stacked Borrows retag, by contrast, is a function of the byte span: two
different spans grant the new tag on different byte sets, and the skip-retag
fallback differs from the retag for every non-empty span.

Basis: source + derived (Lean: `tree_borrows_extern_new_permission`,
`tree_borrows_reborrow_sound_without_pointee_size`,
`tree_borrows_lazy_permission_matches_true_extent`,
`implicit_writes_separate_inside_from_outside`,
`ce3_stacked_borrows_eager_retag_requires_byte_span`). The implicit-writes mode
was not executed.

### 13. Proposal text versus implementation

Disagreements and silences, preserved rather than resolved:

- **Status and names.** RFC pull request 3729 "Hierarchy of Sized traits"
  (created 2024-11-15, last updated 2026-10-12) was open and unmerged on
  2026-11-22; no `text/3729-*` file exists in `rust-lang/rfcs` at
  `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`. At its head commit the proposal
  introduces "new marker traits, `SizeOfVal` and `Pointee`" with
  `trait Sized: SizeOfVal {}`, `trait SizeOfVal: Pointee {}`, `trait Pointee
  {}`. The compiler at all three revisions calls them `MetaSized` and
  `PointeeSized`. There is therefore no accepted normative text for the
  hierarchy; the implementation is an unstable experiment.
- **`?Sized`.** Proposal: "`?Sized` would be made syntactic sugar for a
  `SizeOfVal` bound." Implementation: `?Sized` adds `MetaSized`. These agree up
  to the name.
- **`size_of_val`.** RFC 1861 (merged): "we must also be careful that
  `size_of_val` and `align_of_val` do not work either … For an initial
  implementation, those methods can just panic, but before this is stabilized
  there should be some trait bound or similar on them that prevents their use
  statically." The proposal's motivation calls the panic "always wrong". The
  examined compilers reject statically (finding 4).
- **Tail field offsets.** RFC 1861 sanctions storing "an extern type at the end
  of a container" and says nothing about the offset of that field. The
  proposal's section "Restrictions in compound types" states: "`Pointee` types
  can only be used as the final field in non-`#[repr(transparent)]` compound
  types as the alignment of these types would need to be known in order to
  calculate field offsets." That restriction keeps *later* fields computable
  but not the final field's own offset, which is what findings 8–10 are about;
  the proposal's prior-art section does record that an earlier `DynSized`
  attempt was "motivated by wanting to have a mechanism by which `!DynSized`
  types can be prevented from being valid in struct tails due to needing to
  know the alignment of the tail in order to calculate its field offset". The
  examined compilers accept extern tails at any offset and pin the run-time
  abort with a test.

Basis: normative (RFC 1861) + documentation (the open proposal) + source +
execution.

### 14. Anneal's trusted boundary

At `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613`:

- `trusted/lean/Trusted/MirAst.lean:312-321` defines the admitted type universe
  as `MirTy ::= bool | int | unit | never | enum | tuple | ref | rawPtr |
  unsupported`, and its documentation (lines 308–311) states that
  `.unsupported` "represents all other `TyKind` variants (`Char`, `Float`,
  non-fieldless-enum `Adt`, `Foreign`, `Str`, `Array`, `Pat`, `Slice`, `FnDef`,
  `FnPtr`, `Dynamic`, …), causing [the semantics] to fail closed with
  `FaultKind.unsupported`". `ProjectionElem` (lines 472–475) is `deref | field
  | unsupported`.
- `trusted/lean/Trusted/MirSemantics.lean` rejects every non-empty projection:
  `if !place.projection.isEmpty then .error .unsupported` in operand evaluation
  (lines 953, 962), in `.discriminant` (line 1270), and `.fault .unsupported`
  for an assignment destination (line 1407). `evalRvalue` (lines 1240–1313)
  evaluates only `.use`, `.binaryOp`, `.unaryOp` and `.discriminant`; every
  other rvalue, including the AST's `.ref` and `.addressOf`, ends in
  `.error .unsupported`. `isPrimitiveReadableTy` (lines 834–836) admits only
  `.bool` and `.int`.
- The vendored interpreter mirrors the compiler's offset-0 rule:
  `vendor/lean-miri/Miri/Interpreter/PlaceDynamic.lean:82` has `if offset !=
  Size.ZERO then throw (.unsupported "ExternTypeField")` in the `none`
  (no dynamic alignment) branch, and `Miri/Interpreter/Projection.lean:146`
  the same test with `.obligation "ExternTypeField"`. The vendored tree's
  `UPSTREAM_PIN.json` names `proofs-rs/lean-miri` commit
  `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`.

Consequences for a verifier built on this boundary (derived): no program that
reaches the abort of finding 8 is inside the admitted fragment today, since it
needs a struct ADT type, a `Foreign` type, a field projection and a reference
or raw-pointer rvalue, each of which faults as unsupported. Any extension that
admits struct tails must carry the sizedness tier of the pointee explicitly,
because (i) pointer width cannot
supply it (finding 5), (ii) field projection has a run-time failure mode that
type checking does not rule out (finding 8), and (iii) that failure is an
abort in compiled code but an "unsupported" stop in the interpreters, so a
semantics that models it must pick the compiled behaviour to be faithful to
executables.

Basis: source + derived.

### 15. The Lean model

`support/SizedHierarchyAndExternTailSoundness.lean` (1172 lines; 60 theorems,
34 definitions, 15 inductive or structure types; no imports).

Correspondence between model and source (by inspection):

| Model | Source it transcribes |
| :--- | :--- |
| `Ty` = `scalar \| slice \| dyn \| foreign \| adt pack tailOffset prefixAlign tail`; `Ty.tier` | builtin tables of finding 2; an ADT takes the tier of its tail |
| `Bound.desugar` (`?Sized ↦ metaSized`, none `↦ sized`) | `add_implicit_sizedness_bounds`, type-parameter case |
| `Ty.metaKind`, `Ty.ptrWords` | `ptr_metadata_ty_or_tail`, pointer layout (finding 5) |
| `Ty.sizeAlign` | `size_and_align_from_meta` (finding 6), including the pack cap |
| `sizeOfValRuntime` | `size_and_align_of_dst`: `none ↦ panicNounwind` |
| `codegenProjectTail`, `interpProjectTail` | the two `project_field` case splits (finding 8) |
| `tailOffset off pack a = alignUp off (capAlign pack a)` | "bump the unaligned offset up to the appropriate alignment", with `alignUp` the mathematical round-up |
| `permOfPart`, `newPermission`, `Perm.associatedAccess` | `NewPermission::new`, `associated_access` (finding 12) |
| `tbReborrowSize`, `tbRetagState` | `tb_retag_place` range and the inside / outside split of `tb_reborrow` |
| `sbRetag` | `sb_retag_place`: no size ↦ skipped with a warning |
| `tbRetagHeaderOutcome` | precise walk reaching the tail projection (finding 11) |

Principal statements (verbatim signatures):

```lean
theorem metaSized_implies_total_runtime_layout (ty : Ty) (m : Meta)
    (hTier : Implements ty .metaSized) (hMeta : MetaFor ty m) :
    ∃ sa, ty.sizeAlign m = some sa

theorem runtime_layout_total_iff_metaSized (ty : Ty) :
    (∀ m, MetaFor ty m → ∃ sa, ty.sizeAlign m = some sa) ↔ Implements ty .metaSized

theorem extern_tail_offset_static_iff (off : Nat) (pack : Option Nat)
    (hpack : ∀ p, pack = some p → IsPow2 p) :
    OffsetStatic off pack ↔ (off = 0 ∨ ∃ p, pack = some p ∧ off % p = 0)

theorem extern_tail_offset_static_iff_zero_prefix_or_packed1_specialization
    (off : Nat) (pack : Option Nat) (hrepr : pack = none ∨ pack = some 1) :
    OffsetStatic off pack ↔ (off = 0 ∨ pack = some 1)

theorem tree_borrows_reborrow_sound_without_pointee_size
    (kind : RefKind) (c : RetagCtx) (np : NewPermission)
    (hFreeze : c.tyIsFreeze = false) (hUnpin : c.tyIsUnpin = false)
    (hnp : newPermission kind c = some np)
    (frozenAt : Nat → Bool) (knownPrefix trueSize : Nat) (hsize : knownPrefix ≤ trueSize)
    (i : Nat) :
    tbRetagState np frozenAt knownPrefix (tbReborrowSize none knownPrefix) i
      = tbRetagState np frozenAt knownPrefix trueSize i
```

Counterexamples:

- `ce1_question_sized_as_pointee_sized_panics_size_of_val`: if `?Sized` imposed
  no sizedness obligation, an `extern type` and any struct ending in one would
  satisfy the bound of `size_of_val` with well-typed metadata and the compiled
  call would be the non-unwinding panic.
- `ce2_nonzero_prefix_extern_tail_requires_unknown_align`:
  `tailOffset 6 none 2 = 6`, `tailOffset 6 none 4 = 8`,
  `tailOffset 6 none 16 = 16`; the offset is not static and no single value is
  correct for all admissible alignments.
- `ce3_stacked_borrows_eager_retag_requires_byte_span`: for spans `n < n'` the
  new tag is absent at byte `n` under span `n` and present under `n'`; no
  span-oblivious grant function matches all spans; the skip fallback differs
  from the retag at byte 0 for every non-empty span.

Other proved facts used above: the supertrait edges and their strictness; thin
pointer iff not strictly-`MetaSized`
(`thin_pointer_iff_not_strictly_metaSized`); `size_of_val` total under the
`?Sized` lowering; `stacked_borrows_skips_non_metaSized_pointee`;
`precise_tree_borrows_header_retag_unsupported_iff_nonzero_offset`.

Check performed (`support/verify_lean.sh`, output in
`support/lean_verification_output.txt`): a token scan of the source for
`sorry`, `admit`, `native_decide`, `bv_decide`, `omega`, `partial def`,
`unsafe`, `Classical.`, `axiom`, `implemented_by`, `deriving`, `import`,
`opaque`, `_unsafe_rec` (all counts 0); elaboration and kernel check with
`-DwarningAsError=true -Ddebug.skipKernelTC=false -DElab.async=false` (exit 0);
then `support/AxiomAudit.lean`, which walks all 477 constants the module adds
to the environment (144 theorem constants including generated equation lemmas,
262 definitions, 15 inductive types) and reports the union of axioms used as
`[propext]`, with 0 declared axioms, 0 opaque constants, 0 unsafe, 0 partial
and 0 `_unsafe_rec` names. Recursive functions over `Ty` are structural and
`noncomputable`; no instance is derived for `Ty`. One library lemma about
powers of two (`Nat.pow_le_pow_iff_right`) depends on the axiom of choice in
this Lean version and was replaced by a direct proof (`le_of_two_pow_le`).

Basis: derived (machine-checked for the model; the model-to-source link is the
table above).

## Boundaries

**Not examined.**

- Targets other than `x86_64-unknown-linux-gnu`; the 8 / 16-byte widths and the
  concrete offsets are for that target.
- The Cranelift and GCC code generators. `compiler/rustc_codegen_cranelift/src/unsize.rs:209`
  contains the same message text at the first revision, but nothing was run
  with it; the upstream UI test carried `//@ ignore-backends: gcc` at the first
  revision.
- Execution on `rustc 1.102.0-nightly` or on the default-branch head. The
  preserved earlier record for 1.102.0-nightly comes from a smaller predecessor
  probe whose inputs were not kept.
- Compile-time evaluation of the projection in `const` contexts, link-time
  optimisation, and optimisation levels other than 0 and 3.
- `size_of_val_raw`, `align_of_val_raw`, `Layout::for_value`, `Rc`, `Arc`, and
  drop glue for extern-tailed types.
- Miri's `-Zmiri-tree-borrows-implicit-writes` mode (modelled, not executed) and
  any multi-threaded scenario.
- Whether the content of Anneal's vendored `lean-miri` tree equals the upstream
  commit its pin file names.

**Unknown.**

- Whether upstream intends to reject the non-zero-offset projection
  statically, to add a `packed`-aware static path, or to keep the run-time
  abort. Neither RFC text decides it and no decision was found in the examined
  sources.
- Whether `rust-lang/rfcs` pull request 3729 will be accepted, and under which
  trait names.

**Known not to apply.**

- The abort is not undefined behaviour and not a memory-safety violation: it is
  a non-unwinding panic. Reaching it still requires `unsafe` (or foreign code)
  somewhere to produce a reference to the extern-tailed struct.
- Miri's "unsupported operation" is not a report of undefined behaviour.
- "Zero warnings under Tree Borrows" does not extend, with default flags, to
  references to structs whose extern tail is at a non-zero offset.
- `packed(1)` does not make the projection work in the examined compilers, even
  though the offset is then statically determined.
- The static rejection of `size_of_val` does not extend to field projection.

**Unsupported (by the tools themselves).**

- Stacked Borrows with `extern type` pointees: Miri says so in its diagnostic
  and skips the retag.
- Anneal's trusted MIR semantics for `Foreign`, slice, `str`, `dyn` and struct
  ADT types and for any place projection: `FaultKind.unsupported`.
- `unsized_tuple_coercion`: removed feature.

**Stronger conclusions the evidence does not establish.**

- That Tree Borrows is sound for extern types in any absolute sense. The
  theorem shows agreement between a prefix-only retag and a true-extent retag
  inside a model, under the stated treatment of foreign bytes.
- That the Lean model equals the compiler. It transcribes specific case splits;
  layout computation, the trait solver, and Miri's tree updates are not
  modelled.
- That later nightlies behave as executed here; only source continuity was
  checked for them.
- That the offsets 6, 8 and 16 are what any particular foreign type would get;
  they illustrate the dependence on an alignment the compiler does not have.

## Evidence

All evidence was acquired on 2026-11-22 except the preserved earlier record
(2026-11-21). Every revision below was resolved through the GitHub REST API
(`repos/<owner>/<repo>/commits/<ref>`, `…/pulls/<n>`, `…/issues/<n>`) on
2026-11-22; `support/resolved_revisions.json` holds the responses' identifying
fields.

**`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`** (line
numbers; `support/source_region_continuity.json` gives the ranges at the other
two revisions):

| Path | Lines | Content |
| :--- | :--- | :--- |
| `library/core/src/marker.rs` | 145–192 | `Sized`, `MetaSized`, `PointeeSized` |
| `library/core/src/mem/mod.rs` | 401–404, 548–551 | `size_of_val`, `align_of_val` with `T: ?Sized` |
| `library/core/src/ptr/metadata.rs` | 59, 85 | `Pointee: PointeeSized`, `Thin` |
| `compiler/rustc_hir_analysis/src/hir_ty_lowering/bounds.rs` | 162–235 | `add_implicit_sizedness_bounds` |
| `compiler/rustc_hir_analysis/src/hir_ty_lowering/mod.rs` | 971–982 | `PointeeSized` bounds not represented |
| `compiler/rustc_middle/src/ty/sty.rs` | 1758–1759, 1929–1974 | metadata of `Foreign`; `has_trivial_sizedness` |
| `compiler/rustc_ty_utils/src/ty.rs` | 20–79 | `sizedness_constraint_for_ty` |
| `compiler/rustc_ty_utils/src/layout.rs` | 467–472, 515–519 | thin pointer to `Foreign` tail; `Foreign` layout |
| `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs` | 109–110, 774–785, 1240–1307 | lowering invariant; auto traits; builtin sizedness |
| `compiler/rustc_codegen_ssa/src/size_of_val.rs` | 15–184 (`Foreign` arm 57–89) | `size_and_align_of_dst` |
| `compiler/rustc_codegen_ssa/src/mir/place.rs` | 166–248 | `PlaceRef::project_field` |
| `compiler/rustc_const_eval/src/interpret/projection.rs` | 150–201 | interpreter `project_field` |
| `compiler/rustc_const_eval/src/interpret/eval_context.rs` | 432–518 | `size_and_align_from_meta` |
| `compiler/rustc_const_eval/src/interpret/visitor.rs` | 78–209 | `walk_value` |
| `compiler/rustc_const_eval/src/util/alignment.rs` | 9–51 | `place_unalignment` |
| `compiler/rustc_middle/src/mir/interpret/error.rs` | 717 | `ExternTypeField` message |
| `compiler/rustc_feature/src/removed.rs` | 296–297 | `unsized_tuple_coercion` |
| `src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs` | 824–853 | `sb_retag_place` |
| `src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs` | 126–229, 238–442, 444–475 | `NewPermission::new`, `tb_reborrow`, `tb_retag_place` |
| `src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs` | 311–319 | `associated_access` |
| `src/tools/miri/src/helpers.rs` | 444–588 | `visit_freeze_sensitive` |
| `src/tools/miri/src/diagnostics.rs` | 700, 810–825 | `ExternTypeReborrow` text |
| `tests/ui/extern/extern-types-field-offset.rs`, `.run.stderr` | whole files | `run-crash` test |
| `tests/ui/extern/extern-types-size_of_val.rs`, `.stderr` | whole files | static rejection test |
| `src/tools/miri/tests/pass/extern_types.rs`, `tests/fail/extern-type-field-offset.rs` | whole files | Miri tests |

Spot check of local-versus-upstream identity: the toolchain's bundled
`library/core/src/marker.rs` and
`compiler/rustc_const_eval/src/interpret/projection.rs` match the files fetched
at the pinned upstream revision bit-for-bit.

**Other primary sources.**

- `rust-lang/rust` pull requests 137944 (merge commit
  `86d0aef80403f095d8bbabf44d9fdecfcd45f076`) and 137728 (merge commit
  `257b4947ed14795a8411df53b6cf6d5a57b56240`); issues 144404 and 43467
  ("Tracking issue for RFC 1861: Extern types"), both open.
- `rust-lang/rfcs` at `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`,
  `text/1861-extern-types.md`, lines 62–68 and 84–85.
- `rust-lang/rfcs` pull request 3729 at head
  `1bb22f00880cb6d24192af4041585683b56e9b3a` (2026-03-18),
  `text/3729-sized-hierarchy.md`, lines 93–121, 206–244, 430–451,
  601–630, 1790–1793.
- `rust-lang/unsafe-code-guidelines` issue 276 (title and state only).
- `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:
  `trusted/lean/Trusted/MirAst.lean` lines 296–321, 472–475;
  `trusted/lean/Trusted/MirSemantics.lean` lines 834–836, 949–966, 1240–1313,
  1406–1408; `vendor/lean-miri/Miri/Interpreter/PlaceDynamic.lean` lines 68–85;
  `vendor/lean-miri/Miri/Interpreter/Projection.lean` lines 132–148;
  `vendor/lean-miri/UPSTREAM_PIN.json`.

**Execution environment.** `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, host
`x86_64-unknown-linux-gnu`, LLVM 22.1.6; Miri from the same toolchain, invoked
as the `miri` driver with the sysroot printed by `cargo miri setup
--print-sysroot`; Python 3.13.15; Lean 4 v4.34.1
(`5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`).

**Preserved material** (directory `support/`):

- `probe_sized_hierarchy_and_extern_types.py` — the probe; all Rust inputs are
  embedded in it. Part A1: one program (tier witnesses, pointer widths, dynamic
  sizes, offset-0 projections, reborrow). Part A2: ten scenarios, native as two
  crates at two optimisation levels and under four Miri modes, plus MIR and
  LLVM IR capture. Part B: 35 compile-only cases. The script compares fresh
  observations to pins and reports mismatches; it never substitutes a pin for
  an observation.
- `probe_results_rustc_1_98_0_nightly_2026_05_31.json` — its output, with 0 pin
  mismatches, recording the SHA-256 of the script that produced it.
- `prior_run_record_rustc_1_102_0_nightly_2026_11_11.json` — the earlier
  output-only record (see `support/README.md` for its provenance and the two
  edits made to it). It shows, on that toolchain: a 7-tuple of pointer widths
  containing only 8 and 16; the `(size, align)` pairs `(8, 2)` and `(4, 4)`
  under labels naming a `u16` tail of length 3 and a `u32` tail of length 0; a
  Stacked Borrows
  warning and no Tree Borrows warning for an `&OpaqueExtern` reborrow; a native
  SIGABRT with the same message for a safe tail projection; the Miri "unknown
  offset" error under Tree Borrows at the reference creation; `E0277` naming
  `MetaSized` for `size_of_val`, a `?Sized` generic and a `MetaSized` bound on
  a header; and `E0557` for the removed feature.
- `SizedHierarchyAndExternTailSoundness.lean`, `AxiomAudit.lean`,
  `verify_lean.sh`, `lean_verification_output.txt`.
- `compare_source_regions.py`, `source_region_continuity.json`.
- `resolved_revisions.json`.

**Synthesis versus source facts.** The tier table, the correspondence table,
the statement that the later-revision diffs are refactorings, the attribution
of the Tree Borrows failure to the precise walk (source reading confirmed by
the ablation run), and everything in finding 14's last paragraph are this
report's synthesis. Quoted code, comments, diagnostics and test contents are
source facts at the stated revisions.

## Revalidation

Cheapest discriminating checks, in order of cost:

1. **Has the tail-projection behaviour changed?** Read the upstream test pair
   `tests/ui/extern/extern-types-field-offset.rs` and `.run.stderr` at the
   revision of interest. While the test says `//@ run-crash` and the expected
   stderr contains "attempted to compute the size or alignment of extern
   type", finding 8 holds. If it became a compile-fail test, the static hole
   was closed; if it became `run-pass`, an offset path was added.
2. **Has a `packed` fast path appeared?** In `PlaceRef::project_field`
   (`compiler/rustc_codegen_ssa/src/mir/place.rs`) and the interpreter's
   `project_field` (`compiler/rustc_const_eval/src/interpret/projection.rs`),
   check whether anything other than "sized", "slice or `str`" and "offset 0"
   returns before the dynamic alignment is requested. Finding 10's gap
   statement depends only on that.
3. **Has the lowering changed?** Search
   `compiler/rustc_hir_analysis/src/hir_ty_lowering/bounds.rs` for "`?Sized` is
   equivalent to `MetaSized`", and `library/core/src/marker.rs` for the three
   `pub trait` lines. A rename to the proposal's `SizeOfVal` / `Pointee` would
   show here first.
4. **Re-run the probe** on any nightly with the `miri` component:

   ```sh
   cargo +<toolchain> miri setup
   python3 support/probe_sized_hierarchy_and_extern_types.py \
       --toolchain <toolchain> --out fresh.json --check
   ```

   Exit 0 with `pin mismatches: 0` re-establishes findings 2–9 and 11 for that
   toolchain on the host target. A mismatch is printed as
   `MISMATCH: <part>[<case>] …` and names exactly which observation moved.
   `--no-miri` restricts the run to `rustc`. The probe checks classes of
   outcome (exit status, error codes, key message substrings, presence of the
   `panic_nounwind` call in the IR), not full diagnostics text.
5. **Re-check source continuity** for other revisions:

   ```sh
   python3 support/compare_source_regions.py --out regions.json \
       14210df0e27ccd7d9e6a05b8085cbd438e4bbc65 <other-revision>
   ```

   A region reported as identical needs no further reading; a changed region
   must be diffed by hand, and `anchor_not_found` means the item moved or was
   renamed.
6. **Re-check the Lean model** with Lean 4 v4.34.1:

   ```sh
   LEAN=/path/to/lean support/verify_lean.sh
   ```

   This establishes only that the model's theorems are kernel-checked without
   disallowed axioms. If any transcribed case split changes upstream (checks 2
   and 3, or `NewPermission::new` in Miri), the corresponding definition in the
   model must be updated before its theorems say anything about the new
   compiler.
7. **Anneal.** Finding 14 holds for a later Anneal revision as long as
   `MirTy` in `trusted/lean/Trusted/MirAst.lean` has no struct, slice, `dyn` or
   foreign constructor and `Trusted/MirSemantics.lean` still tests
   `place.projection.isEmpty` before evaluating a place. Once either changes,
   the three consequences listed there become obligations on the extended
   semantics rather than vacuous facts.

No cheap check covers other targets or other code generators; those require
repeating the probe there.
