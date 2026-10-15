# Lowering audit before adding memory-safety claims

This audit records what the pinned extraction retains, forgets, and rejects.
It answers a specific question: could a proof of the generated function omit a
Rust operation that matters to a proposed bit-validity or memory-safety claim?
Yes. Successful extraction and a kernel-checked proof are insufficient unless
the translation preserves the observations needed by that claim.

The current integration proves conditional functional contracts under the
correspondence premises in [SEMANTICS.md](SEMANTICS.md). It does not yet implement
a runtime storage semantics or establish general Rust UB-freedom.
The pure byte representation model described below supplies initialization laws;
it does not add storage events to extracted executions.
[ADMISSION_DESIGN.md](ADMISSION_DESIGN.md) describes the implemented admission
checks on the preserved pre-transformation snapshot and final LLBC, as well as
the additional requirements for future storage and handler models. Those checks
restrict which executions we admit; they do not prove the translator premises
recorded in this audit.

## Scope and evidence

The audit used the revisions selected by `anneal/flake.lock` on 2026-10-08:

- Aeneas: `ca282ec2312a96f6a985a4d23a663690816d3f3e`.
- Charon: `cf02e3f228f97ee7be3a415be56989053063326d`.

The fetched Aeneas archive's SHA-256 matched the installed build's recorded
source SHA-256. The local Aeneas patch exposes the tuple-newtype option; it does
not change the effect handling examined here. A separate Charon patch saves the
imported AST before transformation and refuses optimized-MIR fallback for local
bodies during admission. The driver uses Charon's Aeneas
preset, `--sysroot default`, and strict error handling. It does not enable
precise/desugared drops or Aeneas's `-feature-gates` option.

The enumeration below covers every constructor of the pinned LLBC statement
and rvalue languages and lists their auxiliary operation forms. The audit also
examined the MIR importer, the transformation pass lists, the relevant erasing
handlers, builtin replacement policy, and selected effect-removing optimizations.
It is not a proof of every pass, builtin, rustc transformation, or supported
combination of constructs. No end-to-end counterexample was executed. Statements
about ignored operations are findings from the pinned source; their consequences
for future memory claims are deductions from those findings.

## Confirmed boundaries

1. **Typed transfers do not retain a storage event.** Copying and moving operate
   on logical values. Aeneas tracks moves, uninitialized logical values, and
   loans internally, but the pure output does not retain byte initialization,
   padding, or provenance. A carrier that treats `MaybeUninit<T>` as an exact
   byte sequence could therefore promise more than the lowering preserves.
   [Issue #1405](https://github.com/AeneasVerif/aeneas/issues/1405) tracks typed
   copies. A restricted storage abstraction can forget all padding contents and
   initialization facts, provided supported operations cannot recover them.
   Arguments and write-access obligations still need evaluation; forgetting a
   padding write does not excuse an invalid access. See [operand evaluation] and
   [type translation].
2. **Residual destructors are ignored by default.** The statement interpreter
   treats `Drop` as a no-op. `-eval-drops` instead invalidates the logical value
   and processes loans; it does not execute the supplied destructor body.
   Charon can make destruction explicit with precise drops and calls to drop
   glue, but the current preset does not enable that path. Any safety extension
   must account for destruction, including generic and unwind destruction, or
   exclude it. Merely turning on `-eval-drops` would not solve this problem. See
   [statement interpretation], [drop configuration], and [Charon options].
3. **Place validity can be omitted.** Charon documents that `PlaceMention` can
   cause UB when its projections are invalid. Aeneas explicitly handles it as a
   no-op. Other operations may already enforce the necessary conditions for a
   particular program, but that needs an argument; this handler does not provide
   one. See [statement syntax] and [statement interpretation].
4. **Some implicit call preconditions are optional.** Aeneas has a pass that
   inserts assertions for `#[target_feature]`, but its flag defaults to false
   and our driver does not enable it. Rust can require the enabled CPU features
   even when the function body otherwise looks harmless. Such functions need
   feature admission or rejection before a safety claim. See [feature gates]
   and [Rust target-feature rules].
5. **Generated failure kinds lose distinctions.** Charon distinguishes panic,
   UB, and unwind termination. The interpreter turns every `Abort` into the
   same symbolic panic node and ignores the failure kind on `Assert`. It also
   ignores `on_unwind` blocks when interpreting calls and assertions. Today's
   total and partial contracts reject these failures, so this collapse alone
   does not make those branches acceptable. Future panic-tolerant rules must
   not assume every generated failure represents a recoverable Rust panic.
   Our handwritten `.undef` primitives preserve their own failure tags; they
   do not repair tags or effects lost earlier. See [statement interpretation].
6. **Addresses and allocation effects are abstracted away.** References lower
   to their referent types and `Box<T>` lowers to `T`; `Box::new` is eliminated.
   Charon's preset also hides allocator parameters. Borrow reasoning remains
   part of symbolic execution, but the output does not by itself describe
   address alignment, allocation identity, resource lifetime, retagging, or
   allocator effects. These are deliberate value abstractions, not automatic
   memory-safety theorems. See [type translation], [box elimination], and
   [Charon options].
7. **Typed values already assume a representation domain.** Lean `Bool` cannot
   contain an invalid Rust boolean, and an enum constructor does not contain an
   invalid physical discriminant. Field records omit padding and niche layout.
   Producing such values from storage must be checked before entering that
   domain. A type decoder used by an ordinary contract cannot retroactively
   expose a UB-producing operation erased by translation. Charon's logical
   enum discriminants are explicitly distinct from physical stored tags. See
   [expression syntax] and [type translation].
8. **Earlier normalization remains trusted.** Charon requests promoted MIR for
   local functions by default, but can fall back to optimized MIR when that
   body is unavailable. Its pinned driver already sets MIR optimization level 0,
   `mir_preserve_ub`, and `always_encode_mir` for both selected crates and
   dependencies compiled through its wrapper. The `optimized_mir` query name
   alone therefore does not establish that optional optimizations ran.
   Precompiled dependency/sysroot bodies need their own build-origin evidence
   or an explicit external interpretation. The driver also disables
   `CheckAlignment` and `CheckNull`; preserving an operation does not supply
   all of its safety guards. Charon additionally reconstructs arithmetic checks,
   indexing, boxes, matches, and control flow.
   A downstream primitive cannot restore an effect that disappeared at an
   earlier stage. Source-to-model correspondence therefore remains a premise;
   checking final LLBC alone cannot establish it. See [MIR configuration],
   [MIR selection], and [Charon transformations].

These are limitations on stronger claims, not evidence that the current
numerical propositions are false. Conversely, they apply inside annotated
functions too: finding every annotation does not establish that every relevant
operation in its dependency closure was faithfully modeled.

## Pure byte representations and `IntoBytes` laws

[`Rust.Storage`](../../anneal/lean/Rust/Storage.lean) represents initialized and
uninitialized bytes and fixed-width physical decoders as pure values.
`BitDecoder.Initialized` says that every byte list accepted by a decoder is
initialized. `RustModel.initializedRepresentation` requires an available
physical decoder and this law; absence is `False`. The library's mathematical
`decode` cannot restrict that quantification. A decoder rejecting every byte
list satisfies initialization vacuously, so its law alone does not establish
correspondence with Rust.

The physical correspondence premise has three parts: decoder width equals the
Rust representation width for the selected type and metadata; every
language-valid representation is admitted with the corresponding raw value;
and every admitted representation denotes a language-valid value. Neither
`BitDecoder` nor a proof of initialization establishes those parts. The
following laws are conditional on those representation premises and the
translation premises already recorded in [SEMANTICS.md](SEMANTICS.md).

### Exact authored implementation scope

The default-feature library extraction has 59 nameless `invariant_proof`
markers, each attached through invocation arguments to one native positive
`IntoBytes` impl. This count inventories authored claims; the native binding
manifest and checked implementation-law witnesses establish which compiled
owners fulfill them.

| Family | Exact Rust carriers and bounds | Count |
| --- | --- | --- |
| Primitive | `()`, `bool`, `char` | 3 |
| Integer | `u8`, `u16`, `u32`, `u64`, `u128`, `usize`, `i8`, `i16`, `i32`, `i64`, `i128`, `isize` | 12 |
| Nonzero | `NonZeroU8`, `NonZeroU16`, `NonZeroU32`, `NonZeroU64`, `NonZeroU128`, `NonZeroUsize`, `NonZeroI8`, `NonZeroI16`, `NonZeroI32`, `NonZeroI64`, `NonZeroI128`, `NonZeroIsize` | 12 |
| Niche option | `Option<N>` for each of the preceding 12 nonzero carriers | 12 |
| Empty marker | `PhantomData<T>` for `T: ?Sized`, without `T: IntoBytes` | 1 |
| Array | `[T; N]` for `T: IntoBytes`, every `const N: usize` | 1 |
| Sized wrapper | `Wrapping<T>`, `Unalign<T>` for `T: IntoBytes` | 2 |
| Possibly unsized wrapper | `ManuallyDrop<T>`, `Cell<T>`, `UnsafeCell<T>`, `ReadOnly<T>` for `T: ?Sized + IntoBytes` | 4 |
| Byteorder | `U16<O>`, `U32<O>`, `U64<O>`, `U128<O>`, `Usize<O>`, `I16<O>`, `I32<O>`, `I64<O>`, `I128<O>`, `Isize<O>`, `F32<O>`, `F64<O>` for every `O`, without `O: ByteOrder` | 12 |

The source locations are [`impls.rs`](../../zerocopy/src/impls.rs),
[`wrappers.rs`](../../zerocopy/src/wrappers.rs), and
[`byteorder.rs`](../../zerocopy/src/byteorder.rs). The `unsafe_impl!` grouped arm
accepts attributes before each trait; shared proof attributes would duplicate a
source fence and fail unique-owner binding. Single generic calls use leading
attributes. `impl_for_transmute_from!` forwards attributes to its single impl.
`impl_or_verify!` forwards them only to the handwritten implementation.

`Unalign` and byteorder select that handwritten branch only with neither
`feature = "derive"` nor `cfg(test)`. Their derive/test branches verify separate
derive-generated implementations; these are outside this extraction claim.
Byteorder markers are concrete invocation arguments, not a fence duplicated by
`define_type!`. `F32` and `F64` store `[u8; 4]` and `[u8; 8]`; their laws depend
on those byte arrays, not native floating-point bit semantics.

Deferred implementations are `[T]`, `str`, native `f32`/`f64` and feature-gated
`f16`/`f128`, atomics under their target/version cfgs, SIMD under its
feature/target/version cfgs, procedural derives, and the generated struct/union
impls of `cryptocorrosion_derive_traits!`. These remain ordinary Rust impls;
this inventory makes no initialization-law certification for them. Neither
core nor zerocopy `MaybeUninit`, non-unit tuples, raw pointers, references,
`NonNull`, nor arbitrary `Option<T>` has an `IntoBytes` impl in this snapshot.
Incoming downstream dictionaries still require their own conditional law
premises; these 59 local markers do not certify future external implementations.

### Decoder correspondence premises

Admission currently requires one little-endian 64-bit target, as checked in
[`admission.py`](admission.py). The word decoders use that byte order and an
eight-byte `usize`/`isize`; this is an enforced extraction restriction, not a
Rust guarantee for every target. Integer assembly preserves the full unsigned
word and interprets signed values in two's complement. Every fixed-width word
first requires exactly its width of initialized bytes.

The following versioned references identify the concrete propositions consumed
by decoder correspondence. Their applicability to the selected compiler and
standard library is an explicit semantic compatibility premise, not a
kernel-checked Rust theorem or an all-release soundness claim. These exact
semantic compatibility propositions are admitted trust premises. Compiler or
standard-library pin changes require review of these propositions and mappings.
The current standard-library documentation reviewed for these mappings reports
Rust 1.99.0 (`b940084d7`, 2026-09-28); archived 1.81/1.85 links also remain in the
adjacent Rust safety comments. Versioned archive URLs were unavailable to the
documentation checker during this update, so that archive verification is not
claimed as new evidence.

| Decoder | Required language/stdlib proposition and resulting interpretation |
| --- | --- |
| Integers | [Rust 1.81 numeric validity](https://doc.rust-lang.org/1.81.0/reference/types/numeric.html#bit-validity) equates a numeric type's bit validity with its same-size `u8` array; uninitialized `u8` is invalid. Its signed integer definition uses two's complement. The [primitive layout table](https://doc.rust-lang.org/1.81.0/reference/type-layout.html#primitive-data-layout) fixes 1/2/4/8/16-byte integer widths; the target premise fixes pointer-sized words. |
| `bool` | [Rust 1.81 boolean rules](https://doc.rust-lang.org/1.81.0/reference/types/boolean.html) give one-byte layout and the encodings zero/one. The decoder rejects every other byte and every uninitialized byte. |
| `char` | [Rust 1.81 textual rules](https://doc.rust-lang.org/1.81.0/reference/types/textual.html) describe a 32-bit unsigned word representing a Unicode scalar value. Four initialized bytes are decoded; values above `0x10ffff` or in `0xd800..=0xdfff` are rejected. |
| Nonzero integers | [Rust 1.99 `NonZero` layout](https://doc.rust-lang.org/1.99.0/std/num/struct.NonZero.html#layout) preserves the underlying layout and validity except for the all-zero pattern. `filterMap` rejects zero as decoder failure; it never converts failure into an admitted optional payload. |
| `Option<NonZero<_>>` | The same `NonZero` layout contract gives ABI compatibility with the underlying integer. [Rust 1.99 `Option` representation](https://doc.rust-lang.org/1.99.0/std/option/index.html#representation) additionally guarantees the all-zero `None` representation and preserves valid `Some` payloads. The niche mapping decodes the full integer domain: zero becomes the Rust payload `None`, nonzero becomes `Some`; uninitialized storage still fails outer decoding. No generic `Option<T>` layout is inferred. |
| `()` and `PhantomData<T>` | [Rust 1.81 unit layout](https://doc.rust-lang.org/1.81.0/reference/type-layout.html#tuple-layout) has size zero. [Rust 1.99 `PhantomData` layout](https://doc.rust-lang.org/1.99.0/std/marker/struct.PhantomData.html#layout) guarantees size zero for every `T`; its public fieldless constructor stores no `T`. Each decoder supplies its explicit raw constructor, without fabricating a `T` or requiring `RustModel T`. |
| `[T; N]` | [Rust 1.81 array layout](https://doc.rust-lang.org/1.81.0/reference/type-layout.html#array-layout) gives total size `N * size_of::<T>()` and element offset `k * size_of::<T>()`. [Validity rules](https://doc.rust-lang.org/1.81.0/reference/behavior-considered-undefined.html#invalid-values) require valid elements. Consecutive complete element chunks cover all storage; padding within each chunk remains the element law's obligation. |
| Standard wrappers | [Rust 1.99 `Wrapping`](https://doc.rust-lang.org/1.99.0/std/num/struct.Wrapping.html#layout) preserves inner layout and ABI; its public single field stores `T`. [`ManuallyDrop`](https://doc.rust-lang.org/1.99.0/std/mem/struct.ManuallyDrop.html) preserves layout and bit validity. [`Cell`](https://doc.rust-lang.org/1.99.0/std/cell/struct.Cell.html#memory-layout) and [`UnsafeCell`](https://doc.rust-lang.org/1.99.0/std/cell/struct.UnsafeCell.html#memory-layout) preserve the inner in-memory representation. Map the actual inner decoder, including its failures; these premises do not certify interior mutation, aliasing, or destruction. |
| Local wrappers | Source `repr(transparent)` on `ReadOnly`/byteorder and `repr(C, packed)` on `Unalign`, with the [Rust 1.81 representation rules](https://doc.rust-lang.org/1.81.0/reference/type-layout.html#representations), justify retaining their complete field storage. `Unalign` removes outer alignment padding; it cannot remove padding within `T`. Byteorder's array and empty marker occupy all its storage. |

The generic wrapper laws retain the original `?Sized` bounds. A physical
interpretation for a particular unsized value must retain the relevant metadata
and representation width in its supplied provider. These conditional laws do
not install a universal DST decoder or certify arbitrary slices, strings, or
trait objects. A missing child representation remains unavailable through its
wrapper; an available child decoder must carry its actual correspondence and
initialization premise.

### Zero construction and construction-trait laws

`FromBytes` and `FromZeros` consume the same decoder-correspondence premises
above. Their additional mathematical decoding condition records library
validity, rather than treating bit validity as sufficient for every invariant.
The selected nine impl proofs cover unit, u8, u32, Boolean zero construction,
and generic arrays. They do not certify the other construction-trait impls.

The `core::mem::zeroed` interpretation uses the selected provider's physical
width, all initialized zero bytes, and that provider's mathematical decoder.
Applying it to Rust additionally assumes the selected physical interpretation
has the actual Rust width and represents the resulting Rust value. The existing
primitive and array premises supply that connection for the concrete proofs;
compiler assertions challenge unit, Boolean, byte, u32, and representative array
widths. A successful construction does not assert that initialized padding
survives a typed move. The current resource-free scope adds no claim about
provenance, ownership, destruction, or external-state constructor permission.

A checked semantic provider suffix extends generic native definitions that use
this boundary. It does not replace their extracted computation or Rust input
prefix. Both the native call audit and the independently written outcome family
retain that provider before choosing an outcome. The exact enclosing trait
bound, if Charon removes it from a default body's computational arguments, is
recovered as a specification premise from original trait/method ownership.
Required pointer-based validators are signature-only dictionary fields: their
whole Lean stubs return undef, and admission rejects every execution of them.
Their opaque Ptr carrier is an audited type constructor, not a value, spatial
model, or proof axiom about pointers.

### Empty construction and external invariants

Size zero does not imply that a value exists, that a Rust constructor may be
called, or that a library invariant holds. `emptyDecoder` requires an explicit
raw value; there is no blanket physical model inferred from size, a fieldless
extracted shape, or Lean `Inhabited`. A fieldless Rust token can carry a
constructor obligation about external state even when its physical bytes are
empty. That obligation needs an explicit state model or a retained caller
premise. A bit-valid raw constructor does not discharge it.

[`EmptyConstructionTests.lean`](lean/EmptyConstructionTests.lean) checks an
uninhabited raw carrier with no representation model, an inhabited carrier
without one, and an explicit empty physical decoder with an external-state
condition in its library provider. Physical construction of the latter succeeds
in both states; full `decodeBytesResult` rejects the absent-state case as
`.fail .undef`. Both total and partial correctness reject that result even with
postcondition `True`. `PhantomData<Empty>` succeeds using its actual empty
constructor, with no value or model of `Empty`. These are tests of modeled
admission, not executions of invalid Rust and not a proof of an external token's
safe constructor.

The array theorem partitions storage by element count, requires an empty final
remainder, and derives initialization for every count from the element law.
The same rule handles empty arrays, zero-byte elements, and nested arrays.
Each marker requests its exact native impl independently of caller roots.
Both retained AST stages and the implementation-law audit preserve the full
trait, type/const parameters, carrier application, and dictionary bounds;
checked ordinary Lean witnesses cannot specialize or add premises.

These laws establish modeled initialization conditional on correspondence.
They do not prove every `IntoBytes` method body, runtime storage transitions,
`as_bytes` pointer formation, aliasing, provenance, synchronization, destruction,
or general Rust UB-freedom. The typed-transfer and value-production boundaries
above continue to apply.

## Complete LLBC operation inventory

“Logical” below means the value-and-borrow interpretation. It does not mean
that abstract bytes, physical layout, or all Rust safety conditions are modeled.
“Rejected” means that a surviving unsupported form reaches an error in the
examined handler; strict driver error handling must remain enabled.

All 18 `StatementKind` constructors appear in this table. See [statement syntax]
and [statement interpretation].

| Statement | Disposition relevant to this audit |
| --- | --- |
| `Assign` | Evaluates a logical rvalue and updates a logical place; no general byte-validity production check. |
| `SetDiscriminant` | Updates a logical ADT, not a stored tag or niche encoding. |
| `StorageLive` | Removed in preprocessing or treated as a no-op; no storage allocation event. |
| `StorageDead` | Some removed in preprocessing; remaining ones invalidate a logical value and process loans. |
| `PlaceMention` | Ignored; projection-validity checks need separate justification. |
| `Borrowck` | Removed with compiler-only borrow information. This does not model runtime retagging. |
| `Drop` | Ignored by default; alternative flag handles logical invalidation, not destructor execution. |
| `Assert` | Condition evaluated; failure kind and unwind block ignored. |
| `InlineAsm` | Rejected by the statement handler. |
| `Call` | Translated call retained subject to builtin replacement and later optimization; unwind block ignored. |
| `Abort` | All three kinds become symbolic panic. |
| `Return` | Produces the logical return; physical transfer and implicit cleanup need correspondence. |
| `UnwindResume` | Rejected if interpreted; ignored unwind blocks are not interpreted. |
| `Break` | Structured loop control. |
| `Continue` | Structured loop control. |
| `Nop` | No operation. |
| `Switch` | Logical branch/match interpretation. |
| `Loop` | Symbolic loop interpretation and pure loop/recursive extraction. |

All 10 `Rvalue` constructors appear below. See [expression syntax] and
[rvalue interpretation].

| Rvalue | Disposition relevant to this audit |
| --- | --- |
| `Use` | Evaluates operand; ignores its `WithRetag` flag. |
| `Ref` | Creates symbolic borrows/loans; final reference representation is the referent value. |
| `RawPtr` | Rejected by the rvalue handler. |
| `BinaryOp` | Logical scalar operations; pointer `Offset` rejected. Arithmetic correspondence includes overflow mode. |
| `UnaryOp` | Logical `Not`, `Neg`, and supported casts; unsupported casts rejected. |
| `NullaryOp` | Surviving runtime-check queries rejected by the rvalue handler. |
| `Discriminant` | Reads logical enum variant discriminant, not physical tag bytes. |
| `Aggregate` | Builds logical ADTs/arrays; union construction and raw-pointer aggregates unsupported. |
| `Len` | Requires earlier conversion to a function call; surviving form rejected. |
| `Repeat` | Requires earlier conversion to a function call; surviving form rejected. |

The auxiliary operation forms are finite too:

- **Operands:** `Copy`, `Move`, `Const`. Copies retain logical content; moves
  invalidate the source in the interpreter. Neither retains a physical transfer
  event. Constant normalization is another correspondence boundary.
- **Places:** `Local`, `Global`, `Projection`. Projections are `Deref`, `Field`,
  `PtrMetadata`, `Index`, `Subslice`. Raw-pointer dereference is explicitly
  rejected; array/slice indexing is converted to calls with logical bounds
  checks. Field/dereference reasoning is over logical values. Pointer metadata
  is not a provenance or reference-validity certificate.
- **Borrows:** `Shared`, `Mut`, `TwoPhaseMut`, `Shallow`, `UniqueImmutable`.
  Shallow borrows are removed by preprocessing; the remaining supported forms
  participate in loan reasoning. `WithRetag` is `Yes` or `No`, ignored by `Use`.
- **Casts:** `Scalar`, `RawPtr`, `FnPtr`, `Unsize`, `Transmute`, `Concretize`.
  Scalar casts translate numerically. The supported scalar-pointer cast calls a
  backend model that always returns `.fail .undef`. Function-pointer casts,
  transmutation, and dynamic-trait concretization are rejected. Supported
  array-to-slice unsizing remains a logical conversion; it establishes no byte
  representation claim. See [cast translation] and [raw-pointer backend].
- **Binary operations:** `BitXor`, `BitAnd`, `BitOr`, `Eq`, `Lt`, `Le`, `Ne`,
  `Ge`, `Gt`, `Add`, `Sub`, `Mul`, `Div`, `Rem`, `AddChecked`, `SubChecked`,
  `MulChecked`, `Shl`, `Shr`, `Offset`, `Cmp`. Overflow modes are `Panic`, `UB`,
  `Wrap`; retaining a mode in an intermediate AST is not evidence that every
  backend preserves its failure classification. `Offset` is rejected. This
  audit did not prove all scalar implementations or their mode combinations.
- **Unary operations:** `Not`, `Neg`, `Cast`. **Nullary operations:**
  `UbChecks`, `OverflowChecks`, `ContractChecks`.
- **Abort kinds:** `Panic`, `UndefinedBehavior`, `UnwindTerminate`, all collapsed
  by the statement handler. See [abort syntax].

Declarations and constants can introduce effects or erase representations even
when the statement roster stays unchanged. Their complete outer constructor
lists are included to make that boundary explicit:

- **Types:** `Scalar`, `Array`, `Slice`, `Adt`, `Ref`, `RawPtr`, `FnDef`,
  `FnPtr`, `DynTrait`, `Pattern`, `Never`, `TypeVar`, `TraitType`, `PtrMetadata`,
  `Error`. Signature translation explicitly rejects unsupported types; raw
  pointers have a limited backend carrier. ADT fields, traits, builtin mappings,
  attributes, regions, and ABI/layout metadata require review beyond this list.
  In particular, erasing reference regions or marker-trait evidence does not
  establish arbitrary unsafe callers' ownership obligations. See [type syntax].
- **Constants:** `Bool`, `Integer`, `Char`, `Float`, `Adt`, `Array`, `Ref`,
  `Ptr`, `Str`, `ByteStr`, `FnDef`, `FnPtr`, `PtrNoProvenance`, `TypeId`,
  `RawMemory`, `Var`, `Global`, `Call`, `TraitConst`, `VTableRef`, `Discriminant`,
  `SizeOf`, `AlignOf`, `OffsetOf`, `Opaque`. Normalization converts many to
  ordinary expressions or calls. Surviving raw memory and opaque constants
  explicitly fail interpretation. Const evaluation can already have selected
  values using the compiler's layout and target assumptions. See [constant syntax].
- **Bodies:** `Unstructured`, `Structured`, `TargetDispatch`, `Extern`,
  `Intrinsic`, `Opaque`, `Missing`, `Error`. Our driver requests structured
  bodies for one configuration. External/builtin interpretations are trusted
  definitions requiring correspondence, not verified Rust bodies. An opaque
  leaf must never receive an unconstrained successful implementation merely to
  make extraction work. See [body syntax].

## Other transformation boundaries

The [MIR importer] has an exhaustive match over its pinned MIR statement and
terminator forms. Assignments, discriminants, storage markers, calls, assertions,
control flow, drops, assembly and aborts reach the corresponding Charon forms.
`Assume` and `CopyNonOverlapping` become intrinsic calls, not no-ops. Projected
place mentions are retained; mentions of an unprojected local are discarded.
Fake reads and user type ascriptions become borrow-checking information.
Coverage markers, const-evaluation counters, lint-only drop hints and no-ops
are discarded. False edges/unwinds retain only their real control-flow edge.
Coroutine drop, tail calls and yield are explicitly unsupported. This inventory
does not audit the earlier rustc passes that produced the input MIR.

[Charon transformations] replace explicit overflow, division and bounds checks
with operations that must implement those checks; reconstruct vector/box
operations; convert indexing to calls; and simplify control flow and constants.
It is necessary to inspect the replacement operation, not just note that a check
disappeared. For example, removing an unused unit local is restricted to avoid
removing a read through a pointer. Aeneas preprocessing additionally removes
shallow borrows and storage/borrow-checking markers, erases body regions, and
normalizes unreachable calls and panics. See [Aeneas preprocessing].

The inspected pure-output optimizations do not simply discard every call whose
result is unused. `filter_useless` preserves a monadic computation unless it
recognizes unconditional success or a narrowly redundant indexing check. That
is useful positive evidence for our failure marker. It still relies on effect
classification and pure deterministic semantics. Duplicate-call elimination
explicitly warns that stateful backward functions would require a change.
Stateful primitives must make state an explicit input/output, or the applicable
transformations must be changed and justified. See [unused-call filtering],
[failure analysis], and [duplicate-call elimination].

Builtin replacement is another separate boundary: matching a Rust name to a
Lean implementation can avoid inspecting its Rust body. The scalar, byte-order,
container, allocation and trait replacements therefore need claim-specific
correspondence. This audit examined the replacement policy and key examples,
not every backend implementation. See [builtin replacements].

## Inventory of a preserved zerocopy extraction

The preserved `forbidden-execution-20261008/zerocopy.llbc` artifact has SHA-256
`62f9b864513a45ffdaeae802021d73cf3802db28d3337acfbd314d12d2136d7a`.
It contains 188 present function declarations: 130 structured and 58 opaque.
This was an inspection of existing evidence, not a fresh extraction or proof run.
The inventory includes dependencies and generated methods; not every declaration
is an independently specified root.

- No residual `Drop` or `InlineAsm` statements were present, including unwind
  blocks. No target-feature attributes were found on the function declarations.
- Normal bodies contained 39 `PlaceMention` statements. Their projection chains
  contained 14 reference dereferences and 26 field projections, with no raw
  pointer dereference or index/subslice projections. This does not itself prove
  their validity; it limits the concrete cases that need justification for this
  artifact.
- Normal bodies contained 26 panic aborts and 12 UB aborts. These retain a
  failure in the current generated semantics despite losing the failure kind.
- Unwind blocks contained 503 `UnwindResume` statements and eight UB aborts.
  Aeneas ignores the enclosing calls'/assertions' unwind paths. Unwind behavior
  cannot therefore be inferred from the normal-result proofs.

These counts are a checkpoint, not an enforced support policy. A future source
change or pin update can change them. Golden comparison plus proofs does not
replace an admission rule for a stronger safety claim.

## A principled preservation rule

Confidence requires more than finding every intentional erasure. Choose a
relation between concrete Rust states and abstract modeled states, then establish
that every concrete behavior relevant to the contract is covered by the model.
An omitted operation is acceptable only if it preserves that relation and cannot
hide a forbidden event or a required observation. For safety, reason about traces
up to the first UB event: that event must remain forbidden in the abstraction.
Treating UB as an arbitrary successful result would defeat this purpose.
Even retaining every operation would be insufficient if an operator, branch,
or builtin replacement had the wrong meaning. An erasure inventory is evidence
for the correspondence argument, not a substitute for it.

This relation concerns execution semantics, not a new mandatory representation
theorem for each mathematical type decoder. A type's mathematical model may
still forget details irrelevant to its operation contracts. The translation must
preserve whatever observations and safety conditions those contracts require.

For padding, the relation can forget every padding byte's contents and
initialization. A valid padding write or typed transfer can then preserve the
relation without an explicit event. A later supported read cannot manufacture an
initializedness fact that was forgotten. This restriction rejects some sound
programs, as issue #1405 describes, but it does not justify accepting bad ones.

Total correctness needs an additional progress argument. Infinitely many erased
Rust steps must not appear as a terminating abstract execution. Preserving just
finite successful results would be insufficient. Partial correctness may admit
divergence, but it must still exclude executions that reach UB.

Aeneas's [borrow-calculus soundness paper] already proves simulations between
its symbolic, borrow-centric and pointer languages. That gives a method and
substantial evidence for its intended subset. It does not establish our proposed
abstract-byte extension or every pass of the pinned Rust-to-Lean implementation.
The ultimate claim is that a proved abstract contract transfers to the concrete
Rust execution under stated input and correspondence premises.

The smallest practical next step is a claim-specific supported subset:

1. Inspect the full dependency closure and implicit type/call effects before the
   relevant information is erased. This includes destructor-bearing types,
   target-feature attributes and external calls, not just explicit `unsafe`.
2. Require an interpretation and correspondence argument for every admitted
   effect; reject unsupported cases. Destructors need precise extraction or a
   justified exclusion. An LLBC-only check cannot discover an earlier erasure.
3. Keep byte-to-value production behind checked storage primitives. Preserve
   forbidden execution through sequencing and any future handlers. Today’s
   `.undef` rules cover represented primitives, not arbitrary source operations.
4. Challenge the boundaries with negative controls: invalid production, ignored
   results, destruction, invalid place formation, and eventually CPU-feature
   and unwind behavior. Differential tests against an abstract-machine
   interpreter are useful evidence; they do not prove exhaustive equivalence.

A verified interpreter or kernel-checked translation certificate could make
this argument compositional and shrink the translator's trusted boundary.
That would be a larger project. Neither this source enumeration nor ordinary
golden/proof checks provide such a certificate.

[statement syntax]: https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/ast/bodies/structured.rs
[expression syntax]: https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/ast/bodies/expressions.rs
[type syntax]: https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/ast/type_level/types.rs
[constant syntax]: https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/ast/bodies/values.rs
[body syntax]: https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/ast/bodies.rs
[abort syntax]: https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/ast/bodies.rs#L215
[statement interpretation]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/interp/InterpStatements.ml#L779
[operand evaluation]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/interp/InterpExpressions.ml#L556
[rvalue interpretation]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/interp/InterpExpressions.ml#L1464
[type translation]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/symbolic/SymbolicToPureTypes.ml#L139
[drop configuration]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/Config.ml#L628
[feature gates]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/Config.ml#L349
[Rust target-feature rules]: https://doc.rust-lang.org/reference/attributes/codegen.html#the-target_feature-attribute
[Charon options]: https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/options.rs#L525
[MIR configuration]: https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/bin/charon-driver/driver.rs#L33
[MIR selection]: https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/bin/charon-driver/translate/get_mir.rs#L60
[MIR importer]: https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/bin/charon-driver/translate/translate_bodies.rs#L1501
[Charon transformations]: https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/transform/mod.rs#L105
[Aeneas preprocessing]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/PrePasses.ml#L2342
[box elimination]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/pure/PureMicroPassesGeneral.ml#L2156
[cast translation]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/symbolic/SymbolicToPureExpressions.ml#L560
[raw-pointer backend]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/backends/lean/Aeneas/Std/RawPtr.lean#L31
[unused-call filtering]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/pure/PureMicroPassesGeneral.ml#L1157
[failure analysis]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/pure/PureUtils.ml#L1544
[duplicate-call elimination]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/pure/PureMicroPassesGeneral.ml#L607
[builtin replacements]: https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/extract/ExtractBuiltin.ml#L507
[borrow-calculus soundness paper]: https://arxiv.org/html/2404.02680v1
