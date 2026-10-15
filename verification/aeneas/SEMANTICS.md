<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Layout semantics and the Rust boundary

`lean/LayoutMath.lean` defines layout independently of the Rust implementation.
Its recursive `Description.size` places a complete inner field at an aligned
offset, then rounds the enclosing record's size. Every level retains the
inner field's own padding. `Description.offset` tracks the physical slice
offset separately from the size calculation.

The compilation theorem is parametric in nesting depth and slice metadata.
For a leaf whose element size is divisible by its alignment,
`compile_size` proves that normalization into a `Formula` preserves size for
every metadata value. `compile_offset` and `compile_elem` preserve physical
offset and element stride; `compiled_contains_tail` proves that the full size
contains those physical bytes. These statements use unbounded `Nat`
arithmetic and do not assume that the result fits a machine integer.

The normalization target describes size as
`base + roundUp (phase + metadata * elem) align`. Neither `base + phase` nor
the method called `size_offset` is generally the physical slice offset.
`pad_size` proves the two alignment-order cases of rounding a normalized
formula, and `advance_size` proves byte advancement independently of the
physical offset. `capacity_spec` and `maximal_metadata` account for plateaus:
several different metadata values can have the same complete padded size.

`recordState` separately evaluates declaration-order field placement for each
metadata value. It uses each field's complete size, without manipulating the
normalization's base, phase, or size alignment. `recordState_refinement` proves
that the normalized prefix fold agrees with this direct rule for arbitrary
field lists in the construction domain. `constructor_matches_record` connects
the extracted, terminating record constructor to this rule and final rounding.

## Explicit Rust premise

The Rust reference in `zerocopy/src/layout/nested_reference.rs` follows the same
recursive rule using checked machine arithmetic and remainder-based rounding.
`assert_matches_dst_layout` compares its complete optional size with the
production layout for arbitrary nesting and metadata. A total unit contract
checks the assertions themselves, including equality when both computations
overflow. Its early returns describe the construction domain in Rust. Other
Rust harnesses compare primitive fields, trailing sizes, capacity, metadata,
and cast results. They make these application claims readable without inspecting
the out-of-line Lean proofs that establish them.

The mathematical statements do not certify a compiler implementation. Their
application to Rust assumes the following bridge for the exact compiler,
target, features, and type instantiation used for extraction or a regression
test:

1. Element size and alignment inputs equal Rust's `size_of` and `align_of`
   results; alignment is a positive power of two, and element size is a
   multiple of it. Slice metadata counts elements with this stride.
2. A `repr(C)` record places fields in declaration order, aligning the next
   field's offset and adding its complete size. The record is finally rounded
   to its own alignment. Packing caps field placement alignment; explicit
   alignment raises the record's alignment. Neither changes an inner field's
   complete size or internal padding.
3. An accepted type instantiation with generic indirection around a packed
   field follows the same recursive rule, including when an inner type has an
   explicit alignment. Continued acceptance of this otherwise prohibited
   transitive combination is a compatibility premise, not a Reference theorem.
4. The descriptor inputs correspond to the actual fields and representation
   modifiers. Bounds required by each extracted contract hold, including
   machine overflow checks and the compiler's allowed alignment range. Object
   creation and pointer operations additionally require their own Rust safety
   contracts; a numerical layout theorem does not establish these contracts.

The versioned [Rust 1.93 layout Reference](https://doc.rust-lang.org/1.93.0/reference/type-layout.html)
provides the source of the ordinary layout rules. In particular,
`layout.repr.inter-field` says that an outer representation
"does not change the layout of the fields themselves". The sections
`layout.properties.align`, `layout.properties.size`, `layout.array`,
`layout.slice`, `layout.repr.c.struct.size-field-offset`, and
`layout.repr.alignment` supply the other rules. Applying these rules to the
pinned extraction compiler and other tested compilers is an explicit
compatibility premise. Sparse compiler tests do not prove compatibility for
an interval of compiler versions or for an untested target.

The packed regression has complete size 10 at metadata zero, whereas the old
flattened calculation yields 8. `packed_regression` checks this witness in
Lean. Compiler regression tests independently compare actual Rust layouts
with the candidate recursive rule; their role is to challenge the bridge,
not to replace the universal algebra proof.

## External inputs and trust

Aeneas erases ABI layout information from generic Rust type parameters.
`Zerocopy.RustLayout.size` and `Zerocopy.RustLayout.alignInput` are
uninterpreted **data inputs**, each of type `Type → Usize`. No proposition
about their values is an axiom. `RustLayout.align` uses alignment one for the
concrete byte carrier `U8` and the abstract alignment input for every other
carrier. That byte interpretation is an explicit compiler-correspondence
premise, checked by a Rust compile-time assertion. It allows the concrete
`u8: Unaligned` dictionary to discharge its trait law without assuming that
all types have alignment one. The constructors' contracts explicitly
require the relevant primitive reads and alignment properties. The audit
admits exactly these two names and verifies their signatures. Changing an
input to a proposition, or adding another axiom, fails the audit.

The primitive correspondence applies to the selected Rust type instantiation;
Lean's erased type alone is not an ABI descriptor. If distinct Rust types erase
to the same Lean type, each constructor theorem still needs its own primitive
read premise. Combining incompatible ABI interpretations into a single
instantiation is not justified by the data-input model.

The `usize` size used to calculate pointer width is modeled separately as
the selected word width divided by eight. The extracted scalar model
supports 32- and 64-bit words. `NonZero::new` is modeled for the `Usize`
instantiations actually extracted: zero returns `None`, and a nonzero input
returns that input without changing its bits. Other type instantiations return
the forbidden-execution marker because their model is unsupported; this makes
no claim about their actual Rust behavior. `NonZero::get` returns those
bits. Lean's representation permits zero in the external wrapper, so contracts
using mathematical models reject that zero representation through the native
NonZero decoder. Its mathematical output carries positivity and machine bounds.
The rounding decoder accepts every positive representable word and decomposes
it into a power-of-two alignment and a bounded phase; structural layout models
reuse that shared pair. This admission law requires its ordinary Lean proof and
does not change the extracted raw implementation.

The extracted cast metadata helper uses Rust's unsafe `usize::unchecked_mul`
and `usize::unchecked_add`. Their handwritten external models use Aeneas's
checked multiplication and addition on fitting inputs, and return `.fail .undef`
on overflow. The correspondence premise is restricted
to non-overflowing inputs: each call returns the exact natural-number result.
No correspondence is claimed for overflowing inputs, where Rust's unchecked
operations have undefined behavior. The arithmetic contracts prove both
intermediate results fit; `cast_from::checks::assert_cast_preserves_size`
derives those bounds from an accepted plan and a representable complete source
size, rather than accepting them as harness preconditions. The root also checks
size preservation against the independent remainder-based reference. It
covers the numerical composition, not pointer provenance, reference validity,
or the `KnownLayout` implementation obligations at the pointer boundary.

The downstream `forbiddenExecution` marker uses Aeneas's existing `.undef`
failure tag. The backend also uses that tag for unsupported modeling, so it
means that no execution claim is permitted, not that every tagged case is Rust
UB. Both total and partial contracts reject it, and sequencing propagates it
even when a caller discards a result. CI independently checks the complete
unchecked-arithmetic interpretations, including their overflow tags, and rejects
downstream execution dependencies on the backend's failure-erasing
`Option.ofResult` adapter, including uses hidden behind local helpers. The audit
stops at the pinned backend's implementations: its checked integer operations
use that adapter internally to turn arithmetic overflow into Rust's `None`.
These checks run against both golden and live models. They do not prove arbitrary
external models faithful to Rust; those models and the translator remain part
of the trusted boundary.

Panic catching, panic-tolerant contracts and thread spawning are not modeled.
Adding them requires preserving forbidden executions independently of which
defined outcomes a caller accepts. A future spawn contract must also establish
safety of the child execution, including after the parent returns or detaches
the child. A successful parent result alone cannot establish that property.

The remaining trusted boundary is the pinned Rust-to-LLBC-to-Lean translation,
its builtin arithmetic and control-flow models, the external primitive
correspondences above, the Lean kernel, and specification adequacy. Both
golden and live extraction must independently satisfy the required theorem
types, axiom audit, and proof dependency checks. Fuzzy textual equivalence
alone establishes none of these semantic claims.

## Admitted execution and remaining storage limits

The [pinned lowering audit](LOWERING_AUDIT.md) records operations that translation
ignores or abstracts, including destruction, allocation and physical value
transfers. A forbidden tag rejects an operation represented in the model; it
cannot reveal an operation erased before that model was produced.

[ADMISSION_DESIGN.md](ADMISSION_DESIGN.md) describes the implemented restricted
value-and-borrow fragment. CI checks a preserved promoted-MIR import before
Charon's transformations, final LLBC, and the complete executable dependency
closure. A retained conditional drop requires a kernel-checked proof that its
whole local has no destruction obligation, independently for both compiler
snapshots. Other drops, unsupported operations, and unregistered opaque calls
reject the run. The ownership proof does not certify compiler translation or
execute destructor bodies.
Admission is tied to the compiler inputs and the patched runtime; it is not a
formal certificate of rustc or Aeneas correctness. Valid incoming references,
reviewed builtin lowering, and registered external interpretations remain
explicit premises. Boolean production and byte copying exercise two such
boundaries; they do not establish general storage or provenance semantics.

<!-- FIXME: Exact abstract bytes for general typed values require accounting for
typed copies: https://github.com/AeneasVerif/aeneas/issues/1405. A restricted
model can instead forget padding contents and initializedness at all times,
while retaining access obligations. The current numerical byte-order model
does not supply this storage semantics. -->

## Mathematical model and ghost domain

`RustModel` associates a raw carrier with a mathematical type and an optional
decoder. The complete decoder recursively decodes every field before applying
the inline local decoder. Its accepted domain and retained observations are
part of the specification. It does not require injectivity, an encoder, or a
canonical raw representative. Constraints stored as model proof fields must be
established by safe Lean construction under the same axiom audit as the proofs.

Function contracts execute the original extracted function on the original raw
arguments. Plain clauses refer to decoded values; `(raw)` clauses refer to the
corresponding raw inputs and successful payload. Both require accepted inputs
and successful output decoding. Named requirements are successive premises;
multiple postconditions are conjunctive. Ordinary ghosts are universally
quantified in mathematical input context, before requirements and execution.
Their types may impose premises or be empty. Conditional correctness does not
establish unconditional caller admission or panic-freedom for such domains.

Automatic providers are fixed from the single verified source/extraction table,
explicit generic dictionaries, and recursive container combinators. Authored
instances cannot redirect these retained choices. Model shapes precede support helpers and full decoders; ordinary Lean imports
must remain acyclic. Raw representations and temporary internal states remain
unchanged by these mathematical interpretations.

Independent required contracts compare the inline contract with an authored
expectation for every possible execution outcome, including panic and divergence.
The comparison preserves input admission, requirements, and postconditions; only
its execution argument is abstracted. After proving the implication, the checker
specializes it to the original extracted call and canonical proof. Model proof
fields establish that successfully constructed mathematical values satisfy their
constraints. Operation expectations establish what those values mean for the
verified methods. A separate representation relation is optional proof machinery,
not a universal requirement. See [DESIGN.md](DESIGN.md) for the full design and
explicitly deferred decisions.

## Concrete owned standard transmute

The private `util/owned_transmute.rs` entry points call the actual standard
`core::mem::transmute` operation. Native extraction lowers it to
`core::intrinsics::transmute`; its external interpretation has an explicit,
closed implicit provider parameter. The reviewed endpoints are `u32 -> [u8; 4]`,
`[u8; 4] -> u32`, and `u8 -> bool`. Original compiler evidence retains those
ordered Rust type arguments. Admission rejects every other instantiation, and
compiled auditing checks each reached call's canonical provider, including calls
inside unannotated helpers. It also independently checks the whole primitive
and provider definitions and the extended primitive signature.

The integer providers encode and decode little-endian bytes. Verification admits
only the original 64-bit little-endian compiler target and rejects target
overrides before compilation; the private integer harness module is gated by
Rust's target-endian configuration. Ordinary nonproof builds remain portable.
The Boolean provider accepts exactly bytes zero and one and returns `.fail
.undef` otherwise, before constructing a Boolean. Its validity rule is independent
of endianness. Discarding an invalid result cannot make a True postcondition hold.

This interpretation relies on the standard transmute contract: both values must
be valid at their types, equal sizes are checked by Rust, and the operation moves
the representation. These fixed unsigned scalars and byte arrays accept every
bit pattern, contain no padding or pointers, and have no destructor. The
[standard contract](https://doc.rust-lang.org/std/mem/fn.transmute.html) does not
promise preservation of padding for general by-value types. The interpretation
supplies no general pointer, provenance, allocation, borrowing, or generic trait
law, and proves no production `transmute!` macro expansion.

## Generic owned conversion through `transmute_copy`

The const helper in `util/macro_util.rs` consumes `Src: IntoBytes`, checks equal
sizes with the real post-monomorphization assertion, wraps the source in
`ManuallyDrop`, and calls the standard `transmute_copy`. Its independent generic
caller in `util/generic_transmute.rs` consumes the helper's contract. Both roots
are extracted and proved in the golden and live builds. The production
`transmute!` macro does not use this helper yet. Rust versions before 1.74 omit
the helper, because the standard operation was not const on those versions.

Three different facts support the byte proof. `IntoBytes` establishes that all
accepted physical representations are initialized. It also establishes source
realizability: each mathematically admitted source value has some physical
representation. `FromBytes` establishes that every initialized representation of
the destination width admits both a language value and a mathematical value.
Realizability is conditional on a source value, so an uninhabited source remains
vacuous; it does not acquire an arbitrary value or an `Inhabited` requirement.

`RustModel.sameSize` makes the layout bridge explicit. The ordinary total ABI
queries must return the same `usize`, and both physical decoder widths must
equal that observed size. This is the correspondence premise of the Lean model,
not an additional safety rule imposed on safe Rust callers. The Rust assertion
checks actual sizes; the byte models still need their documented correspondence
to Rust. Existing layout proofs retain their original ABI query interpretation.

Physical decoding is a relation from a raw value to its accepted byte strings;
it need not provide a unique string. A model's `representationChoice` selects a
preferred string, which is checked before use. Generic contracts universally
quantify that provider. Coverage theorems then vary its preference while fixing
its decoders, proving that every permitted representation and decoded outcome
occurs in the verified family. The public postcondition `byteCast` observes a
common byte string, independently of the preference. Tests exhibit two distinct
destination values for the same raw source. This covers ambiguous source
representations, not nondeterministic decoding of one fixed string.

The admitted fragment permits at most one conversion per execution, including
unannotated callees and constant initializers. Repeated calls, recursion, loops,
and concrete forwarding that would fix the source preference are rejected.
Supporting them requires an explicit extension of the choice semantics. The
compiled audit checks original type arguments and exact retained providers on
both direct and forwarded calls. Equal Lean carrier types cannot justify
substituting another provider. Identical pure size queries may be shared by
Aeneas; their endpoint bindings remain mandatory, while copy calls retain their
original multiplicity.

The standard-library boundary supplies `ManuallyDrop`'s layout and bit-validity
identity, destructor suppression, and the equal-width `transmute_copy` behavior
on a valid readable reference. It permits different source and destination
alignments. The ownership checker independently proves all ignored conditional
drops empty, including unwind paths. No meaningful destructor execution,
pointer provenance, allocation ownership, or external resource invariant is
modeled. Destination padding may be forgotten after construction; it is not
promised to retain its input bytes. General typed-copy storage effects remain
deferred: [Aeneas issue #1405](https://github.com/AeneasVerif/aeneas/issues/1405).

The underlying contracts are recorded in the pinned standard library and the
[versioned `ManuallyDrop` documentation](https://doc.rust-lang.org/1.74.0/core/mem/struct.ManuallyDrop.html)
and [`transmute_copy` documentation](https://doc.rust-lang.org/1.74.0/core/mem/fn.transmute_copy.html).
The numeric, resource-free representation profiles remain the supported domain;
this proof does not admit arbitrary downstream representations merely because a
trait dictionary can be extracted.

## Referent-content boundary

`Rust.Referent.Allowed` combines an explicit byte width with a content promise.
`Safe` requires a raw value from physical decoding and a mathematical value
from that same retained model's decoder. An empty safe domain makes a
safe-source implication vacuous without constructing an impossible value.
Completeness in the other direction still requires an actual decoded result.

`TransmuteFrom` is conditional on equal widths. Its composition theorem also
requires the intermediate width to agree; outer equality alone is insufficient.
Transparent-wrapper proofs compare both decoding stages, so equal layout alone
cannot erase a library invariant. `CastableFrom` states its two permitted type
identity pairs directly, rather than accepting coincidentally equal safe domains.

The type-level validity codes identify the four empty Rust markers and agree
with their actual associated constants. They do not inhabit the marker types
or interpret `AsInitialized`. The resource-free numeric representation premise
still governs application to Rust; these laws provide no permission to access
or mutate memory. Opaque `MaybeUninit` has no admitted storage model here.
