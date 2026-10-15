<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Aeneas verification in CI

The `aeneas` job in `.github/workflows/ci.yml` compiles selected zerocopy functions
with Charon and Aeneas, compares complete generated Lean goldens, and proves
the inline Rust specifications against both the checked-in and live models.
The required `All checks succeeded (ci.yml)` job depends on it. The settled design
and deferred work are recorded in [DESIGN.md](DESIGN.md).

For application review, start with the ordinary Rust reference calculations and
assertion harnesses in [`layout/nested_reference.rs`](../../zerocopy/src/layout/nested_reference.rs),
[`layout/tail_checks.rs`](../../zerocopy/src/layout/tail_checks.rs),
[`layout/composition_checks.rs`](../../zerocopy/src/layout/composition_checks.rs),
[`layout/tail_transform_checks.rs`](../../zerocopy/src/layout/tail_transform_checks.rs),
[`layout/primitive_checks.rs`](../../zerocopy/src/layout/primitive_checks.rs), and
[`util/checks.rs`](../../zerocopy/src/util/checks.rs). A total `ensures _ => True`
specification on a harness proves that it terminates without failing any of its
assertions for every admitted input. The assertions, comparisons, and early
returns are ordinary Rust, so the reviewer can assess the intended behavior and
its domain together. In particular, a guard that returns early excludes that
case from the comparison even though the harness itself still succeeds.

Six concrete wrappers in [`lib.rs`](../../zerocopy/src/lib.rs) call the actual
`PointerMetadata` implementations for `()` and `usize`. Their contracts check
element-count conversion, layout-variant handling, and checked metadata sizing.
Using these results for an arbitrary `KnownLayout` implementation requires
separate layout correspondence.

The numerical harness in [`split_at.rs`](../../zerocopy/src/split_at.rs) compares
split sizes with the independent remainder-based reference. It checks physical
tail containment and the zero-padding gate. The shared length helper also runs
in the production pointer path. These proofs establish bounds and disjoint byte
intervals, including empty and zero-sized tails; pointer validity and provenance
remain separate Rust obligations.

The checks in [`pointer/mod.rs`](../../zerocopy/src/pointer/mod.rs) follow the
actual `CastUnsized` layout gate. Accepted DST pairs retain alignment, physical
tail offset, and complete sizes for every metadata count. Sized pairs need only
equal sizes, including zero-sized layouts with different alignments. Rejection
does not claim that a cast would be impossible. The proof covers the numerical
decision and sizing comparison, not the resulting pointer's validity.

The checks in [`util/allocation.rs`](../../zerocopy/src/util/allocation.rs) cover
actual metadata sizing and exact preparation of allocator arguments. Preparation
preserves every optional size and the supplied alignment, without adding a
runtime validity filter. Under explicit correspondence to a valid recursive
layout, separate lemmas establish complete size and tail containment. Numerical
allocator admission additionally needs the outer alignment and the signed
metadata-size bound. Allocator behavior, zeroing, and `Box` validity remain
separate Rust obligations.

These harnesses use the same annotation and proof rules as every other function.
There is no root marker or separately maintained list of required functions.
Every present specification must have its corresponding proof in both CI builds.
Removing a specification deliberately removes that claim; the Rust diff must
make that decision visible. Helper specifications remain useful proof interfaces,
but understanding their Lean proofs is unnecessary to assess what a Rust
assertion harness promises. Reviewing the integration itself still requires
reviewing the extraction, contract elaboration, and audit machinery below.

Source coverage is unconditional under `zerocopy/src`: discovery includes
inactive cfg branches and unused modules, even in directories named `vendor`,
`target`, or `.lake`. An annotated item absent from the selected compilation
fails extraction binding. Symbolic links and unreadable source directories
also fail rather than silently removing source from the checked set. Both the
file roster and its contents must remain unchanged throughout verification.

## How the implementation fits together

The integration connects a comment beside a Rust function to a proposition that
Lean has proved about that function. Several tools make that connection, because
each tool answers a different question:

1. Rust's parser identifies the item that owns the comment. The independent
   source audit accounts for every reserved fence, including fences the parser
   cannot associate with a supported item. These checks prevent an annotation
   that looks meaningful to a reader from being silently ignored.
2. Charon translates the selected Rust implementation to LLBC, an intermediate
   representation of its types and control flow. Aeneas translates LLBC to Lean.
   This is the **extracted model**: executable Lean definitions representing the
   Rust program. Extraction includes called functions, not just the annotated
   function's body.
   Before Aeneas runs, `admission.py` follows every executable dependency from
   every discovered specification in two snapshots: original promoted MIR as
   imported by Charon, and final LLBC. Annotation status never exempts a callee.
   Unsupported drops, raw pointers, arbitrary indirect calls, foreign code,
   and unknown effects reject extraction. Calls through original trait
   dictionaries are admitted only through the checked trait-law boundary
   described below. This prevents an operation from being accepted
   simply because a later lowering forgets it. The small Charon snapshot patch
   preserves evidence; it changes neither Aeneas nor the execution semantics.
3. Our Lean declarations describe how extracted values are interpreted as
   mathematical values. A `RustModel` supplies a mathematical type and a decoder.
   Successful decoding defines which representations a contract admits. The
   decoder first checks every field, then applies the type's authored decoder.
   A parent that ignores a field cannot thereby skip that field's admission.
   The binding manifest also accounts for every compiled raw type, including
   trait dictionaries and external nominal types. Live classification comes
   from Charon declarations; Lean checks the complete compiled image against
   that roster. Local nominal types additionally need their exact source-bound
   model provider. Macro-generated dependency types can use a structural model
   only when their inspected source span belongs to an item macro. A literal
   `invariant_proof` marker in macro input instead binds to its unique compiled
   trait impl through the compiler's documentation origins. Macro input does
   not support function specs or mathematical model declarations.
4. The `spec` command turns the inline requirements and postconditions into a
   transparent proposition in `Specs`. A handwritten Lean theorem proves that
   proposition. The command supplies input decoding and successful-result
   decoding, even when the authored postcondition says only `True`.
5. Separately written `Obligations` describe the behavior and input domain we
   intend to retain. `check_contract` proves that the authored spec implies that
   expectation for an arbitrary execution outcome. It then applies that
   implication to the actual function and its canonical proof. `Check` audits
   these compiled declarations, their source bindings, and their assumptions.

The extracted model and the mathematical model have different purposes. The
first represents the computation we prove properties about; the second supplies
the vocabulary in which we state those properties. For example, Rust stores
rounding alignment and phase in one nonzero word, while its mathematical model
exposes two natural numbers. Plain clauses use mathematical values; `(raw)`
clauses use extracted representations. Both execute the same extracted function
on its original arguments and require the actual returned value to decode.

Aeneas also distinguishes execution from the value returned by execution.
`Aeneas.Std.Result` represents success, failure such as panic, or divergence.
A successful computation may itself return a Rust `Option` or Rust `Result`.
Thus successful execution returning Rust `None`, a decoder rejecting a value,
and the function panicking are three different events. Total `spec` requires
success; `partial spec` also allows divergence, while still excluding panic and forbidden execution (`.fail .undef`).

The independent comparison checks the specification itself. For an identity
function, both `ensures r => True` and `ensures r => r = x` are provable about
the real implementation. Comparing only those concrete truths would not reveal
that the first specification promises less. Comparing an arbitrary outcome
does: a wrong result satisfies `True` but fails the independently required
identity property. The required domain is independent too, so a decoder that
rejects every input cannot silently remove previously promised coverage.

`run.sh` builds this whole chain twice. One build uses the checked-in extraction;
the other uses a fresh extraction. Fuzzy comparison permits specified textual
differences between them, but each build must prove all the same contracts and
pass the same audits. Neither build substitutes the inline mathematical decoder
for an extracted function definition.

CI invokes `workspace.py verify`, which requires fresh live-extraction admission
even when checking the golden definitions. It also checks that the copied proof
sources still match the checkout before and after compilation. The editor's
`check` command also supports development bindings, which cannot certify a Rust
extraction.

Each proof check rebuilds the proof package and the shared Lean packages authored
in this checkout. Lake may reuse the pinned compiler and dependency artifacts;
it must not reuse an earlier compiled meaning of an edited shared model.

The checked-in `projections/ModelShapes.lean`, `projections/Models.lean`,
`projections/Specs.lean`, and `projections/TraitLaws.lean` expose the Lean source
assembled from Rust annotations.
CI regenerates these files in both proof projects and requires exact equality,
including comments and whitespace. They make generator changes reviewable even
when the Rust annotations are unchanged. They contain macro invocations, not
fully elaborated propositions; use spec inspection for the latter.

Track authoritative sources and useful, reproducible review artifacts. Ignore
disposable execution and editing state. These projections and the Aeneas goldens
are review artifacts; neither replaces fresh generation. Compiled caches and
installed toolchains are ignored. Editable projections under `lean/` are also
ignored until their authored fragments are copied back to Rust. Update the
review snapshots with `bash verification/aeneas/run.sh --update-goldens`, which
checks the live proofs before writing either family. Never edit the snapshots
instead of their Rust sources or generator.

For a first review of the verification machinery, follow this order:

| Start here | Question answered |
| --- | --- |
| A Rust `aeneas` fence | What behavior does the author promise? |
| `RustModel.lean`, `DeriveModels.lean` | How are representations admitted and interpreted? |
| `SpecsSyntax.lean` | What proposition does the fence mean? |
| `Proofs/Util.lean` or a named theorem in `Proofs.lean` | Why does the extracted computation satisfy it? |
| `Obligations.lean`, `RequiredContracts.lean` | Does that promise retain the independently stated behavior and domain? |
| `Check.lean`, `run.sh` | How does CI check that every source annotation has the required proofs? |
| `copy_back.py`, `workspace.py` | How can native Lean editing update the authoritative Rust comments safely? |

When reviewing specifications, follow the
[agent review guidance](../../skills/zerocopy-review/SKILL.md#specification-meaning):
reconstruct the intended guarantee and check whether the written domain and
postconditions could promise less. Passing proofs establish the written claims;
they do not establish that those claims capture the intended behavior.

The comments in these modules explain their inputs, outputs, and non-obvious
checks. [SEMANTICS.md](SEMANTICS.md) states the premise connecting the independent
layout mathematics to Rust. This integration proves conditional functional
behavior; it does not prove that every caller meets the requirements or that
zerocopy's unsafe pointer operations are sound.

## Unsafe boundaries and admission

`external.json` lists exact reviewed Rust identities and signatures, with the
Lean interpretation used at each boundary. It derives the local `--opaque`
selections; arbitrary opaque flags are rejected. A changed local helper body
requires a fresh review and an updated body digest. Registration is a trusted
Rust-to-model premise, not a Lean proof of the omitted body. Standard-library
builtin correspondence also remains part of the pinned translator's trust
boundary. See [ADMISSION_DESIGN.md](ADMISSION_DESIGN.md) for the implemented
fragment and [LOWERING_AUDIT.md](LOWERING_AUDIT.md) for the erasure inventory.

The first storage examples are in
[`util/safety_checks/mod.rs`](../../zerocopy/src/util/safety_checks/mod.rs):

- `checked_bool` accepts exactly byte encodings 0 and 1 and rejects all others.
- `checked_copy` copies a fitting prefix, preserves the suffix, and leaves the
  entire destination unchanged when the source is too long. Its model returns
  the updated mutable slice explicitly.

The production `IntoBytes` write methods now call the proved
[`util/bytewrite`](../../zerocopy/src/util/bytewrite/mod.rs) helpers. Their
contracts cover exact, prefix, and suffix writes, preserved surrounding bytes,
and unchanged rejection. A concrete big-endian word consumer additionally
checks the public byteorder constructor/accessor composed with prefix writing.
Native tests compare that composition with `IntoBytes::write_to_prefix`; the
`as_bytes` pointer bridge remains the existing Rust safety argument.

[`util/validity`](../../zerocopy/src/util/validity/mod.rs) supplies the Boolean and
nonzero-word predicates used by the actual scalar `TryFromBytes` implementations.
The checked conversions retain raw candidates until validation; pair and slice
contracts cover invalid bytes at every position. The exact byte-read bridge has
an execution-time bounds guard. These proofs establish conditional behavior for
initialized byte slices, without claiming the whole generic `Maybe` pointer path
has been lowered and verified.

The existing production `add_scaled_metadata` exercises guarded unchecked
addition and multiplication. The primitive definitions have an
independent complete-definition check, including its forbidden branch. Kernel
controls prove rejection even if an invalid result is discarded or followed by
divergence. Extraction controls check actual generated callers that discard an
invalid Boolean or reach it before a loop. Mutation controls also challenge the
failure tag and helper guards.

Incoming references must already denote valid Rust allocations with the
necessary exclusivity and initializedness. Logical byte lists do not establish
provenance, allocation lifetime, or reference validity. Both storage examples
use padding-free `u8`/`bool`; general padding and typed-copy effects remain
unsupported. No panic-catching, thread, callback, or failure-recovery model is
admitted. Both today's total and partial contracts reject *every* execution
failure, including source UB aborts whose tag the pinned importer merges with
panic. Supporting a recovery handler would require preserving that distinction.

The binding manifest records both inspected snapshots, their dependency
closures, exact registry identity, sources, compiler configuration, and patched
runtime. Inputs are captured before compilation and checked again during binding
and after proof checking. Neither a stale report nor development-only extraction
qualifies as completed verification. This remains conditional safety for the
admitted fragment under explicit correspondence premises, not a rustc proof or
whole-program unsafe-code certification.

## Scope and proofs

Rust review entry points: [arithmetic assertions](../../zerocopy/src/util/checks.rs), [nested reference](../../zerocopy/src/layout/nested_reference.rs), [primitive assertions](../../zerocopy/src/layout/primitive_checks.rs), [tail assertions](../../zerocopy/src/layout/tail_checks.rs).

Extraction starts from the function and nominal-type owners of every present
`aeneas` fence in `zerocopy/src`, including their dependencies. The current
function specifications cover the layout and arithmetic methods and their Rust
reference harnesses. Unannotated functions and impls can be added without
extending the specification set. Every present fence must have a supported Rust
owner, exact extraction binding, and the corresponding checked Lean declarations.

| Functions | Checked property |
| --- | --- |
| Byteorder U16/U32 read, write, and set (both endiannesses) | Exact integer value, every encoded byte, and setter/getter equality for every typed input. |
| `max`, `min`, padding, round-down | Exact extrema, least padding, greatest aligned predecessor, and bounds. |
| Alignment/phase encoder and decoders | Power-of-two alignment, bounded phase, and exact encoding round-trip. |
| Trailing size, padding, capacity, and advancement | Independent unbounded size formulas, exact checked-size overflow, wrapping padding, and byte advancement. |
| Size-sequence comparison | A positive answer establishes equal sizes for every natural metadata value. |
| Zero-stride conversion and element capacity | Exact zero handling, preserved representation fields, and greatest fitting element count. |
| `DstLayout` constructors, extension, and padding | Exact fields, field placement, alignment, flags, and normalized size formulas. The record constructor terminates for arbitrary field lists satisfying the independent construction domain. |
| Static and dynamic padding queries | Exact flag result and the mathematical condition sufficient to eliminate dynamic padding for all metadata values. |
| Cast validation and exact-size metadata | Alignment/size error priority, greatest fitting metadata, exact prefix/suffix split, and rejection of unattainable sizes. |

All registered specifications use total `spec`: accepted input representations
and their stated requirements imply successful termination, a valid returned
value, and their postconditions. Intentional panic for
casting a zero-stride DST is checked separately. The size-sequence comparison
is conservative: a negative result does not claim that the sequences differ.

`LayoutMath.lean` defines an independent recursive layout semantics and proves
normalization correct for every nesting depth and metadata value. The extracted
contracts connect machine arithmetic and control flow to that mathematics.
`LayoutModel.lean` supplies shared interpretation predicates, without using
any function proof. `Corollaries.lean` connects checked sizes and physical
padding to the recursive semantics, proves that outer padding preserves
complete inner sizes, and connects the record constructor to direct
per-metadata field placement.
See [SEMANTICS.md](SEMANTICS.md) for the exact Rust premise and trust boundary.

The nested Rust reference starts with `metadata * element_size`, then places
each complete inner record at a remainder-based aligned offset and rounds the
containing size. Its equivalence harness constructs the production layout and
compares the complete `Option<usize>` result, including overflow. It handles
arbitrary nesting, zero-size tails, and every machine-word metadata count.
The construction guards are visible in Rust: invalid descriptors, excessive
alignment, and static layouts that do not fit return before construction.
The tail harnesses additionally compare capacity, exact-size metadata, and both
successful cast splits and alignment/size errors. Their explicit witnesses let
reviewers read alignment and phase directly instead of decoding a stored word.
The original mathematical helper theorems retain their broader natural-number
domains; these Rust harnesses quantify the machine-word arguments Rust receives.
The composition harnesses compare extension, padding, and arbitrary field-list
construction, including every stored field and the shallow-padding flag. The
transformation harnesses compare byte advancement, wrapping padding, dynamic
padding queries, and checked sizes after a positive size-sequence answer. The
existing sequence theorem additionally preserves its unbounded size equality;
equality of checked optional sizes alone would lose differences after overflow.

The inline checks in `layout/cast_from.rs` cover numerical cast composition.
They select a production `CastPlan`, require the checked metadata calculation
to succeed, compare it with the actual unchecked conversion, and compare
complete sizes using the independent remainder-based reference. Metadata
representability follows from a representable complete source size; it is not
an assumed harness precondition. The proof covers all three accepted plan
variants. Rejected plans carry no completeness promise, and the typed pointer
adapter's provenance and `KnownLayout` obligations remain outside this proof.

The constructor's requirements check field alignment, the independent prefix
layout's overflow bounds, canonical encodings, and final padding bounds. These
are predicates over the mathematical construction, not assumptions that the
Rust constructor returned a correct result. Fragment operations have explicit
fit requirements; arbitrary malformed internal layout records need not succeed.
Generic size/alignment reads are explicit external data inputs, never axioms
asserting layout correctness.

`LayoutMath.lean` supplies independent unbounded size and capacity formulas.

The mathematical layout semantics proves normalization across arbitrary
nesting and metadata values. These algebraic laws do not themselves verify
a Rust layout method.

The nominal rounding wrapper decodes to `RoundingValue`, a power-of-two
alignment and bounded phase with machine-fit proofs. Ordinary representation
laws establish acceptance of every positive stored word and exact reconstruction
from that pair. Zero is rejected by the native NonZero child decoder.

`LayoutModel.lean` supplies raw observations and projections of the recursively
decoded records without function proofs. Layout models retain each field and
the unpadded flag; realizability, alignment and fit conditions remain explicit.
Generic size/alignment reads are external data inputs, not correctness axioms.
See [SEMANTICS.md](SEMANTICS.md) for the Rust correspondence premise.

The checked trailing-size and padding contracts connect machine arithmetic
to the independent recursive semantics.

Plain arithmetic clauses use mathematical word values carrying machine bounds
and, for NonZero, positivity. They coerce to `Nat` or `Int` without unwrapping
raw fields. Binding `let N : Nat := n` makes addition and remainder ordinary
unbounded mathematics. Explicit `(raw)` clauses retain the extracted scalar
operations, whose checked arithmetic returns execution `Result` values.
Operation-specific power-of-two alignment and overflow bounds remain explicit
requirements.

CI uses the default features, debug assertions, and the runner's native
`x86_64-unknown-linux-gnu` target. Local replay also supports macOS arm64. The
proofs cover all registered layout methods under their stated domains;
they do not certify other extraction configurations, a rustc implementation,
or zerocopy's pointer safety. The explicit Rust premise connects the recursive
semantics to an actual type's layout. Compiler regression tests challenge that
premise independently of the Lean algebra. Aeneas currently targets a safe Rust
subset; whole-crate unsafe verification is a separate task.

The Rust tests also compare reconstruction with rustc directly at compile
time. Concrete instantiations of ordinary, aligned, and packed `repr(C)` records
check their complete size and alignment; compilers supporting `offset_of!` also
check each field offset. Nested packed DST fixtures safely unsize real array-tail
objects, then compare their compiler size and alignment with the computed
metadata size. Those checks become compile-time assertions on Rust 1.85 and
later, while runtime comparisons remain available on the MSRV. They challenge
the correspondence premise for the tested compiler, target, and instances;
they do not replace the universal arithmetic proofs.

## Shared mathematical library

The independent Lake package at `anneal/lean` supplies the `Rust` models. This
integration uses a local path dependency and recompiles it with this project's
Lean compiler from Anneal's pinned archive. It reuses the existing
backend packages without fetching a second Mathlib tree. The golden and live
projects both import the same authored mathematical library; their extracted
Rust definitions remain independent.

The library's own `RustTests` and `RustBytesTests` targets run in the Anneal
archive build. This integration also audits the actual transitive dependencies
of its proofs, including shared-library lemmas.

## Reproduce

Install Nix, Python 3.9+, Git, and patch for a cold setup, then run from the repository
root:

```bash
bash verification/aeneas/setup.sh
bash verification/aeneas/run.sh
bash verification/aeneas/negative-controls.sh
python3 -B -m unittest discover -s verification/aeneas/tests
```

The runner builds `tools/aeneas-inline` with the pinned compiler. To run that
tool's own tests, use:

```bash
source verification/aeneas/toolchain.sh
CARGO_TARGET_DIR=target/aeneas/annotation-tool \
  cargo test --locked \
  --manifest-path tools/Cargo.toml -p aeneas-inline
```

The local failure-control command checks both models sequentially. To select
one isolated project, pass `golden-verification` or `verification`. CI runs
these two suites concurrently, waits for both, and reports both logs; either
failure fails the job.

`setup.sh` builds Anneal's existing omnibus archive and layout check, then
installs its Rust compiler, Charon, Lean, backend, and Mathlib cache together.
It builds Aeneas with the checked-in CLI-only patch using Anneal's configured
upstream package. A matching installed cache requires no Nix: setup validates
its source identity against `anneal/flake.lock`, its CLI provenance and binary
digests, and the actual tool versions. A mismatch fails without rewriting the
cached metadata. Cold setup stages and validates everything before installation.

To share a new installation across worktrees, set `AENEAS_TOOLCHAIN_CACHE_DIR`
to a writable cache directory before running `setup.sh`. Setup derives its cache
key from Anneal's lock, archive configuration and shared Lean sources, the local
patches and builders, and the host platform. It validates the complete installed
payload before reuse, then creates the requested toolchain path as a symlink to
the cache entry. For a new requested toolchain path, changed build inputs select
a new entry; changed runtime, library, or Lean artifact bytes reject reuse.
Historical installations remain
usable through `AENEAS_TOOLCHAIN_DIR`, but need a fresh setup before entering the
shared cache. A producer lock prevents concurrent setup for the same entry;
a stale lock fails with its path so the interrupted setup can be inspected.
Publication refuses an existing destination atomically. On a publication failure,
setup prints and retains the validated staging directory for inspection.

The resulting tools live in ignored `target/aeneas/toolchain`. To reuse an
existing installation with the same bundle layout, set `AENEAS_TOOLCHAIN_DIR`.
`run.sh` checks tool versions before extraction. It runs Charon with
`--preset=aeneas --sysroot default`, using Aeneas's builtin models for standard
library operations instead of regenerating a sysroot. Cargo resolves the
library's dependencies from its checked-in vendor configuration, offline and
locked. Charon is a compiler driver and selects its own Rust version; it does
not use zerocopy's ordinary Cargo wrapper or its stable/nightly aliases.

Every run replaces `target/aeneas/verification` (live extraction) and
`target/aeneas/golden-verification` (checked-in model), including their compiled
Lean artifacts. This prevents stale declarations or the other model's artifacts
from passing after source is removed or renamed. Both retain Lean sources,
handwritten models/proofs, and resolved Lake manifests for inspection; the live
directory also retains LLBC. External templates are compared but never imported
into proofs as axioms.

## Inline specifications and coverage

Annotations are outer Rust doc attributes before the decorated item. The Rust
parser owns the association, including attributes between docs and the item.
Every reserved fence is accounted for: malformed or misspelled fences, unsupported
owners, duplicate declarations, and orphaned annotations fail. Literal `#[doc]`
attributes are also supported. Annotated functions and model types cannot also
carry computed doc strings. Trait declarations may retain ordinary computed documentation alongside their
literal invariant fence. Direct `include_str!` in owner doc expressions
is rejected, including nested, qualified, and conditional invocations. Visible
reserved literal fragments in computed docs are rejected even when split across
strings. Conditional and inner doc forms with reserved fences also fail.
Unannotated computed documentation otherwise retains its ordinary Rust meaning.
Macro-produced documentation is outside the annotation language: the checker
does not expand macros or claim to inspect arbitrary external text they produce.

A trait fence declares a law on its exact extracted dictionary:

````rust
/// ```aeneas
/// invariant byte_roundtrip for self =>
///   ∀ byte, (do let encoded ← self.encode byte; self.decode encoded)
///     ⦃ result => result = byte ⦄
/// ```
trait ByteCodec { /* ... */ }
````

The generated law class uses the native trait parameters and dictionary. A
generic function specification receives law assumptions for its original
dictionary inputs, including unused bounds and retained supertraits. These
computational dictionaries remain outside Rust value decoding. This checks
selected extraction roots and their dependencies, rather than certifying every
implementation in the crate or every possible external implementation. Each
extracted local implementation requires a checked proof for that exact native
dictionary. An impl fence independently requests extraction and checking, even
when no annotated caller uses it:

````rust
unsafe_impl!(
    /// ```aeneas
    /// invariant_proof
    /// ```
    const N: usize, T: IntoBytes => IntoBytes for [T; N]
);

unsafe_impl!(u8:
    Immutable,
    /// ```aeneas
    /// invariant_proof
    /// ```
    IntoBytes,
    Unaligned,
);
````

Literal outer doc comments and literal `#[doc = "..."]` attributes inside macro
invocation arguments may contain this nameless marker. It must decorate exactly
one native positive trait impl. Grouped `unsafe_impl!` calls put proof attributes
before the individual trait; a shared proof fence copied to multiple impls
fails binding. Ordinary shared documentation may still decorate multiple impls.
Direct declaration markers remain supported with their declaration anchors.

The marker has no name or proposition: the Rust header identifies the trait,
carrier, and generic bounds. Its proof must cover every original type and const
parameter using only those bounds and their model providers. CI binds the marker
to its compiler owner. The source census retains inactive and unused source
and checks reserved annotations in macro templates too. Conditional or computed
annotations, inner annotations, misplaced annotations, and unsupported forms
fail explicitly. Computed ordinary documentation may accompany a literal
annotation; the expanded census must still account for every reserved fence. The complete native
HIR attribute census reconciles physical source origin, decoded doc text,
fragment order, and multiplicity; direct markers also retain their declaration,
signature, body, and source checks. Native evidence is recorded in
`annotation-origins.json` and the binding manifest. A missing, disabled,
mismatched, or unsupported impl fails rather than becoming an unchecked comment.
Extraction selection uses exact UTF-8 byte offsets. The proof name is `Zerocopy.Proofs.` followed by the emitted dictionary name without
its `Zerocopy.` prefix and with `_law` appended. The same rule applies to
unmarked local impls reached through other extraction roots. Removing a marker
therefore cannot weaken the proof requirement of a caller that still reaches
that impl.

A generic caller may assume the invariant for its incoming computational
dictionary: it proves a conditional theorem for any implementation that keeps
the trait's promise. It cannot prove that a future downstream impl keeps that
promise. Each selected local impl has a separate ordinary theorem discharging
the promise, and Rust's unsafe-trait contract remains the obligation of external
implementers. CI also inspects every extracted
admitted implementation method body in the original and final ASTs, even when
only the law refers to the method. Excluded provided methods cannot execute;
interface-only validators retain their required signatures but cannot be called.

This initial bridge accepts traits with only their `Self` parameter and simple
generic bounds. It compares compiler-resolved original and final type
applications, rather than matching clause ordinals. Associated types, higher
ranked bounds, transformed carrier identities, and bounds on nominal model
definitions fail closed. The compiled audit independently enumerates
implementation dictionaries and
requires the same complete set of proof obligations. Omitting or swapping a
native JSON binding cannot leave an extracted implementation unchecked.
For each impl, generated `Required.lean` contains an ordinary theorem that
applies its authored proof to the exact native dictionary obligation. Lean's
kernel checks this application. A separate audit inspects the authored theorem's
parameters and conclusion against the native impl, so an extra assumption,
specialized const parameter, or assumption of the impl's own law cannot pass
merely because the generated obligation made the same mistake. The final audit
requires every such witness and checks its proof dependency and module owner.
The native dictionary translation remains a compiler correspondence premise;
an empty dictionary alone does not distinguish Rust
types whose Lean carriers coincide. Trait laws have a compiled CI check and an
exact review projection. Development regeneration and reverse copy-back of
trait projections are unsupported and reject such edits; edit the Rust invariant
fence directly. Existing function and model editing baselines retain their
original three-module authority.

````rust
/// ```aeneas
/// spec identity_spec
///   ensures result => result = x
/// ```
fn identity<T>(x: T) -> T { x }
````

A function fence contains exactly one `spec` or `partial spec` declaration.
Only explicitly typed ghost binders are authored. The original Rust type
parameters, receiver `self`, and arguments come from the exact extracted
signature. Each original type parameter receives one `RustModel T` dictionary,
including unused and result-only parameters.

Plain clauses expose value arguments as their mathematical models. Raw clauses
expose their original Aeneas representations:

```text
requires      name : proposition
requires(raw) name : proposition
ensures       resultPattern => proposition
ensures(raw)  resultPattern => proposition
```

Every requirement is a named implication premise; later clauses can use its
proof. Requirements precede all postconditions. Every postcondition contributes
a conjunct, and all plain postconditions share one decoded output witness.
Ghost types elaborate in mathematical input scope, so `(position : Fin self.length)`
can depend on a decoded sequence. Ghosts may depend on earlier ghosts. Inputs,
ghosts, and earlier requirement names cannot be shadowed. No ghost is an argument
to the extracted function or is selected after execution.

The proposition retains the original contiguous raw-input telescope. It then
introduces modeling dictionaries, mathematical inputs, decoding equations,
ghosts, and requirements before executing the original extracted function on
its original raw arguments. A successful payload must decode, even when every
postcondition is raw or is `True`. Total specifications require successful
termination and exclude panic and divergence. Explicit `partial spec` permits
divergence while excluding panic and checking every successful return.

A type fence defines one mathematical shape and one local decoder:

````rust
/// ```aeneas
/// model AlignValue where
///   value : Nat
///   power_of_two : value.isPowerOfTwo
/// decode? self =>
///   if h : self.value.value.isPowerOfTwo then
///     some { value := self.value.value, power_of_two := h }
///   else none
/// ```
struct Align { value: NonZeroUsize }
````

The alternative `model Name := ExistingType` associates an existing mathematical
type. `decode self => term` is locally infallible; `decode? self => term` may
reject the decoded fields. Both consume the owner's generated `Fields` carrier.
The full decoder first decodes every field of a structure or the active enum
constructor, including fields ignored by the local decoder. Child rejection
rejects the entire value. There is no independent validity dictionary or predicate.
An unannotated nominal owner's model is its own `Fields` carrier. `model Name := Fields`
uses that same representation under an authored name. Different Rust owners
retain distinct default carriers; aliases inherit their carrier's model.

Native adapters carry exact scalar values and machine bounds, plus positivity
or nonzero proofs for NonZero types. Products, options, Rust results, lists,
slices, and arrays traverse their child providers and preserve their constructors
and lengths. Rust `Option.none` and Rust `Result.Err` are ordinary successfully
decoded cases; Aeneas panic/failure remains a separate execution outcome.
Unsupported opaque leaves, recursive nominal groups, indexed carriers,
trait/const generics, and escaping borrow continuations fail explicitly.
Generic shapes take mathematical type parameters: `Box.Fields TModel` needs
only its child carrier type. Authored generic model declarations bind `TModel`
for each Rust parameter `T`; decoder bodies and function specifications retain
the real dictionaries and `ModelOf T`. A field of type `Box<Child>` can therefore
declare its mathematical shape before Child's decoder exists. Slice and array
shapes retain their length bounds without a child decoder. Full decoding still
requires the actual child providers.

Each generated nominal decoder has a `decode_decompose` theorem. It characterizes
successful decoding by existential decoded child values, their child decoder
equations, and the local `decodeFields` equation. Enum cases follow their active
constructor. These witnesses remain present when a local model discards fields;
no reconstruction or injectivity assumption is required.

Automatic decoding uses directly named native/nominal providers, fixed container
combinators, and the original generic dictionary variables. Providers are selected
before decoded witnesses and ghosts and retained explicitly, so a later ghost
instance cannot redirect admission or output meaning. Ordinary instances remain
available for authored expressions and helper lemmas. No global instance-selection
comparison is part of the automatic-decoding audit.

Generated modules follow the proof-construction dependency:

```text
raw Types + ModelPrelude → ModelShapes → ModelSupport → Models → Specs + Proofs
```

`ModelShapes` declares nominal mathematical fields and inline model types in
verified extraction order. Handwritten `ModelSupport` modules can supply ordinary
Lean helpers. Lean enforces an acyclic import graph; there is no additional ban on
harmless dependencies on extracted functions. `Models` elaborates local decoders
and composes full decoders and named providers. The generated shapes, decoders,
and specifications all carry Rust source maps. Every handwritten module is
discovered and audited; generated modules are excluded from that discovery.
Handwritten module path components must be simple identifiers
(`[A-Za-z_][A-Za-z_0-9]*`); literal dots, whitespace, and quoted components in
filenames are rejected so distinct Lean Name segments cannot be conflated by the
file inventory.

These are conditional contracts over accepted representations, supplied ghosts,
and satisfied requirements. A decoder may intentionally forget observations or
reject raw values. A ghost with type `False`, or a dependent ghost with an empty
domain, makes the relevant contract vacuous. Neither the pipeline nor a decoder
proves that every Rust caller meets the domain. `DstLayout` initially keeps a
structural mathematical model, including its unpadded flag and decoded rounding
pair, without imposing a global realizable-layout requirement. Operation-specific
alignment, fit, and construction conditions remain explicit. The independently written operation expectations check both intended input
admission and promised behavior. Representation laws can be useful proof helpers;
they are not an additional universal model-certification requirement.

The fully qualified model application is generated and cannot be supplied in
Rust. Charon's root identity, exact source body, source path, and signature must
match the annotation, including inherent Self types and inactive `cfg`
alternatives. Discovery retains exact inspected source snapshots; later digest,
binding, and assembly steps reject changes to any inspected input. The source
digest includes all inspected crate Rust sources and reserved-fence candidates. Every
contents-bearing Charon-local file must agree with its inspected snapshot, so an
unchanged caller cannot hide a changed dependency. Pinned external `/rustc` files
without source contents remain within the translation premise.
The elaborated call must pass exactly its original Rust input
variables, with no swapping, coercion, or substitution. Introduced signatures are
inspectable in the generated Lean propositions and native editor.

Function and nominal-model annotations determine the extraction roots. Trait
invariants remain required annotations but bind dictionaries reached from those
roots; a trait name is not itself a root, because that would also select default
method bodies outside the supported subset. A present trait invariant whose
dictionary is absent from extraction still fails binding. Removing an annotation
and its associated proof intentionally removes that claim from the checked set;
the source and generated golden changes make the reduced coverage reviewable.
There is no separately maintained function or type coverage roster. Nominal
types used by extracted functions retain their exact source mapping and
structural model checks, including unannotated dependency types.

Model names, theorem identities, filenames, and dependency edges are derived
from the present annotations and verified extraction. Discovery inspects all
`zerocopy/src` Rust sources and reserved-fence candidates elsewhere in the
repository, except generated and vendored directories. A Rust lexer distinguishes
comments from strings and `syn` establishes ownership before conditional
compilation. A present fence on an unsupported owner, including one hidden in a
macro, fails discovery; unannotated macros and impls keep their ordinary Rust
meaning. Every function extraction root must match a present function annotation.

No parser can recognize every informal prose claim as a proof. The `aeneas`
fence is the reserved CI-checked convention. Near-miss guard detection protects
that convention without treating all mathematical prose as annotations. CI
checks every present specification on both the golden and live models so an
owned fence cannot escape proof checking or the compiled binding and axiom audits.

## `IntoBytes` initialization laws

The `IntoBytes` fence in [`lib.rs`](../../zerocopy/src/lib.rs) requires every
accepted physical representation byte to be initialized. A byte in
[`Rust.Storage`](../../anneal/lean/Rust/Storage.lean) is either initialized with
an eight-bit value or uninitialized. A physical decoder has a fixed width and
a successful run consumes exactly that width. `RustModel.initializedRepresentation`
requires an available physical decoder and initialization over its entire
accepted domain. Absence is `False`; rejection by the library's mathematical
`RustModel.decode` cannot reduce this domain.

There are 59 authored implementation markers: `()`, `bool`, `char`; all twelve
signed/unsigned integer carriers; all twelve corresponding `NonZero` carriers
and their `Option` forms; `PhantomData`; arrays; `Wrapping`, `ManuallyDrop`,
`Cell`, `UnsafeCell`, `ReadOnly`, `Unalign`; and all twelve byteorder wrappers.
[The scope inventory](LOWERING_AUDIT.md#exact-authored-implementation-scope)
retains their exact generic bounds, configuration branches, and deferred impls.
The default library build selects the handwritten `Unalign` and byteorder
implementations; their derive/test alternatives remain deferred. Native floats,
slices, `str`, atomics, SIMD, and other derive-generated impls remain outside
this implementation-law scope.

Integer physical decoders assemble initialized bytes in the extraction target's
little-endian order, then interpret signed words in two's complement. Admission
requires a little-endian 64-bit target, so pointer-sized words occupy eight
bytes. Nonzero decoders reject zero as decoder failure. The specialized
`Option<NonZero<_>>` decoder admits all initialized underlying integer patterns:
zero becomes the Rust payload `None`, nonzero becomes `Some`. Outer decoding
failure stays a failure. The character decoder rejects surrogates and values
above `0x10ffff`. No general optional-value or struct layout is inferred.

Array decoding splits complete element representations into consecutive chunks
and requires an empty final remainder. `arrayDecoder_initialized` proves the
law for every count under the actual element decoder's law. Recursion counts
elements, so the same rule covers empty arrays, positive counts of zero-byte
elements, and nested arrays. Padding within an element remains the element
law's obligation. Wrapper decoders preserve the actual child's failures and
initialization law. Generic `?Sized` impl bounds are retained; a supplied
physical provider for an unsized value must also carry its applicable metadata
and representation width. These conditional laws supply no universal DST
representation model.

The byteorder structs have transparent byte-array storage plus an empty
`PhantomData` field. In particular, `F32` and `F64` use `[u8; 4]` and `[u8; 8]`;
their initialization laws require no native floating-point representation model.
`PhantomData<T>` uses its explicit empty raw constructor, without a stored `T`
or a model of `T`. This differs from inventing a value based on size zero or a
Lean `Inhabited` instance. Structural mathematical models receive no physical
decoder by default.

[`EmptyConstructionTests.lean`](lean/EmptyConstructionTests.lean) checks that
empty-byte construction without a physical provider fails, including for an
uninhabited raw type. An explicit empty physical decoder can produce a
unit-like raw token, but its full provider rejects that token when the modeled
external-state condition is false. Total and partial correctness both reject
this `.fail .undef` result even with postcondition `True`. Empty storage proves
neither Rust constructor permission nor an external library invariant.

Applying these Lean laws to Rust requires explicit correspondence: the
physical decoder has the correct width and admits exactly the applicable
language-valid representations with their corresponding raw values. The
[versioned language and standard-library premises](LOWERING_AUDIT.md#decoder-correspondence-premises)
record what each builtin interpretation consumes and their compatibility trust.
Initialization theorems alone cannot prove that correspondence: a decoder
rejecting all inputs also satisfies initialization vacuously.

These are conditional initialization laws for the exact native trait dictionaries.
They do not prove every method body, runtime storage, typed transfers, aliasing,
pointer provenance, destruction, or general Rust UB-freedom.
`IntoBytes::as_bytes` retains its Rust safety argument; its pointer implementation
is outside these laws. See [LOWERING_AUDIT.md](LOWERING_AUDIT.md) for the remaining
lowering boundaries.

## `FromBytes`, `FromZeros`, and owned zero construction

The `FromBytes` law requires every fully initialized byte sequence of the
physical decoder's exact width to produce both a language-valid raw value and
a mathematical value. The `FromZeros` law requires the same two stages for the
all-zero sequence. Both stages use one `RustModel` provider; a physical success
cannot bypass an optional library invariant. A missing physical decoder fails
both laws. These definitions permit padding: neither law promises that a typed
copy preserves the initialized padding bytes used for construction.

Nine `invariant_proof` markers cover `()` and `u8`/`u32` for both traits,
`bool` for `FromZeros`, and the two generic array impls. Array proofs compose
the actual element decoder and its law, including empty arrays and zero-sized
elements. The completeness lemma also derives the zero law from a `FromBytes`
law. Negative Lean examples distinguish Boolean zero validity from Boolean
validity for every byte, and reject zero construction of nonzero integers or a
value rejected by its library decoder.

The specification on the existing `FromZeros::new_zeroed` default method proves
its actual body under the exact enclosing trait's law. Its stdlib boundary,
`core::mem::zeroed`, decodes zero storage before returning a typed value;
rejection is forbidden execution, even for a `True` postcondition. The compiled
audit checks this complete definition, not just successful examples. An
independent required contract states the physical and mathematical decoding
facts without using the primitive's implementation.

Aeneas normally has no model dictionary in the computation. The downstream
`native_models` elaborator retains a provider only in generic definitions
whose bodies need this boundary. Original Rust arguments remain in their exact
order, followed by implicit semantic providers; anonymous lets retain unused
arguments without changing the body. Contracts reuse those same providers.
They cannot quantify a different decoder after choosing an execution outcome.
The native-input audit distinguishes this checked suffix from source arguments.

Charon can erase the unused enclosing Self dictionary from a default body.
Source and compiler evidence identify its trait and method slot before that
erasure; the specification receives that exact trait dictionary and law as
premises. These are specification parameters, not replacements for Rust
arguments. Separately, required `TryFromBytes::is_safe` fields retain their
native signatures but have no execution model. Carrying those dictionaries is
allowed; calling an unmodeled validator is rejected at admission. Its opaque
`Ptr` carrier supplies no construction, layout, provenance, or validity facts.

As with `IntoBytes`, applying these proofs to Rust assumes the physical decoder
has the correct Rust width and language meaning. The primitive and array
interpretations have explicit Reference premises; compiler assertions challenge
the concrete widths. A generic provider is a supplied interpretation, not a
proof of an arbitrary downstream type's representation. This example covers
resource-free owned zero construction, not pointer access, external-state
invariants, destructors, or every `FromBytes`/`FromZeros` impl.

## Native Lean proofs and independent checks

`Specs.lean` is generated from the Rust comments in a fixed context containing
the extracted model and mathematical vocabulary. Each `Zerocopy.Specs.*` is a
transparent proposition. The module is elaborated before proof modules are
imported, so proof declarations cannot change what the comment means.

Handwritten proofs are ordinary checked-in `.lean` modules. Their theorem types
refer directly to generated propositions rather than restating them:

```lean
theorem example_spec : Zerocopy.Specs.example_spec := by
  intro input h
  ...
```

Changing the Rust specification changes this theorem's goal. An old proof is
accepted only when Lean still establishes that goal. Normal imports and Lean
declaration order assemble proofs. There are no proof templates, insertion
slots, or hand-maintained dependency lists.

Each function annotation requires its canonical exported proof and an independent
proposition in `Obligations.lean`. Missing canonical proofs, stale `Specs`
references, duplicate declarations, and unrelated required theorem types fail.
Additional helper theorems are allowed in the configured proof modules. The
required checks prove that the inline contract implies its independently authored
expectation for **every execution outcome**, before specializing that implication
to the proved implementation. The generated `Specs.<name>_contract` family
abstracts only the execution node; the audit checks that every original premise,
decoding check, and postcondition remains unchanged. Handwritten
`Obligations.<name>_contract` families independently state the expected domain and
result. Their concrete `Obligations.<name>` aliases are checked to specialize the
same families to the original calls.

This comparison cannot pass merely because a weaker specification and the
expected behavior happen to hold for the current implementation. It also catches
an unexpectedly narrowed domain. The generated checks retain both an
`<name>_adequate` implication and an `<name>_checked` concrete theorem for kernel
and axiom audits. Every canonical theorem must directly name its inline `Specs`
proposition; the audit requires both independent witnesses in the generated checks
module. It derives required theorems from compiled specifications, without a
separate generated roster. The expectations are reviewable sanity checks on
specification meaning, not an additional axiom or proof language.

The audit also compares the existing verified Rust-to-model mapping in
`bindings.json` with the functions actually called by compiled specifications
declared in `Specs`. Every mapped function must have exactly one such
specification; missing, extra, or repeated functions fail. Each specification
in turn requires its canonical theorem and independent required theorem.
The same versioned table records every extracted nominal owner's source,
raw carrier, Fields carrier, mathematical type, decoder, and provider. The compiled
audit checks those identities and their generated-module ownership in both
directions, independently scans raw nominal types, and rejects missing or extra
provider registrations. This reuses one verified table without another coverage roster.

For cast validation and
exact-size metadata, the required outcomes spell out error priority, split
positions, exact size, and greatest-fitting metadata independently of the
predicates used by the inline specs. `OutcomeTests.lean` pins distinguishing
fixed-size, suffix-alignment, and padded-size plateau examples.
`LayoutModelDomainTests.lean` also establishes concrete admitted constructor
inputs and exact views for an ordinary record and a nested packed DST. These
bounded examples guard against vacuous preconditions; they do not establish
that every Rust type meets the construction domain.

`Check.lean` derives dependencies from elaborated theorem types and terms,
following helpers across handwritten modules, including private helpers, and
writes `proof-dependencies.json` in each proof workspace. It imports and audits all
declarations from every handwritten Lean module, including unused auxiliary
modules, together with the model, vocabulary, obligations, and generated
specifications. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted.
The explicit data-only Rust layout inputs documented in `SEMANTICS.md`
are also permitted. Models with generic alignment reads must provide both
data inputs with their exact signatures; the audit also checks that generic
size/alignment reads use those inputs and that `Usize` size uses the pointer
width. These checks pin the declared external interpretation; correspondence
to the actual Rust ABI remains an explicit premise.
New axioms, `sorryAx`, and native evaluator proof axioms fail.

Callers reuse ordinary exported theorems, either explicitly with `step with` or
through Aeneas's existing `step` registration. For a theorem whose type is a
transparent `Specs` proposition, `register_spec_step theorem_name` supplies a
kernel-checked alias with the expanded type for that registry. The canonical
theorem keeps its ordinary `Specs` type. Golden caller proofs use golden
callee theorems; live caller proofs use live callee theorems. Both models are
built in separate fresh workspaces from the same handwritten source, never
from shared compiled proofs or substituted model definitions. Handwritten
modules must not create import cycles through generated `Required` or `Check`.

## Decoder proof completion

Model fields declare ordinary Lean constraints. A decoder can supply only its
data and use native `..` to omit proof fields:

```lean
model RoundingValue where
  align : Nat
  phase : Nat
  align_pow2 : align.isPowerOfTwo
  phase_lt : phase < align
  fits : align + phase ≤ Usize.max
decode self =>
  let word := self._0.value
  let align := 2 ^ Nat.log2 word
  { align := align, phase := word - align, .. }
```

Both `decode` and `decode?` implicitly use `model_value` completion on the whole
body; outside decoders write `model_value { ... , .. }` explicitly. Native
elaboration creates the omitted-field goals, so no field discovery or defaults
are attached to model declarations. Every remaining goal must be a proposition.
Missing data (including a field of type `Prop`) is an error. Proof search uses
ordinary assumptions, arithmetic, and shared logarithm/word-bound facts with a
maximum of 100000 Lean heartbeats; explicit field proofs and complete `by`
bodies retain their ordinary meaning.

Proofs are completed in their own local contexts, including `let` bindings and
conditional hypotheses, even in nested records or `some { ... , .. }`. An
unproved constraint fails compilation, including in a fallible decoder; it
never becomes `none` or changes the decoder's domain. Ordinary proof fields
ensure that chosen data satisfy the model constraints. The independent meaning
and admission laws still check what those data describe and which raw values
are accepted. `ModelCompletionTests.lean` covers both behaviors.

## Development

Run `bash verification/aeneas/dev.sh` once to prepare the stable development
project from the checked-in golden model. Preparation first extracts current
Rust to bind trait dictionaries, native layouts, and specifications; it does not
check proofs. If the golden definitions differ from that extraction, use
`--live` to prepare with the current model. Edit its Lean files with native editor
support, then use `--check` for quick feedback. An existing project is checked
in place: this command does not rerun extraction, regenerate annotations, clean
all proofs, or perform the complete audit. First use prepares the project if it
has not been initialized. Add native module names to narrow the work:

```sh
bash verification/aeneas/dev.sh --check Proofs.Util
```

These checks are explicitly **provisional**. Normal Lake traces follow changes
to Lean imports, but the Rust extraction may be stale and a selected module does
not establish coverage of other specifications or audit all proof assumptions.
Use `--refresh` to extract current Rust and regenerate specifications with the
golden model, or `--live` to use the freshly extracted model. Either can be
combined with `--check`. Generation computes the complete
output but preserves unchanged files' timestamps, avoiding needless local
recompilation. Edited inline projections remain protected against regeneration.

After copying annotation edits back to Rust, run the complete final check:

```sh
bash verification/aeneas/dev.sh --final
# Equivalent to bash verification/aeneas/run.sh, the command used by CI.
```

The final check creates fresh projects, extracts and admits current Rust,
compares goldens, rebuilds every mutable proof source against **both** models,
and runs the complete binding, trait, dependency, and axiom audits. It has no
module-selection option and never accepts a development check as evidence.

The editor project keeps handwritten proof modules at their checked-in paths
and generates the extraction, `ModelShapes.lean`, `Models.lean`, and `Specs.lean`.
Source maps connect specification diagnostics to Rust comments; proof diagnostics
point to checked-in Lean sources.

Development regeneration records a version 2 baseline of the three inline
projections and their owned Rust doc payloads, and refuses to overwrite local
edits before extraction or project writes. Edit only the marked authored
regions: specifications in `Specs`, model shapes in `ModelShapes`, and the
`decode`/`decode?` clause in `Models`. A type's shape and decoder copy back
together. Generated imports, `for` targets, and derive/check commands remain
unchanged. Handwritten proofs continue to be edited at their real paths.

Preview the exact Rust diff, then apply it for one full Rust owner:

```sh
bash verification/aeneas/dev.sh --copy-back zerocopy::util::padding_needed_for --dry-run
bash verification/aeneas/dev.sh --copy-back zerocopy::util::padding_needed_for
```

Copy-back reads the existing project without regeneration, extraction, or
builds, and cannot be combined with preparation or checking options. Preview writes
nothing. Apply updates one annotation in one Rust file, preserving its doc
indentation, newline style, other source bytes, and file permissions. It accepts
only contiguous, uniformly indented `///` fences; block comments and literal
doc attributes remain readable but require manual editing. The saved source
snapshot and owned spans authorize the edit; source maps are diagnostic only.
Edits outside authored regions and changes to the original Rust file fail
without writes. Authored edits must retain the formatting produced by generation;
copy-back rejects formatting that would be discarded on the next regeneration. Other owners' edits stay protected until copied back in turn;
then rerun the development command to regenerate from Rust.

Rust and its projection baseline are replaced separately. If interruption
occurs after writing Rust, rerun the same copy-back command with unchanged
Lean projections: it recognizes the exact planned Rust result and finishes
updating the baseline. Keep the baseline and edited projections together for
this recovery. There is no force option.

Older version 1 baselines still protect edited projections, but cannot copy
back automatically. Clean regeneration upgrades them. For unbaselined or
older edited projections, preserve the files and manually move authored
fragments into the Rust doc fences before establishing a clean baseline.
Unannotated structural models have no authored fragment; edit their Rust type
or the generator.

After a Lake build, inspect an effective compiled specification with:

```sh
python3 -B verification/aeneas/workspace.py inspect verification/aeneas/lean \
  --root "$PWD" --spec encoding_components_spec
```

This reads compiled declarations without running another build. It displays the
actual proposition, original raw call, selected input/result providers and
decoding equations, total/partial WP judgment, all binder types, compiled axiom
dependencies, existing proof graph, and available extraction metadata. Mathematical
witnesses and ghosts are shown as binders; proposition-valued ghosts and named
requirements have the same universal meaning and are displayed together. Rust/ABI
correspondence assumptions are documented in `SEMANTICS.md` when that document is
present; the scope and translation trust boundary are described above. Missing
extraction provenance is reported as unavailable; legacy LLBC metadata is explicitly uncertified against
compiled imports. An edited source may differ from its compiled declaration;
rebuild the relevant modules before using inspection as development feedback. Only the final check certifies the current checkout. This command
provides inspection, not a new verification result.

Edit a specification in Rust and run the development command again to refresh
its generated proposition. Edit its proof directly in Lean. No proof copying
back to Rust is required. This development cache is for iteration; CI always
regenerates specifications and builds both models in fresh isolated projects.

## Mathematical views and indexed loops

### Arithmetic, mathematical views, and indexed loops

Checked addition, subtraction, and multiplication already have upstream
`step_pure` specifications. Use `step as ⟨result, facts⟩` and split the `Option`
result to obtain both the exact successful value and the overflow condition.
`SupportTests.lean` exercises all inputs, including overflow. Layout proofs use
these registrations directly, without naming bitvector specification lemmas.

A contract may express equality through a pure mathematical view:

```lean
theorem operation_spec (input : Input) (h : valid input) :
    operation input ⦃ result =>
      view result = mathematicalOperation (view input) ∧ canonical result ⦄ := by
  ...
```

This ordinary theorem states the existing total WP postcondition directly.
A view-only theorem states just the view equality. Partial correctness uses
`⦄div` in place of `⦄`: it explicitly permits divergence and still excludes
failure. These are Aeneas's existing specification operators. Use `WP.spec_mono`
to adapt an existing result specification to a view, and register useful caller
specifications with `attribute [step] operation_spec`. The existing Aeneas
registry then lets callers use `step` without specifying the theorem manually.

`AeneasContracts.indexed_loop_spec` specializes Aeneas's `loop.spec_decr_nat`
to a state and `Usize` index. Supply a view, the mathematical value of each
prefix, and a representation invariant. Each continuing body step must advance
the index by
exactly one and establish the next prefix; a completed step must be at the
length. The adapter supplies bounds and the decreasing `length - index`
termination measure. The record constructor instantiates this rule; its body
proof still establishes the arithmetic bounds needed to avoid Rust overflow.
`SupportTests.lean` contains a smaller independent example.

The specification syntax, examples, and required-contract proof terms
participate in the axiom audit. Failure controls challenge an incorrect view,
divergence under a total view contract, a stationary loop index, an incorrect
prefix step, and continuing past the loop bound.

## Updating models and fuzzy comparison

`golden/` stores all four complete generated Aeneas modules, including types,
function bodies, trait dictionaries, constants, and external templates. There
are no per-function model slots or separate scaffolding. Handwritten external
models remain under `lean/Zerocopy/` and templates are never imported as axioms.

Regenerate the checked-in output with:

```bash
bash verification/aeneas/run.sh --update-goldens
```

The command extracts live output and checks its proofs and independent required
propositions before updating the complete generated module set. It then checks
comparison and both model builds. Rust comments, handwritten proofs, and
executable Rust are preserved. Review and commit the changed goldens alongside
the Rust or pin changes that prompted them. Ordinary CI never updates them.

To add coverage, add the fenced specification, its ordinary Lean theorem, and an
independent required proposition.
Regenerate the complete goldens. Each annotation's model declaration is checked
in the complete generated modules; missing or duplicate declarations fail.

Fuzzy comparison ignores line and nested block comments, including source
locations, empty nonliteral lines, and trailing horizontal whitespace outside
literals. It preserves code, indentation, nonempty line boundaries, interior
whitespace, and string/character/quoted-identifier contents. Unsupported raw or
interpolated strings and malformed comments/literals fail closed. Missing or
additional generated files, changes to external-template signatures, and code
changes fail with a normalized diff and require regeneration.

CI compiles the checked-in model and the unmodified live model in separate fresh
Lake workspaces. Both must prove all inline specifications and composition
corollaries and pass required checks and the complete axiom audit. The normalized
text is used only for comparison, never compilation. This independently checks
that accepted differences preserve the proved properties; it does not by itself
prove full semantic equivalence beyond those properties.

## Pins and upgrade procedure

`anneal/flake.nix` and its lock are the authoritative upstream pin. The existing
omnibus archive records the full Aeneas source revision and NAR hash, Charon
revision, and compatible Rust and Lean versions. `toolchain.sh` reads this
metadata and checks its source identities against the lock; it contains no
independent upstream versions, release digests, or download map.
The checked-in patch exposes the existing `Config.use_tuple_structs` option as
`-use-tuple-structs false`, which our extraction selects. The upstream default
remains unchanged. The locked source identity, checked patch digest, distinct tool
version, and
`tests/nominal-tuples.sh` keep this change reproducible and check constructors,
projections, patterns, updates, and default-mode compatibility.
Its `lake-manifest.json` pins Mathlib and transitive dependencies; the generated
proof workspace shares those fetched dependencies through path entries instead
of resolving a second copy.

Upgrade Anneal's existing input and regenerate its fixed-output hashes together.
Validate all supported archive platforms, then rebuild this consumer's CLI patch
and run extraction and all proofs from fresh output. Review new
external templates, the generated helper bodies, proof statements, and axiom
results. Remove or adapt the naming workaround only after inspecting the new
output. Do not pair Aeneas with an independently selected Charon nightly.

## Trust boundary and failure checks

These are Lean theorems about generated functions. Transferring them to Rust
requires the following external correspondence premises, which this CI job
records but does not formally prove:

- Rust MIR generation and Charon's LLBC extraction preserve these selected
  functions' semantics for the pinned configuration.
- Aeneas's translation and the pinned integer, comparison, wrapping-subtraction,
  checked-addition, bitwise, and assertion models represent those Rust
  operations faithfully. The translated layout records and variants represent
  their stored fields, not physical Rust layout or niche encoding.
- The handwritten `NonZero` wrapper represents its stored value;
  `NonZero::get` succeeds with that value and `NonZeroUsizeInner::clone`
  succeeds with a copy. These models abstract values, not niche encoding,
  layout, validity, or memory operations. The wrapper over-approximates valid
  Rust values by admitting zero; the generated conditional contracts assume
  successful recursive decoding of inputs and prove it for returned values.
  This introduces no axiom asserting that every modeled wrapper is nonzero.
- The guarded `NonZeroUsize::new_unchecked` interpretation returns its input
  in the raw wrapper only when that input is nonzero. Zero and unsupported
  native types produce forbidden execution (`fail undef`), including when the
  result is ignored. Admission checks the original Rust `usize` instantiation
  and its lifted `NonZeroUsizeInner` argument; the compiled audit compares the
  whole definition independently of successful-input proofs. The pinned std
  contract (`core/src/num/nonzero.rs`, nightly-2026-09-17, lines 394–399) says
  that zero causes undefined behavior and requires a nonzero argument. Its
  Rust-to-model correspondence remains a primitive boundary premise. The
  `divide_by_unaligned` body stays extracted: the exact dictionary's law proves
  alignment one, hence `1 / alignment = 1`, establishing constructor safety
  before the final checked division. The concrete `u8` caller discharges its
  implementation law. These proofs concern values and arithmetic, not memory.
- The external `usize::unchecked_mul` and `usize::unchecked_add` models
  return the exact product and sum on non-overflowing inputs. Their Lean
  definitions use checked arithmetic, and every use proves both results fit.
  They claim no Rust behavior outside that domain. The cast composition
  harness derives these bounds from successful plan selection and a
  representable source size, and compares complete source/destination sizes
  using the independent remainder-based reference. Pointer provenance,
  reference validity, and `KnownLayout` implementations remain outside this
  numerical proof.
- Lean's kernel, its standard logic axioms, and the imported proof artifacts
  check the encoded propositions correctly. Release checksums establish
  artifact identity, not a proof of compiler or model correctness.

Failure controls challenge missing annotations and proofs, orphaned proofs,
incorrect binding and parameter order, malformed specifications, admitted
proofs, unrelated theorem types, changed generated callees, and comments or
whitespace accepted by fuzzy comparison. Each model must pass the same controls.
Control families are selected from available model capabilities. Once selected,
a missing fixture or mutation target is an error. Semantic model mutations must
compile before their proof failures count as evidence; malformed mutants fail
the control run. Valid weaker contracts and weakened outcome predicates must
also be rejected. Controls edit and restore scratch workspaces, then recheck the
original results.

Extraction rejects warnings, translation errors, missing artifacts, and LLBC
whose `has_errors` is not exactly `false`, even when Charon exits zero.
`prepare.py` repairs one pinned Aeneas naming collision: `ZeroablePrimitive` has
two `Copy` parent dictionaries that Aeneas names `markerCopyInst`. The second
projection and initializer are renamed `innerCopyInst`; dictionary types and
values are preserved and no function body changes. Unexpected output fails.

## Research used

The upstream [Aeneas README](https://github.com/AeneasVerif/aeneas) describes the
Charon-to-LLBC-to-Lean pipeline, required compatible pins, external model
workflow, and safe-subset limitations. The repository's `reference` branch
provided useful prior evidence:

- [Compatible bundle drift](https://github.com/google/zerocopy/blob/ba4556c30835b56d108b0a6854a760bccf8438c5/reports/aeneas-compatible-bundle-source-drift-2026-09-30/REPORT.md)
  identifies the newer Lean module output and the need to resolve Charon from
  Aeneas's pin rather than release dates.
- [External models](https://github.com/google/zerocopy/blob/ba4556c30835b56d108b0a6854a760bccf8438c5/reports/aeneas-external-models-nightly-2026-06-03/REPORT.md)
  explains the generated templates and the semantic boundary of model
  registrations.
- [Whole-library Charon extraction](https://github.com/google/zerocopy/blob/ba4556c30835b56d108b0a6854a760bccf8438c5/reports/charon-zerocopy-library-repeat-order-nightly-2026-05-31/REPORT.md)
  observed successful process exits with `has_errors: true`, supporting the
  explicit LLBC completeness check.

Those older experiments are not assumed to describe the current release's
runtime. This integration was validated with the pinned October 1 bundle and
fresh translations of the current checkout.

## Shared integer and byte mathematics

`anneal/lean/Rust/Bytes.lean` defines unsigned byte encoding and decoding with
ordinary natural-number arithmetic, independently of Aeneas. It proves lengths,
bounds, truncation, and round trips for arbitrary byte counts. Anneal v1, v2,
and this integration share that package; each consumer supplies its own bridge
to the representation it verifies.

The inline contracts in `byteorder::verification` exercise the production
U16/U32 `from_bytes`, `get`, `new`, `Into`, and `set` paths for both byte orders.
`BytesAdapter.lean` connects Aeneas's bit-vector codecs with the shared radix-256
model. Independent required contracts spell out positional byte sums and each
output digit, so the same decoder helper cannot define both sides of the check.
There are no extra preconditions on these fixed arrays or unsigned integers.
This trial covers value computations; it does not verify signed conversions,
floating-point operations, pointer access, or the full byteorder API.

The extracted ByteOrder trait dictionaries carry formatting methods even when
these computations never format anything. Aeneas leaves `Formatter` as an
opaque `Type`. The axiom audit admits that exact monomorphic data carrier after
checking its signature; no formatting proposition or behavior is assumed. A
change to a proposition or a function fails the audit. The PhantomData model
likewise records its zero runtime fields, with a Lean shape theorem that fails
if extraction adds fields; it makes no ownership or provenance claim.
