<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.

This file may not be copied, modified, or distributed except according to
those terms. -->

# Aeneas integration: design and development plan

This document records the unified design, the immediate implementation work,
and the decisions deliberately deferred until more use supplies evidence.
`README.md` describes commands and current behavior; `SEMANTICS.md` describes
the independent layout semantics and explicit Rust correspondence premise.
Changes to this plan must preserve the stated claims or identify an
intentional change to their domain or observations. Implementation status
belongs with the relevant item below rather than in an unrelated backlog.

## Purpose and scope

The integration proves conditional functional behavior of selected, actual
zerocopy functions using their Aeneas extractions. An inline Rust
specification must have unambiguous ownership, refer to the original extracted
function and arguments, and receive a checked ordinary Lean proof. The same
claims must hold independently for checked-in generated goldens and fresh
extraction.

The mathematical model is a common language for operation contracts.
Operations give that language its behavioral meaning. Decoding determines
interpretation and admission; it is an implementation detail that proofs may
unfold or describe with reusable lemmas. There is no universal requirement for
an encoder, injectivity, canonical raw representation, round trips, or a
separately authored representation relation. A map model may forget its seed.
A model must retain enough information for the operations and observations we
actually promise.

These are conditional contracts. They do not establish that every safe caller
meets preconditions, that every constructor or mutation preserves an
invariant, or that pointer operations are free from undefined behavior.
Anneal's stronger claim would need those additional obligations. Numerical
layout proofs use the explicit Rust premise rather than a formal proof of
rustc.

## Semantic core

`RustModel Raw` contains only a mathematical `Model` and `decode : Raw ->
Option Model`. Successful decoding defines admission. Mathematical values can
carry proof fields, so their constraints follow from construction.

The complete decoder recursively decodes every field before applying a local
decoder, including fields whose information the local model discards. Enum
decoding visits the selected payload. An infallible local decoder adds no
restriction beyond child admission; a fallible one defines additional
admission. Unannotated supported types receive structural models. Missing or
unsupported models fail explicitly rather than receiving a universal trivial
fallback.

Model shapes depend only on mathematical child types. Full providers depend on
the actual child decoders. This separates shapes, ordinary support lemmas, and
decoder construction without requiring another public typeclass. Distinct raw
nominal types remain distinct through the pinned Aeneas tuple-newtype option.

Function annotations precede their Rust owner and contain exactly one `spec`
or `partial spec`. Original source type parameters, trait dictionaries, and
value arguments are
inferred from the verified extraction. Computational trait dictionaries keep
Aeneas's original types. They are not decoded as stored Rust values. Annotated
traits generate separate proposition classes about those exact dictionaries;
generic specifications receive their laws, including laws of retained parent
dictionaries. Every extracted local implementation must provide an ordinary
checked theorem, assuming only laws of its original dictionary inputs. Every
original type parameter receives
a modeling dictionary, including unused and result-only parameters. Automatic
providers are fixed before decoded witnesses, ghosts, requirements, and
authored instances.

Plain clauses expose decoded value inputs and outputs. `(raw)` clauses expose
their original representations. Requirements are successive named premises;
postconditions are conjunctive and share one output witness. A successful raw
payload must decode even for raw-only or `True` postconditions. Execution
always uses the original raw arguments.

Ghosts elaborate in mathematical input scope and may depend on previous
ghosts. They are universally quantified premises fixed for the contract, not
arguments to the extracted function or choices made after execution. Their
types affect coverage: `Fin xs.length` admits no position for an empty list;
`False` admits no instance at all. Such domains are allowed when intended and
must not conceal a broader promised domain.

Total contracts require successful termination and exclude panic and
divergence. Explicit partial contracts permit divergence, exclude panic, and
check every successful return. Decoder rejection, Rust `Option`/`Result`
payloads, and Aeneas execution failure remain distinct.

Decoder-scoped completion uses native record `..` and ordinary kernel-checked
proof search for omitted propositions. Missing data requires ordinary
inference or explicit author input. Explicit proofs remain available. Failure,
including inside a fallible decoder, is a compilation error and never becomes
rejection. There is no per-model tactic registry unless concrete repeated
needs justify it.

## Proofs and independent contract checks

The canonical theorem targets the transparent generated `Specs` proposition.
Proofs and helper lemmas are ordinary checked-in Lean modules. Native imports,
declaration order, and Aeneas theorem registration provide assembly. The
compiled proof graph reports dependencies; it does not dictate a proof
structure or a Rust call graph. Raw lemmas remain useful for broad domains and
intermediate representations. There is no requirement to decode after every
assignment.

Handwritten `Obligations` are independently expressed behavioral expectations.
Their role is specification adequacy and regression protection for promised
domains and observations, not a second universal certification of each model.
When a spec already expresses the complete intended claim, duplication
supplies additional checking evidence rather than another kind of correctness
guarantee.

The independent comparison must abstract an execution outcome. For original
arguments `args` and arbitrary `run : Result RawOutput`, it must establish
`AuthoredAt args run -> RequiredAt args run`. Separately, the canonical proof
establishes `AuthoredAt args (extractedFunction args)`. The outcome precedes
modeling dictionaries, decoded witnesses, ghosts, and requirements so all
instances concern one execution.

Comparing concrete propositions permits an adapter to ignore the authored spec
and independently reprove the implementation. Concrete equivalence has the
same problem when both propositions are true. An arbitrary outcome exposes
weak postconditions, accidental partial correctness, and unintended domain
narrowing. The required input domain must be independently maintained where
admission is part of the promise; sharing a changed decoder on both sides can
be vacuous.

The original execution node and argument prefix remain audited. Its abstracted
WP node must use the fresh outcome, and specialization must be exactly the
original spec. A family that ignores its outcome cannot pass merely because
its concrete specialization agrees. The independently authored family remains
ordinary Lean, with a checked connection to the concrete required proposition.

Existing required guarantees must survive migrations. New requirements or
decoder restrictions that narrow a theorem's domain are semantic changes and
need explicit review. Useful broader raw theorems can be preserved as helpers.
Representation and admission lemmas are ordinary tools for proving operation
contracts or their adequacy; their existence is not a universal type-level
duty.

## Implementation organization

Share a rule when one fact determines its result; retain separate observations
when their independence supplies evidence. For example, a nominal Rust owner's
name determines its generated `Fields`, `decode`, and `aeneasModel` names. The
registry stores the owner once and computes those names. Decoder construction
and its decomposition theorem use the same constructor traversal, while their
different field operations remain explicit: one sequences decoding and the
other states existential witnesses and decoder equations.

The source tools likewise normalize an extracted type's unique source owner
once and append a generated line with its diagnostic location in one operation.
Copy-back planning reuses region parses only after complete baseline validation.
The editor and CI share the generated-module roster, and failure controls share
one roster for fixture preflight and cleanup. These choices remove independent
state and repeated decisions without adding a new public abstraction.

The Rust parser and comment audit remain separate, as do authored specs and
independent expectations. Merging those checks would remove the evidence that
catches a missed annotation or weakened claim. Comments explain both the shared
mechanisms and these deliberate boundaries, starting with the reader overview
in `README.md` and continuing beside the relevant implementation.

## Extraction, CI, and development

Application behavior can be stated in ordinary Rust. An independent reference
calculation and an assertion harness are extracted together with the production
functions they call. A total `ensures _ => True` on the harness requires successful
termination, so its assertions prove the comparison even though the written
postcondition says nothing about the unit result. Guards are part of this visible
claim: returning early makes no comparison for that input. Reviewers must inspect
guards, reference independence, and complete result comparisons when reconstructing
the intended guarantee. A proof does not establish that the reference implements
rustc; the explicit Rust premise and compiler regression tests remain necessary.

Every present annotation uses the same mandatory checking path. A harness needs
no special root declaration, and a separate coverage roster would add a second
place for the reviewer to reconstruct the checked set. Removing an annotation
and its proof intentionally reduces that set. Independent expected propositions
still challenge contract elaboration and preserve existing helper domains; they
do not supply hidden application claims that a Rust harness needs to express.

One unconditional inventory of `zerocopy/src` supplies both discovery and input
freshness. Cache exclusions elsewhere in the checkout cannot exclude source
directories with those names. Symbolic links and unreadable source directories
are unsupported, so filesystem traversal cannot silently narrow the checked
set. A saved source snapshot fixes both the file roster and each file's bytes.

Goldens contain complete generated modules. CI checks conservative fuzzy
textual equivalence and independently compiles proofs, required comparisons,
corollaries, and axiom audits for both golden and live models. Inline
mathematical decoders never replace the live extracted function definitions.
Both builds establish the checked properties, not equivalence of all unclaimed
behaviors.

Checked-in annotation projections expose the assembled model shapes, decoders,
and specifications for review. Both builds regenerate them and require exact
source equality. These snapshots are outputs, never inputs to the proof builds;
Rust comments remain authoritative and editable Lean projections stay separate.

CI's verification command requires live admission evidence in both builds and
exact copies of the checkout's authored proof sources before and after checking;
development-only bindings remain restricted to the editor's checking command.

All authored Lean packages are rebuilt, including the shared Rust mathematics
and its Aeneas companion. Only installed toolchain dependencies may retain
compiled caches across verification. An axiom audit of a cached theorem cannot
establish that the theorem concerns the current source definitions.

Reserved fences, Rust ownership, annotation-derived extraction roots, nominal
type/provider registration, exact function binding, complete LLBC extraction,
inspected source snapshots, configuration, pins, and external primitive
signatures protect the connection between a kernel-checked proposition and the
Rust item. Every present annotation is checked on both golden and live models.
Removing an annotation and its associated proofs intentionally removes that claim
from the checked set, visibly in the source and generated golden changes.

The trust boundary includes the pinned Rust/Charon/Aeneas translation, builtin
models, explicit primitive correspondences, Lean's kernel and permitted logic
axioms, source association, and specification adequacy. ABI reads are audited
data inputs, not axioms asserting useful properties. Type erasure does not
supply a universal ABI interpretation. `SEMANTICS.md` records the exact
bridge.

Failure controls challenge behavioral promises and required domains. Faulty
models must elaborate before proof rejection counts as evidence. Controls
should survive reorganizing helper lemmas: a constant rounding decoder fails
constructor and getter promises; a rejecting decoder fails promised output
admission or independently required input coverage.

Native Lean editing uses protected generated projections and real handwritten
proof paths. Rust annotations are authoritative; saved snapshots and owned
spans authorize owner-scoped copy-back. Source maps provide diagnostics.
Preview, conflict rejection, exact regeneration, and interruption recovery
preserve edits. Compiled inspection reports its actual subject and freshness
without claiming a new verification result. Source clones, credentials, and
irreplaceable editing state remain outside disposable `target` assets. Monitor
disk headroom before expensive extraction and while sustained builds run.

## Implemented changes in this stack

The stack implements the following changes in its earliest useful commits.

1. Replace concrete required-contract conversion with arbitrary-outcome adequacy
   and validate every existing contract. Retain source binding, both builds,
   independent domains, coverage, and axiom auditing. Include cross-module and
   adversarial tests for ignored outcomes, weakened posts, partial correctness,
   empty ghosts, and domain narrowing.
2. Normalize explicit decoder reasoning consistently. Reuse decomposition,
   `simp`, scalar facts, and `WP.spec_mono`; add a small sequencing tactic only
   where it eliminates repeated bridge work. Mathematical carriers alone cannot
   identify a decoder because different providers can share the same carrier.
3. Migrate `extend` to mathematical clauses while preserving its existing exact
   placement, alignment, flag, and payload guarantees. Keep useful raw helpers;
   avoid proof churn that merely changes presentation.
4. Retarget semantic decoder controls to operation promises and coverage rather
   than named representation-helper failures.
5. Allow ordinary acyclic model-support dependencies. Independent comparisons
   protect required getter domains and output admission; mutation controls
   challenge those guarantees without relying on helper names or import bans.
6. Integrate each change in the earliest useful commit of the existing stack.
   Preserve coherent review boundaries and validate intermediate states. Worker
   boundaries do not determine PR boundaries. Preserve GHerrit identities unless
   reordering requires regeneration to avoid the known auto-close bug.
7. Simplify implementation state and repeated traversals while preserving the
   checked boundaries above. Add module introductions, local explanations, and
   reader guidance for the source tools, Lean core, proof layers, and CI drivers.
8. Add Rust assertion harnesses and independent reference arithmetic in the
   earliest commits that can prove them. Retain the existing mathematical helper
   guarantees while making the complete numerical comparisons visible in Rust.
   Discover the checked set solely from present annotations, without a separate
   method roster or special harness classification.

## Shared Rust Lean library

The selected source location is `anneal/lean/`, with Lean modules and namespace
`Rust`. The library contains mathematical models of Rust and proofs about those
models. It is an independent Lake package with its own tests, usable by Anneal
V1, Anneal V2, and this integration. The shared package is implemented as the foundation of this stack.

Distribute the package through Anneal's existing omnibus dependency archive,
installed by exocrate during `cargo anneal setup`. Installed consumers require
that package from the archive. Repository development and zerocopy CI can use
the canonical source package directly with compatible pinned dependencies.
There is no additional Rust assets crate or separately downloaded library.

Archive construction must include the library's source, package configuration,
and compatible dependencies. Its identity and CI cache inputs must account for
changes under `anneal/lean/`; existing cache keys intentionally omit most Anneal
source files. Test the library independently and exercise imports from the
relocated installed archive, without relying on the repository checkout.

Share mathematical definitions and proved lemmas first. Keep frontend-specific
annotation machinery in its consumer, and retain explicit Rust correspondence
premises and proof-dependency audits. The shared namespace does not imply that
the library already models every part of Rust's abstract machine.

## Deferred decisions and reopening evidence

### Resource-free layout and storage work

The shared library supplies two independent foundations for layout and owned
byte-cast proofs:

- `Rust.Pointer.Value` retains an address, opaque optional provenance, and
  metadata. Its casts and metadata operations preserve the exact provenance
  value. Pointer equality observes address and metadata; it does not compare
  provenance. Non-nullness supplies no alignment, liveness, or access permission.
- `Rust.Storage.StorageDecoder` takes metadata explicitly, checks the requested
  byte width, and checks that a successful raw result carries that metadata.
  Fixed-width decoders adapt through unit metadata. Slice counts are inputs,
  including for zero-sized elements; byte length cannot recover those counts.

These are mathematical definitions and checked laws, not newly admitted Rust
operations. The storage carrier still contains only initialized numeric bytes
and uninitialized bytes. It does not encode pointers or decide where provenance
lives in a pointer's representation. Pointer-bearing byte operations remain
unsupported. Typed copies still require the treatment described in
[the lowering audit](LOWERING_AUDIT.md), including
[Aeneas issue #1405](https://github.com/AeneasVerif/aeneas/issues/1405).

Byte-cast reasoning uses the existing distinction between language validity and
optional mathematical admission. The source's `IntoBytes` law ranges over all
accepted language representations, regardless of mathematical admission. The
destination's intended `FromBytes` law must accept every initialized storage of
the correct width at both stages. The shared cast lemma composes these laws for
arbitrary represented bytes. It supplies no encoder and does not claim that a
particular Rust transmutation follows this interpretation.

The concrete `check_u32_slice_known_layout` Rust harness checks the actual
`<[u32] as KnownLayout>::LAYOUT` initializer, its descriptor fields, and sizing
for every element count, including checked-multiplication overflow. Admission
visits the local constant's initializer body; no axiom supplies the descriptor.
The visible guards expose the power-of-two and size-divisibility premises of
the ABI reads. This checks that concrete numerical behavior, not the complete
generic trait invariant. The proof also rejects an initializer changed from
`for_slice` to `for_type`.

The native capability fixtures under `tests/capabilities/` preserve the next
translation boundaries. With the current pins, the generic `KnownLayout`
fixture retains an associated-type equality that Aeneas rejects. A second
fixture without an explicit caller-side equality fails on the trait's own
`MaybeUninit` metadata equality. The production
`transmute!` fixture retains its compile-time trait-check helper and a loop that
Aeneas rejects. The required `FromBytes` declaration dependencies additionally
reach the unsupported recursive `Invariants`/`Alignment` group. These failures
are not successful extraction or completed Rust proofs. Do not delete bounds,
equalities, or required declarations to make those targets extract. Required
recursive declaration support is deferred; dependent work must wait for tools
that support it.

Native raw-pointer emission has a separate limitation. The pinned backend's
carrier stores only `v : T`, and its scalar pointer cast returns `undef`.
Emitted slice construction and `NonNull` operations remain external templates.
The mathematical pointer model does not repair that carrier or grant admission
to those operations. The existing checker continues to reject them. A faithful
carrier and checked primitive interpretations are prerequisites for proving
their address, metadata, or provenance behavior.

When those boundaries are supported, bind `KnownLayout::LAYOUT` to the original
Rust type and its metadata-indexed geometry. Reuse the complete recursive
layout semantics, which preserves an inner field's padding before outer
rounding. Preserve physical tail offset, stride, alignment, and conservative
padding flags. Keep mathematical extent, `usize` representability, and the
`isize` object-size restriction separate. The `MaybeUninit` obligation also
requires identical metadata and layout and acceptance of uninitialized storage
in every position; a layout-only theorem must not be presented as the full
trait invariant.

Concrete owned conversions use the actual standard transmute primitive for
`u32` and four-byte arrays, plus a guarded `u8`-to-`bool` conversion. These types
have no pointers, resources, destruction, or external-state invariants. Original
Rust endpoint checks and a compiled canonical-provider audit restrict that
interpretation to those cases; it does not admit the production macro or an
arbitrary generic transmute. Invalid Boolean encodings take the forbidden path,
even with postcondition `True`. Reference creation remains a later target because
numerical geometry and provenance presence alone do not supply permissions or
lifetimes. Derive
proof requests are also deferred. Existing annotation discovery, native binding
records, independent golden/live proofs, and dependency audits remain the sole
route to reporting a Rust specification as checked; these foundations add no
parallel coverage registry or automatic Rust ABI assumptions.

### Other deferred decisions

- **Canonical layout abstraction.** Retain structural `DstLayout` and existing
  `ModelViews` initially. Padding and trailing-size pilots already use those
  views. Use `extend`, sequence queries, and capacity contracts to compare total
  specification, decoder, bridge, and consumer burden before adopting
  `LayoutMath.LayoutValue` as the canonical model. Preserve physical offset,
  stride, flags, exact overflow outcomes, nested padding, and conservative query
  behavior. `DstLayout` intentionally admits intermediate values that do not
  describe completed Rust types; no global physical-realizability invariant.
- **Remaining raw clauses.** Migrate where mathematical language improves the
  whole proof. Raw clauses remain appropriate for representation-sensitive
  helpers and explicit ABI read premises. Do not require a zero raw-clause
  count.
- **Per-function independent duplication.** Retain current required contracts
  during this migration. After outcome adequacy is exercised, evaluate whether
  generic expansion tests can replace routine duplicate declarations while
  retaining independent semantic regression boundaries for layout operations.
  This is a policy choice, not a kernel requirement.
- **Richer automation.** Prefer upstream checked-arithmetic stepping, scalar
  tactics, and the existing loop adapter. Introduce a larger lifting DSL,
  per-model tactics, or new loop abstraction only after concrete repeated
  failures show a net benefit over ordinary lemmas and a thin tactic.
- **Broader carriers and effects.** Recursive nominal groups, general indexed
  carriers, const generics, associated-type trait laws, higher-ranked bounds, bounded
  nominal models, and escaping borrow reconstruction remain unsupported with
  explicit errors. The trait-law bridge supports type-parameterized traits
  and type-only bounds, preserving every original argument and native
  dictionary. `TransmuteFrom` exercises four ordered type arguments and
  generic state-model providers. Add semantics and admission checks before
  accepting the remaining carriers. Stateful or nondeterministic APIs may need
  observable traces and effects, rather than only result contracts.
- **Abstract storage and bit validity.** Check byte-to-value production before
  entering Aeneas's typed value domain; rejection must remain a forbidden
  execution, independently of ordinary library-model admission. A storage model
  must account for the translation's omissions as well as its primitives. The
  [pinned lowering audit](LOWERING_AUDIT.md) records known omissions and the
  admission checks needed before making memory-safety claims.
  [ADMISSION_DESIGN.md](ADMISSION_DESIGN.md) specifies the closed
  dependency traversal, controlled build origins using Charon's existing MIR
  preservation setup, primitive rules, and mandatory CI path. CI enforces
  these checks for the admitted fragment; extending that fragment requires
  corresponding operation semantics and coverage checks.
  <!-- FIXME: Typed transfers lose storage events; track support at
  https://github.com/AeneasVerif/aeneas/issues/1405. Until then, a typed storage
  abstraction must forget all padding contents and initialization facts. It
  must still check access obligations and reject reads that rely on those facts. -->
- **Anneal's stronger guarantees.** Construction/mutation closure, universal
  caller admission, memory validity, provenance, aliasing, and UB-freedom belong
  to a separately stated stronger claim. Conditional functional proofs can feed
  it without silently being presented as that claim.
- **Compiler correspondence.** Independent recursive semantics plus explicit
  Rust premises are the selected approach. Compiler regression tests challenge
  those premises for tested configurations. Formal rustc verification,
  exhaustive target coverage, and compatibility across compiler intervals are separate
  projects, not consequences of these tests.
- **Editing and execution conveniences.** Existing Lake incrementality,
  inspection, source maps, and copy-back are the baseline. Add watch mode,
  finer proof modules, doctor checks, or owned-cache pruning only for concrete
  latency or operational problems. Cache cleanup must preserve source and
  recovery data; disk pressure never authorizes deleting unique work.
- **Further implementation simplification.** The shared nominal traversal and
  derived registration names are implemented. Apply the same rule to future
  repeated state only when it reduces the whole implementation's reading burden.
  Preserve independent Rust ownership/count checks and regressions for discarded
  invalid fields, enum payloads, generic shapes, provider selection, and exports.
- **Upstreaming nominal-type support.** Keep the tuple-newtype option patch
  reproducible and included in the pin identity. Adopt upstream support when
  available with fresh extraction, complete golden review, and both proof
  builds.

## Historical choices that should not be reintroduced accidentally

The integration no longer uses inline Aeneas function bodies or inline proofs,
model replacement slots, proof templates, per-function declaration sorting,
`depends_on` rosters, `refines` clauses, or separate automatically selected
validity predicates. Native modules, transparent specs, direct retained
modeling providers, recursive decoding, and ordinary postconditions replace
them.

The generic-field staging problem and copy-back gap are resolved. Model proof
completion is scoped to decoder construction rather than defaults attached to
the model declaration. Encoders, losslessness, and representation certificates
remain optional properties justified by particular operation proofs.

## Referent contents: implemented scope

The shared `Rust.Referent` algebra covers uninitialized, initialized, and safe
byte domains, including empty safe domains. The zerocopy adapter uses the
retained physical and mathematical decoders. Validity markers carry optional
type-level codes, checked against their actual `Validity::KIND` dictionaries.
This uses the existing model-provider binding and audit; it adds no separate
state-dictionary inference mechanism.

Marked `TransmuteFrom` blanket impls, ordinary wrapper pairs, and the two
`Cell`/`UnsafeCell` chains have checked native law proofs. `CastableFrom` retains
its exact two identity pairs. Generic clients consume those laws, while
independent outcome families state the actual byte implications. Execution
success remains outside any conditional interpretation of a validity state.

`AsInitialized` contents and opaque `MaybeUninit` storage remain deferred.
Pointer casts and projections will additionally need explicit byte-range,
metadata, access, and resource arguments. These content laws do not grant them.

## Indexed storage and geometric projections

There is one physical profile per retained `RustModel`. A fixed profile uses
`BitDecoder`; an indexed profile uses `StorageDecoder` and retains its metadata
type and equality. Ordinary slices use `usize` element counts. Transparent
wrappers retain those counts. `IntoBytes` initialization covers every accepted
language representation, and realizability supplies bytes at each admitted raw
value's actual metadata. Neither law reconstructs metadata from byte length.
The native slice `IntoBytes` impl carries the same mandatory proof marker as
its fixed-layout counterparts; the client harness exercises native slice and
unsized-wrapper dictionary selection.

Generic Lean providers are more general than Rust's `Sized` parameters. To keep
array and wrapper laws valid for every supplied provider, indexed children also
compose as mathematical sequences with an explicit list of child metadata.
Array sequences check the declared count; slice sequences check the usize
length bound. This total mathematical extension supplies no Rust ABI for an
array of unsized elements. A native layout or pointer operation still needs its
own admitted semantics and correspondence premises.

The fixed-width `representation` API is derived from this profile. Owned zero
initialization and transmutation require that projection to exist. The current
native `FromBytes` and `FromZeros` laws retain their fixed-layout scope; indexed
completeness remains an explicit `StorageDecoder.CompleteWith` proof. Extending
those native laws requires carrying the `Sized`-related premises needed by
owned-value methods, rather than silently guessing metadata for them.

Geometric projection requires a bounded forward offset and unchanged opaque
provenance. `Cast` additionally retains the start; `CastExact` retains the size.
The shared library proves identity, composition, slice splitting, byte-count
views, empty-destination bounds, and no-wrap consequences under explicit bounds.
These numeric theorems grant no access permission or reference validity.

Native pointer execution remains rejected: the unchanged Aeneas pin erases the
observations these proofs need. Supporting native `Project`, `Cast`, or
`CastExact` proofs will require a faithful pointer carrier and primitive
translation. Associated-type equalities and recursive declaration limitations
also continue to block the richer `KnownLayout` path. No backend overlay or
assumed model of a local target bypasses those limits.
