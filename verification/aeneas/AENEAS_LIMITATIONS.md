<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Aeneas limitations encountered while verifying zerocopy

This report is a handoff for someone considering improvements to Aeneas and
Charon. It records the obstacles we encountered, the semantic information we
need, our workarounds, and the changes that would remove those workarounds.
It includes resolved obstacles because their solutions are part of the cost of
using the tools. A local restriction is not necessarily an upstream limitation.

The central finding is that **functional extraction supports substantially more
of our arithmetic and value reasoning than it supports of the connection to
Rust execution**. Most difficult proof infrastructure establishes which source
operation a theorem describes, which conditions survived extraction, and which
unsafe effects the extraction may have omitted. A successful extraction and a
Lean proof do not, by themselves, establish that connection.

## Scope, versions, and status

This report was prepared on October 15, 2026. The authoritative upstream bases
used by the current stack are:

| Component | Version |
| --- | --- |
| Aeneas | `ca282ec2312a96f6a985a4d23a663690816d3f3e` |
| Charon | `cf02e3f228f97ee7be3a415be56989053063326d` |
| Extraction compiler | `nightly-2026-09-17` |
| Lean | `4.31.0` |

Anneal's lockfile supplies the pins. Our runtime adds the checked-in
[tuple-struct option patch](patches/use-tuple-structs.patch) and
[Charon admission/origin patch](patches/admission-snapshot.patch). It also applies
one narrow generated-field naming repair in [prepare.py](prepare.py).
Claims about upstream implementation below refer to these bases, not to current
upstream HEAD. No upstream upgrade was attempted for this report.

The published source checkpoint used for this report is
`f1573e5f7307fde4522ad8ad94cf834f02386179`.
The generic `transmute_copy` extension described below is a subsequent **working
candidate**: its helper, caller, byte semantics, and independent contract checks
have passed isolated Lean checks, and its Rust fixtures have passed focused
compiler tests. At the report handoff, its final integrated golden/live check and
publication were pending. Subsequent commits and CI results establish their own
status; these isolated checks should not be read as a completed CI result.

We distinguish four kinds of evidence:

- **Observed failure:** a preserved invocation failed at the named stage.
- **Source finding:** the pinned implementation explicitly omits or rejects an
  operation. Consequences for stronger safety claims are deductions from that
  source, not necessarily executed counterexamples.
- **Integration restriction:** our checker deliberately accepts less than the
  upstream tools to avoid claiming semantics we have not supplied.
- **Historical result:** an older pin exposed a problem; that is not a claim
  that the October pin still has it.

The [lowering audit](LOWERING_AUDIT.md) enumerates the pinned statement/rvalue
languages and relevant transformations. It is not a proof of every translator
pass. This report is an inventory of encountered limitations and identified
semantic gaps, not a claim to have enumerated every possible translator bug.

## What we are trying to verify

Our initial proofs concern padding, rounding, layout composition, DST sizing,
cast planning, integer/byte computations, and the numerical parts of allocation
and split operations. We use independent recursive Rust-layout semantics and
explicit premises connecting those semantics to Rust's documented behavior.
Compiler assertions and regression tests challenge those premises; they do not
formally verify rustc.

More recent work attaches laws to actual unsafe-trait implementation dictionaries
and consumes those laws in generic functions. Examples include `Unaligned`,
`IntoBytes`, `FromBytes`, and `FromZeros::new_zeroed`. The next candidate proves
a generic owned conversion using `ManuallyDrop` and standard `transmute_copy`.

These are conditional claims. A function's admitted inputs and requirements must
hold, its execution must satisfy the chosen total or partial correctness rule,
and successful outputs must pass their mathematical decoder. This does not yet
establish Anneal's stronger whole-program promise that every caller satisfies
all safety obligations, including resource and temporal obligations.

## Reading map

| Area | Main obstacles | Present disposition |
| --- | --- | --- |
| Trait extraction | Residual associated equalities, recursive dictionaries, mixed declaration groups | Generic `KnownLayout` remains blocked; a specific `FromBytes` cycle was refactored away |
| Identity and source binding | Tuple flattening, macro origins, erased default-method bounds, semantic providers | Small upstream patch plus substantial downstream audits |
| Representation | Invalid values disappear into typed Lean carriers; bytes, padding and provenance are absent from ordinary values | Explicit physical decoders and guarded primitive models |
| Execution safety | Drop, unwind, place and implicit guards may be omitted | Closed admission with kernel proofs for empty drops; other unsupported execution rejected |
| Control flow | Production macro's exitless helper loop; a never-returning conversion failure | Separate extracting helper; original macro remains unproved |
| Pointer and memory operations | Value-only pointer carrier, unsupported raw-address operations, no resource semantics | Mathematical value foundations; native execution generally rejected |
| Proof ergonomics | Raw/model bridges, dictionary-law plumbing, loop and theorem registration adapters | Reuse upstream WP/tactics; small local interfaces |
| Reproducibility | Error-bearing output, partial artifacts, toolchain pins, cache provenance and host packaging | Strict fresh final CI; faster provisional development separately |

## 1. Trait and declaration extraction

### 1.1 Residual associated-type equalities block generic `KnownLayout`

**Observed; Aeneas and Charon interaction; unresolved for the generic target.**
Charon successfully extracts both of these cases:

1. A generic caller with an explicit `KnownLayout<PointerMetadata = usize>` bound.
2. A generic caller without that explicit equality, whose `KnownLayout` trait
   itself requires
   `<Self::MaybeUninit as KnownLayout>::PointerMetadata = Self::PointerMetadata`.

Aeneas rejects them at
`src/symbolic/SymbolicToPureTypes.ml:1000–1001`, which requires the associated-type
constraint list to be empty. The second fixture matters: removing the caller's
equality does not remove the equality required by the trait.

This is not a blanket lack of associated-type support. Small acyclic equality
fixtures succeed. Charon's Aeneas preset already requests associated-type
lifting. Its lifting pass deliberately avoids expanding a self-referential
associated-type cycle indefinitely, leaving a constraint that Aeneas cannot
translate. Changing the order of command-line options is not a solution.

A decomposed recursive fixture gets past one equality and then fails on residual
associated types at `SymbolicToPure.ml:224`. Bounded associated declarations and
implied clauses encounter additional restrictions at `:238–243`. The pinned
`parameterize_trait_types` configuration reference is not a working alternative:
its projection path is unimplemented.

**Effect on zerocopy:** we cannot yet state and prove the complete generic
`KnownLayout` invariant against the faithfully extracted dictionary. In
particular, we cannot silently remove its `MaybeUninit` metadata equality and
claim to have verified the original trait.

**Current workaround:** prove concrete local associated-constant initializers
and numerical descriptor operations. Our `[u32]` layout harness follows the
actual local initializer, checks its fields and every element count, and rejects
a deliberately wrong initializer. It is not a generic trait proof.

**Needed upstream support:** retain equalities through signature translation;
either normalize both paths to the same type parameter or provide checked Lean
equality evidence and use it for the required transports. Preserve the original
associated slot, clause/parent path, and final projection/parameter mapping.
Selective lifting of acyclic components may reduce the problem, but the recursive
relation must remain represented. Deleting the assertion or clearing the
constraint is not faithful support.

Evidence: [capability fixtures and exact outcomes](tests/capabilities/README.md).
The local historical evidence directory
`into-bytes-front-end-20261013/evidence/knownlayout-summary.md` contains seven
minimal probes and the Charon lifting analysis.

### 1.2 Recursive trait dictionaries and mixed groups have narrower support than recursive functions

**Observed and source-confirmed.** Aeneas supports recursive functions, some
mutually recursive functions, recursive data types, and a singleton recursive
trait implementation in Lean. The relevant missing cases are recursive trait
**declarations**, mutually recursive trait **implementations**, and mixed groups
of trait dictionaries, functions, closures, and types.

The restrictions are explicit in `src/Translate.ml:1183–1256`. A finite Rust
trait declaration graph can become a recursive dictionary representation that
cannot simply be emitted as independent Lean records. Full support needs a
finite, well-typed representation of that recursion; not every dictionary cycle
is an ordinary positive inductive type.

**Historical `FromBytes` blocker:** importing its supertrait method signatures
reached the mutually recursive `Invariants`/`Alignment` group. Even a generic
identity function with `FromBytes` could fail without performing a byte operation.

**Resolved portion:** we refactored `Alignment::read` to take an explicit
reference/aliasing parameter and a pointer with tuple invariants. The current
signature uses `Ptr<T, (A, Self, Safe)>`, retains `A: Reference` and
`T: Copy + Read<A, R>`, and preserves the compiler's trait checks. This removes
that particular declaration cycle without deleting its meaning. `FromBytes`
dictionaries and the verified `FromZeros::new_zeroed` path now extract.

**Unresolved portion:** full pointer-heavy production targets also produced
mixed SCCs involving `Alignment::read`, projection/conversion helpers, and
closures. Removing the declaration cycle does not prove those bodies or solve
every mixed group. Some older design notes still describe the initial
`FromBytes` obstacle; that description is historical, not the present frontier.

**Needed upstream support:** group-aware recursive dictionary translation,
including associated types and method dependencies. Start with the small
pointer-free recursive associated-type fixture before the full zerocopy graph.
A requirement to refactor a particular Rust trait cycle may remain a reasonable
interim restriction, but diagnostics should identify that cycle and the
unsupported group kind directly.

Evidence: [current pointer invariant code](../../zerocopy/src/pointer/invariant.rs),
[zeroed proof](lean/Proofs/Zeroed.lean), and local
`trait-read-tuple-evidence-20261014/README.md` plus `production-targets/`.

### 1.3 Excluded provided methods still imported unwanted declaration dependencies

**Observed Charon bug; locally patched.** Traits contain methods irrelevant to
the operation we want to prove. Excluding an unused provided body did not always
prevent its signature or an implementation override from being discovered.
Those signatures could import the very unsupported trait group we intended not
to execute.

**Workaround:** our Charon patch applies exclusion consistently during trait
signature discovery and implementation discovery. A reached reference to an
excluded method is an error. Required methods remain required; we do not remove
their signatures to make a trait appear simpler.

**Needed upstream support:** consistent demand-driven discovery across default
methods, their signatures, overrides, dictionary fields, and actual call
resolution. Preserve the distinction between an interface dependency and an
executed body. Broad opacity is not equivalent: one experiment made
`ConvertError` opaque, then prevented a caller from matching it.

Evidence: [Charon patch](patches/admission-snapshot.patch), provided-method
controls under [tests](tests/).

### 1.4 Default-method extraction can erase the unused enclosing `Self` dictionary

**Observed normalization; downstream semantic binding required.**
`FromZeros::new_zeroed` does not computationally inspect its `Self: FromZeros`
dictionary. Charon can remove that unused argument. The Lean computation is
smaller, but the function's correctness still depends on that trait's promise.

**Workaround:** recover the exact enclosing trait and method from original
compiler ownership, introduce its dictionary and law as specification premises,
and audit that recovery. We do not invent an extra Rust argument or modify the
extracted computation.

**Needed upstream support:** stable original-to-final binder/clause provenance,
including an explicit record of erased assumptions. A proof interface should
make computational erasure compatible with retaining logical premises.
Recreating bounds from generated names alone is too fragile.

Evidence: [ZeroedAudit.lean](lean/ZeroedAudit.lean),
[TraitLawsSupport.lean](lean/TraitLawsSupport.lean), and
[the enclosing-bound documentation](README.md#frombytes-fromzeros-and-owned-zero-construction).

### 1.5 Trait bounds are computational dictionaries, not automatically proved laws

**Integration requirement, not a missing Rust trait translator.**
Aeneas can lower many traits and dispatch through dictionaries. That does not
supply the semantic assertion that an unsafe trait is meant to promise. For
example, `T: Unaligned` must provide evidence that alignment is one;
`T: FromBytes` must provide the construction law for both language and library
validity.

Our `TraitLaws.*` propositions are indexed by the **actual** extracted dictionary
and the selected model providers. Generic contracts consume those propositions.
Implementation checks discharge them for actual impl dictionaries without adding
extra assumptions. Nameless `invariant_proof` markers give a reviewer a visible
request; reached unmarked implementations still incur obligations.

**What upstream support would help:** an optional law layer tied to native
trait/impl identities, with preserved parent and associated-type paths. It could
remain separate from computational records. Automatically assuming every trait's
law without enforcing implementation obligations would merely move a
load-bearing gap into the tool.

**Remaining local limitations:** our bridge handles a restricted generic grammar.
Associated-type law parameters, higher-ranked executable bounds, richer const
generics, and trait-bound nominal model assembly need additional local support
as well as faithful upstream extraction. Not every such rejection is an Aeneas
limitation.

### 1.6 Cross-crate constants can become external templates

**Observed emission boundary.** A standalone fixture depending on zerocopy can
emit a call to `KnownLayout::LAYOUT` while leaving its initializer as an external
axiom template. That is successful translation of an interface, not verification
of the constant's value.

**Workaround:** put the relevant harness inside zerocopy so extraction follows
the actual local initializer. The concrete slice initializer is now proved.
For deliberately external primitives, supply a reviewed interpretation instead.

**Needed support:** precise, documented body-availability/opacity controls and
provenance for dependency bodies and constant initializers. A dependency's
precompiled optimized MIR cannot silently substitute for the inspected stage.
Templates should remain visibly incomplete until an interpretation is supplied.

## 2. Identity, annotation provenance, and generated interfaces

### 2.1 Tuple/newtype flattening destroys distinctions needed by model providers

**Observed default policy; resolved by exposing an existing option.** Different
Rust tuple structs can lower to the same tuple or payload type. Our earlier
`RoundingAlignAndPhase(NonZeroUsize)` example therefore did not initially retain
a nominal one-field Lean structure. Typeclass instances and decoders for
otherwise different Rust types could collide.

**Workaround:** a small CLI patch exposes the existing
`Config.use_tuple_structs` setting. We pass `-use-tuple-structs false`, preserving
nominal constructors and fields. Tests cover constructors, projections, patterns,
updates, generics, and empty tuple structs, and retain an unpatched/default-mode
oracle.

**Needed upstream support:** expose the switch without changing its default,
and test nominal extraction comprehensively. Reconstructing lost identity by
editing aliases downstream is not a principled substitute.

### 2.2 Duplicate trait parent field names produce invalid Lean

**Observed generation bug.** `ZeroablePrimitive` needs `Copy Self` and
`Copy NonZeroInner`; the pinned backend generates the same `markerCopyInst`
field name for both.

**Workaround:** a narrow structural repair renames the second declaration and
matching initializers to `innerCopyInst`. It verifies the expected output shape
and preserves both dictionaries. It does not delete a parent clause.

**Needed upstream support:** unique, stable names based on clause identity, with
matching constructor initializers and metadata. A regression should retain two
instances of the same parent trait applied to different types.

Evidence: [rename_copy_fields](prepare.py).

### 2.3 Ordinary doc comments do not provide sufficient macro provenance

**Observed integration obstacle; Charon extension.** Our specifications and
impl markers originate in Rust doc fences. Macro invocation arguments can supply
a marker that is forwarded, duplicated, transformed, or discarded. Surface text
alone cannot determine which expanded impl it decorates. Expanded doc text alone
cannot establish which source fragment it came from. Tuple-struct constructors
can also share synthetic attributes with the type owner.

**Workaround:** a source lexer/parser discovers reserved annotations; a patched
Charon records a whole-HIR attribute/owner census, literal origins and source
spans before root selection. Exact doc-origin/span selectors independently root
positive impls. The tooling reconciles source fragments with expanded owners in
both directions and rejects missing or ambiguous associations. Constructor
aliases receive a narrow explicit treatment.

**Needed upstream support:** a supported provenance record for each retained
attribute fragment, its source literal and expansion context, exact native owner,
configuration, and transformed owner. A complete census must include otherwise
unsupported nodes, so an annotation cannot disappear before reporting an error.
Rust attributes should not need to become a second ad hoc parser for executable
Rust. Derive-generated proof markers remain a deferred integration problem, not
proof that ordinary declarative macros are unsupported.

### 2.4 Native export metadata exists, but does not replace independent binding checks

**Existing upstream capability with remaining integration needs.** We use
`-emit-json` and `translation.json`; this is not a metadata exporter we invented.
The native tables already identify functions, types, globals, traits and impls,
with ownership, names and relevant effect information.

They do not by themselves establish the correspondence between original compiler
arguments, transformed arguments, model-provider suffixes, generated source and
compiled Lean declarations. A global's native ID can also differ from the ID of
the function that computes its initializer. Our static size assertion exercises
that distinction.

**Workaround:** join native IDs with original/final compiler evidence, then inspect
the compiled Lean environment. Enforce closed inventories and exact argument and
provider identities, not just matching names or definitionally equal carrier
types. Track constant initializer edges as well as ordinary calls.

**Useful additions:** schema/stage identifiers, stable binder/field/clause maps,
explicit erased-origin records, and global-to-initializer identities. Preserve
native metadata as the primary interface; scraping generated Lean text should
remain limited to framing checks the exporter does not supply.

### 2.5 Generic external models need semantic parameters absent from Rust computations

**Observed extension requirement.** A generic physical operation such as
`zeroed<T>` needs to know which physical decoder and mathematical admission rule
interpret `T`. A Rust computational dictionary does not supply our Lean
`RustModel T`.

**Workaround:** `native_models` preserves the original argument prefix and native
function expression, and appends only the semantic providers its elaborated body
needs. Capture propagates through actual dependencies. The compiled audit checks
that forwarded calls use the exact original providers, including when different
Rust meanings share a Lean type. A same-type replacement provider is not accepted
merely because it typechecks.

**Needed upstream support:** an explicit primitive-interpretation interface with
checked semantic parameters and effect classification, native binder maps, and
well-defined propagation through generic callers. This would replace our small
Lean/Python extension, not require baking zerocopy's particular model into Aeneas.

## 3. Physical representation and unsafe execution

### 3.1 Typed values hide invalid representations before a contract can inspect them

**Fundamental abstraction boundary.** An extracted Lean `Bool` has no value
corresponding to byte `2`; an enum constructor has no invalid stored tag.
Record fields do not retain padding or arbitrary physical discriminants.
A proof that every Lean Boolean is valid says nothing about the Rust operation
that may have produced an invalid Boolean before lowering.

**Workaround:** validate candidate bytes or integers before constructing the typed
carrier. Guarded interpretations return `.fail .undef` outside the permitted
language domain. Mathematical/library decoding follows separately; it cannot
retroactively detect an operation erased before reaching that domain.

**Needed upstream support:** a physical-to-typed boundary that retains the source
storage and checks language validity before introducing typed logical values.
It must handle niches, initialization and metadata, not just reinterpret a
well-typed Lean value. Ordinary safe functional lowering can remain unchanged
where its assumptions are justified.

### 3.2 Copies and moves do not retain physical storage events

**Pinned source finding; major safety boundary.** Aeneas transfers logical values,
not a persistent byte store. Typed copies may forget padding; writes to padding
cannot automatically be treated as preserved facts after arbitrary transfers.
This affects an exact-storage model of `MaybeUninit<T>`, `assume_init`, unions,
transmutation and byte-level observations even when the function is annotated.

[Issue #1405](https://github.com/AeneasVerif/aeneas/issues/1405) is the issue we
filed for typed copies. This report relies on our pinned audit and recorded
issue reference; it does not claim a fresh verification of that issue's status.

**Conservative plan:** forget all padding contents and initializedness from the
outset, including when a write would physically precede any typed copy. This
rejects some valid Rust programs but does not falsely promise preservation.
Writes still evaluate their arguments and must satisfy access obligations.
This plan is not an implemented general runtime storage semantics.

**Needed support:** retain typed-transfer events, or provide an explicit
abstraction rule that soundly forgets precisely the permitted storage facts.
A richer carrier alone is insufficient if implicit transfers remain invisible.
Keep provenance placement abstract; do not invent a per-byte provenance rule
that Rust has not committed to.

### 3.3 Pure AM-byte decoders are not a runtime memory model

**Current local foundation and remaining scope.** The shared `Rust.Storage` library
has initialized numeric bytes, uninitialized bytes, physical decoders, arrays,
metadata-indexed storage decoders, and cast-composition laws. Those are ordinary
pure Lean values. They do not cause Aeneas to expose reads, writes or typed
transfers.

The physical relation must correspond to actual Rust layout and language-valid
representations. Initialization alone is vacuous for an always-rejecting decoder.
Our candidate strengthens `IntoBytes` with source realizability: each admitted
source value has some represented bytes. This remains vacuous for an
uninhabited source, as required; it does not manufacture a ZST token or establish
an external-state invariant.

`FromBytes` completeness includes both language decoding and mathematical/library
admission. `FromZeros` requires both stages for all-zero storage. The model
constraints can be proved automatically without proving that a decoder describes
its input as a human intended. We therefore assess models through operation
contracts; we do not impose a universal injective encoder or canonical
representation requirement that would, for example, forbid hidden hash seeds.

**Needed support:** reusable physical profiles connected to emitted type facts,
with explicit coverage and trusted premises. The meaningful upstream target is
a model interface and validated primitive boundaries, not a theorem that an
arbitrary user-authored decoder must be the uniquely correct abstraction.

### 3.4 Generic layout facts are not a universal ABI model after type erasure

**Observed information gap.** Lean `Type` is not a Rust type descriptor.
Different Rust meanings can erase to one carrier. Generic `size_of`, alignment,
DST metadata and associated layout constants therefore need more information
than the bare lowered type supplies.

**Workaround:** explicit data inputs for ABI reads; independent recursive layout
semantics; metadata-indexed decoders; and compiler assertions for concrete
profiles. Charon already retains compiler-chosen layout values and expressions
for guaranteed facts. We can challenge our Reference-based calculations with
Rust compile-time assertions without first inventing an Aeneas memory model.
Those assertions check the configurations compiled, not every ABI.

The generic transmute candidate's `sameSize` premise ties both ordinary ABI
queries to both physical widths. We rejected changing existing total `size_of`
semantics to fail for an arbitrary oversized mathematical decoder, because that
would narrow existing contracts. Physical-model correspondence is explicit.

**Needed support:** preserve stable Rust type/instantiation identities and expose
available layout/metadata observations as data with their provenance and scope.
Keep compiler choices distinct from language guarantees. A layout descriptor
must model inner padding before outer rounding for nested DSTs; outer alignment
alone is insufficient. Layout, bit validity, optional library invariants,
`usize` bounds and `isize` object-size bounds remain distinct facts.

### 3.5 Raw-pointer signatures can emit without useful pointer semantics

**Observed emission and pinned backend limitation.** `RawPtr.lean` has a carrier
with `v : T`, not an address/provenance/metadata representation. Its scalar cast
returns `.fail .undef`. Native probes can emit raw-pointer signatures while
leaving slice-pointer construction, `NonNull` and its operations as external
axiom templates. That is not an admitted pointer proof.

A production `IntoBytes` path separately failed on `&raw const (*self)` and
`&raw mut (*self)`. These are actual extraction rejections, distinct from the
successful signature-only probes.

**Workaround:** reject general native pointer execution; use narrow reviewed
boundaries for selected byte operations. The shared `Rust.Pointer.Value` model
already describes addresses, opaque optional provenance and metadata, with casts
that preserve provenance. It is a mathematical foundation, not a replacement for
the native carrier or permission to dereference.

**Needed support in stages:** first a faithful pointer-value carrier and cast/
metadata operations; then storage/access interpretations with alignment,
initializedness and bit-validity guards; finally permissions, aliasing, allocation
ownership and liveness where those claims require resources. Value-only pointer
reasoning need not wait for a complete resource logic. Do not decide where
provenance lives in pointer bytes beyond documented Rust guarantees.

### 3.6 References, boxes and allocations lose spatial and resource observations

**Deliberate upstream functional abstraction.** References become referent values;
`Box<T>` becomes `T`; box construction is eliminated and allocator parameters
can be hidden by the preset. Aeneas's borrow analysis is useful and substantial,
but the pure result does not retain allocation identity, address alignment,
retagging, access permissions, lifetime extent, allocator effects or ownership
resources.

**Effect:** we can prove interval bounds, disjoint numerical ranges, layout gates
and allocator argument preparation without having proved reference creation,
actual allocation or full pointer validity. The production paths consuming those
facts still require their Rust safety arguments.

**Needed support:** preserve those observations or expose explicit abstract
operations and premises for the claimed layer. Full resource modeling is a
separate larger project; adding a size theorem cannot supply liveness.

### 3.7 Residual drops do not execute destructors in the default interpretation

**Pinned source finding that became an actual prerequisite.** Default `Drop`
interpretation is a no-op. `-eval-drops` invalidates a logical value and processes
loans; it does not execute its arbitrary destructor body. Charon's
`--precise-drops` adds `Destruct` bounds and requires at least elaborated MIR,
which is a different inspection stage. Neither flag is a one-line repair for
our promoted-MIR admission theorem.

The real generic transmute helper retains conditional drops on moved argument
and temporary slots, including normal and unwind paths. Rejecting all drops
would reject this useful program; accepting them without an argument could hide
a destructor with arbitrary unsafe effects.

**Implemented workaround:** a conservative ownership analysis over the complete
compiler body. Lean proves accepted whole-local conditional drops empty, and
therefore unable to execute destructor glue. Fresh certificates are bound to the
exact body, snapshot, native identity and checker source. Uncertain joins,
projections, partial moves, cycles and meaningful drops fail closed. Unreachable
and unwind blocks are not silently omitted from the structural audit.

**Needed support:** accurate initialization/drop-flag semantics and explicit
execution of destructor glue, including generic and unwind destruction, or an
upstream-supported certificate that an erased drop cannot execute. Preserve the
inspection stage and its meaning. A proof that an empty slot has no destructor
effect does not prove arbitrary destructors harmless.

Evidence: [DropOwnership.lean](lean/DropOwnership.lean),
[DropJson.lean](lean/DropJson.lean), [DropAudit.lean](lean/DropAudit.lean), and
[drop_ownership.py](drop_ownership.py).

### 3.8 Panic, UB and unwind termination are not preserved uniformly

**Pinned source finding.** Charon distinguishes these abort kinds. Aeneas maps
all `Abort` forms to a symbolic panic node, ignores the failure kind on `Assert`,
and ignores `on_unwind` blocks during call/assert interpretation.

**Workaround:** total and partial contracts both reject failures. Reviewed unsafe
primitives use the existing `.fail .undef` marker, and sequencing preserves it.
Even `ensures _ => True` cannot accept that result. We audit original cleanup
execution and reject unsupported effects before they are erased.

This is not a new Result constructor patched upstream: `Error.undef` already
exists. It means no permitted execution claim here and is also used by backend
unsupported models; it is not always a diagnosis that actual Rust has UB.

**Needed support:** preserve failure kinds and cleanup effects, and distinguish
fatal forbidden execution from recoverable panic in any future handlers. A
thread-spawn model that returns successfully while hiding a child's UB would
break the intended safety claim even if it correctly ignores child termination.
We do not yet model thread spawn, panic catching or panic-tolerant contracts.

### 3.9 A convenient failure-erasing adapter is unsafe to reuse indiscriminately

**Existing API with a restricted applicability.** `Option.ofResult` can turn every
failure, including `.undef`, into an ordinary `None`. That can be appropriate
inside a reviewed checked-arithmetic model, but is not a faithful implementation
of arbitrary Rust recovery from forbidden execution.

**Workaround:** follow compiled downstream dependencies, including opaque helpers,
and reject uses of this adapter in admitted executions. Stop at explicitly
reviewed backend primitives, whose implementation has its own trusted contract.
Independently audit complete external definitions: blacklisting one adapter alone
cannot rule out a hand-written failure-erasing match.

**Needed support:** effect-specific recovery interfaces or a result/effect design
in which UB cannot be accidentally handled as panic. Retaining the distinction
through interpretation and handlers matters more than adding a tag.

### 3.10 Place mentions and CPU-feature obligations can be absent from the pure body

**Pinned source findings.** Charon notes that invalid projections in
`PlaceMention` can cause UB; Aeneas treats it as a no-op. Aeneas also has a pass
for inserting `target_feature` assertions, but its flag is off by default and
our driver does not enable it.

**Workaround:** inspect the original dependency closure, validate or reject
projection shapes and unsupported attributes, and keep these premises visible.
A supported operation must supply its implicit access/CPU conditions.

**Needed support:** checked place evaluation and explicit feature premises or
admission. Enabling a feature-gate pass solves only that particular obligation;
it does not justify erased storage, destructor or pointer effects.

### 3.11 Builtin replacement and infallibility classification affect what survives

**Trust boundary, not just template filling.** A builtin can replace a visible
Rust body, so auditing that unused body does not audit the executed Lean model.
An operation classified as pure and infallible can also lose unused calls or
repeated evaluations before a downstream safety guard is added.

**Workaround:** select and audit the actual interpretation, exact Rust endpoint
pairs, generated failure-capable signature, complete compiled definition and
call bindings. Preserve argument evaluation and failure even when a result is
ignored. Local opaque helpers have exact body hashes; external standard-library
operations have explicitly reviewed semantics.

**Needed support:** a first-class interpretation registry with effect and
correspondence information, validated against the original signature and use.
A user-supplied unsafe model must not be allowed to add failure after the
translator has already treated the operation as infallible.

### 3.12 Deterministic results do not automatically cover representation ambiguity

**Real design pressure; current bounded downstream solution.** Aeneas's current
`Result` is an interaction tree whose Rust effect interface contains failure,
not arbitrary storage-read choices. A fixed raw value can admit multiple byte
representations, and converting it to a byte-observing destination can expose
those differences. Proving only a chosen canonical output would lose behaviors.

**Candidate workaround:** a checked representation preference in each retained
model provider, a generic proof quantified over that provider, and a coverage
theorem varying only the preference while fixing the decoders. Tests produce two
different destination values from the same raw source. No injective encoding or
single canonical representation is imposed.

This preference is a function of the raw value, not execution history. Admission
therefore restricts the first fragment to one conversion per execution and
polymorphic forwarding that keeps the provider universally bound. Repeated
calls, loops, recursion or concrete forwarding can correlate or fix choices and
are rejected. These are **our restrictions**, not Aeneas's general loop or
recursion limitations.

**Needed support:** explicit state or a suitable nondeterministic effect with a
universal/demonic WP, or another abstraction with a proved coverage theorem.
Thread choices through extraction and optimizations. A general interaction-tree
library is useful infrastructure, but the concrete Rust effect interface and
extracted computations must actually expose the effects in question.

## 4. Earlier compiler transformations and complete admission

### 4.1 The requested MIR stage is not enough unless the actual body origin is checked

**Source-confirmed hazard; Charon patch.** Promoted MIR can be unavailable because
rustc has stolen a body, and upstream can fall back to optimized MIR. Aeneas
cannot reconstruct an already-erased unsafe event from final LLBC.

**Workaround:** preserve the imported unstructured body before Charon passes;
reject local optimized-MIR fallback during admission; inspect both that snapshot
and final LLBC; bind exact source/configuration/runtime identities to the result.
Final CI rechecks the evidence rather than trusting a stale report.

**Needed support:** supported stage-specific snapshots, actual stage/fallback
metadata, body origin and transformation provenance. Final `--ullbc` output need
not mean pretransformation input.

### 4.2 Optimization level zero does not provide a semantic preservation theorem

**Important negative result from the design investigation.** Charon already sets
MIR optimization level zero, `mir_preserve_ub`, and `always_encode_mir` for crates
compiled through its wrapper. Thus seeing an `optimized_mir` query is not proof
that optional optimizations ran. Conversely, level zero does not reverse earlier
mandatory lowering, reconstruct source effects, or establish the build origin
of precompiled dependencies and the sysroot.

**Workaround:** controlled inputs and stage checks, closed original dependency
inspection, and external interpretations for bodies whose relevant origin is
not available.

**Needed support:** auditable compiler-body provenance and a preservation argument
for the admitted language/effects. Enumerating each observed erasure is useful
but cannot substitute for a compositional account of which observations each
pass preserves.

### 4.3 Compiler alignment and null checks are deliberately disabled

**Pinned driver finding.** Charon disables `CheckAlignment` and `CheckNull`
insertion. This avoids compiler-generated checks interfering with its symbolic
model; it also means a missing assertion is not evidence that the corresponding
Rust access has no alignment or non-nullness requirement.

**Workaround:** reject unsupported memory operations, or add explicit semantic
guards to their reviewed interpretations. A pointer-valued cast need not require
dereference permission, while a read or reference creation does.

**Needed support:** expose operation preconditions directly, rather than relying
on incidental rustc debug checks. Enabling those checks alone would still not
model initialization, allocation bounds, provenance or aliasing.

### 4.4 Process success and generated files do not certify a complete translation

**Observed tool contract hazard.** Historical Charon runs exited zero while
emitting `has_errors: true`, missing/partial declarations and warnings. Upstream
failures can also leave files behind. A file's existence or a successful wrapper
command cannot certify extraction.

**Workaround:** strict flags; require the explicit success marker; verify closed
owner/dependency inventories; reject unknown shapes, errors, missing declarations
and unapproved axioms; stage outputs; and compare fresh goldens and live proofs
independently. The local checker validates the complete relevant schema rather
than guessing unfamiliar constructors or serialization references.

**Needed support:** an unambiguous complete-success contract, structured stage
errors, atomic publication of successful output, and explicit schema/version
metadata. External axiom templates should not resemble completed proofs.

## 5. Specific control-flow and backend failures

### 5.1 An exitless loop in the production `transmute!` helper is rejected

**Observed.** The macro's compile-time trait-check helper retains an infinite loop
without a `break`. Aeneas rejects it at `InterpLoops.ml:411`. Direct calls to the
standard transmute primitive extract, isolating the macro-helper issue.

**Workaround:** first prove direct concrete standard transmutations. The current
candidate adds a real trait-bounded const `transmute_copy` helper and a generic
caller with the size assertion in the executable helper. The production macro
is unchanged and has not acquired a proof merely because the helper works.

**Needed support:** translate no-exit loops into an appropriate divergent
computation **while retaining their body effects**. Replacing every syntactically
infinite loop by `.div` would hide a panic, unsafe operation or state effect that
occurs first. Better reachability/declaration selection may avoid importing a
nonexecuted type-check helper, but must retain the compiler-checked trait facts.

### 5.2 A never-returning error conversion produced an internal failure

**Observed historical production probe on the current pin.**
`From<AlignmentError<Src, Dst>> for !::from` / `alignment_impossible` failed with
`Unexpected result: Cps.Unit` in `interp/Interp.ml:593`.

No verified general repair has been recorded. This is a separate control-flow
frontier from the generic trait-cycle failure and from resource semantics.
An upstream regression should retain the exact never-returning conversion and
its call context. A suitable `Result Empty`/divergence interpretation must not
turn a forbidden operation before non-return into an acceptable divergence.

Evidence: local `existing-unsafe-path-probe-20261013/aeneas.log`.

### 5.3 Mutable suffix reconstruction is incorrect in a pinned slice builtin

**Observed backend model bug; avoided.**
`SliceIndexRangeFromUsizeSlice.get_mut` reconstructs an updated slice using a
modified suffix followed by the old suffix, rather than the original prefix
followed by the modified suffix.

**Effect:** a proof about an offset write could describe the wrong updated
sequence even though the Rust operation and Lean types look reasonable.

**Workaround:** leave the builtin unregistered; use a narrow local offset-copy
boundary with exact prefix/copy/suffix semantics and full body/signature checks.

**Needed upstream repair:** correct reconstruction, and prove length, unchanged
prefix, replaced region and unchanged suffix laws. Exercise boundary offsets,
empty replacements and nonempty prefixes. This is a correctness defect, not
merely a request for a more convenient lemma.

### 5.4 Some borrow and type forms remain outside the relevant fragment

**Mixed evidence; do not overgeneralize.** Aeneas supports substantial borrow
functionalization, returned references, closures and recursive functions. Our
current admission checker deliberately rejects escaping borrows, arbitrary
callbacks, function-pointer calls and unreviewed dynamic dispatch.

A returned mutable borrow can expose a backward reconstruction function rather
than an ordinary updated value. Automatically checking only the visible return
would miss validity of the state reconstructed later. We currently reject that
specification shape instead of implying the hidden state was validated.

Pinned source also has restrictions on ADTs with nested mutable borrows,
unsupported function-arrow/dynamic trait shapes, generic associated types and
bound/implied-clause shapes. The historical research includes nested-borrow
failures on older pins; they are not evidence of a current flaky reproducer.

**Needed work:** distinguish a source construct that cannot extract from a
functionalization our contract assembler cannot yet express. For supported
backward functions, expose the argument/result/state relation and attach
higher-order validity contracts. For actual unsupported shapes, retain minimal
regressions and improve diagnostics rather than treating all references or
closures as unsupported.

## 6. Proof and model ergonomics: what was already available

These items caused development cost, but much of the needed foundation already
exists upstream. Reimplementing it would increase the maintenance burden.

### 6.1 Total and partial correctness already have the needed basic meanings

`WP.spec` requires successful termination. `WP.dspec` can permit divergence.
Both reject failure; partial correctness is not permission for panic or UB.
Our concise `spec` language builds on these predicates, automatically checks
input/output decoding, and requires an execution judgment even for a trivial
postcondition. We tested panic and divergence explicitly.

The syntax, raw/mathematical scopes, decoder completion and required-contract
checks are downstream interfaces. They are not evidence that Aeneas lacked
contracts. Upstream `spec_mono`/`dspec_mono` already support mathematical-view
adaptation. Our original contract migration became verbose in part because it
also strengthened propositions; that was not fundamental to macro syntax.

### 6.2 Checked arithmetic and indexed loop proofs mostly needed reuse and adapters

Aeneas already supplies exact checked-add/subtract/multiply rules, `step_pure`,
scalar tactics, well-founded `loop.spec` and `loop.spec_decr_nat`. We reuse them.
Our indexed-loop adapter packages a natural measure, a prefix model and the
specific invariant shape useful for byte/layout computations. The body must
still prove progress, bounds and prefix preservation.

Rust finite-word operations and `Nat`/`Int` views create bridge goals. General
rounding, powers of two, bitwise encodings, overflow outcomes and nested layout
algebra still need domain lemmas. This is largely library/automation work,
not a request for a second arithmetic or termination semantics.

**Useful improvements:** better maintained bridge lemmas and simp sets, stronger
standard primitive specs where appropriate, reusable loop-shape adapters, and
local diagnostics that identify the missing arithmetic fact. Preserve APIs whose
`Option` result intentionally describes overflow on all inputs.

### 6.3 Callee theorem reuse needed declaration assembly, not a new proof calculus

Ordinary Lean imports, named theorems and Aeneas's `[step]` registry suffice for
many caller/callee proofs. Our spec wrapper initially required a small registration
adapter because the registry inspects theorem types syntactically. Explicitly
expanding just the specification alias makes the existing registry usable.

**Useful improvements:** robust registration through transparent proposition
wrappers and structured declaration dependency feedback. Avoid requiring proof
order to follow source-comment order. Associated compiler/native identities and
real import dependencies are more reliable than a second custom proof graph.

### 6.4 Automatic model derivation has deliberate local limits

Our recursive *field composition* supports structural products, arrays, options
and selected wrappers, but our automatic *nominal declaration* derivation rejects
recursive/indexed groups and several richer generic shapes. These are not the
same restriction, and recursive Lean data extraction upstream does not imply
our decoders can be derived automatically for every such type.

Proof fields in mathematical model structures often follow from routine bounds.
We added decoder-scoped completion using ordinary tactics rather than imposing
a separate model-level proof language. Raw-to-mathematical bridges remain a
reusable-lemma opportunity. No extra upstream syntax is necessary for this
completion; Lean's elaborator/tactics already provide the mechanism.

### 6.5 Source meaning and editor support required local tooling

A proof can establish a proposition weaker than a reviewer intended. Our
independent required-contract families compare the authored contract against an
expectation for an arbitrary execution outcome before specializing to the actual
function. They are semantic sanity checks, not extra axioms or a replacement for
the Lean kernel. Reviewers still need to look for vacuous preconditions, early
returns and observations that discard the intended property.

Editing generated Lean gives native editor support but copying comments back was
awkward. Deterministic projections, source maps and guarded copy-back now support
that workflow. We track useful generated review snapshots separately from
unfinished editing state. These are integration affordances; they do not require
changing Aeneas's theory.

**Useful upstream interfaces:** stable names and source maps, native declaration
ranges and semantic metadata sufficient for robust tools. Do not confuse an
editor cache or projection with the authoritative proof source.

## 7. Reproducibility, deployment and historical tooling issues

### 7.1 Lean/Aeneas/Charon/Rust versions must move as a compatible set

Anneal v1 and zerocopy initially used different pins, which prevented a simple
shared-library code move. We updated Anneal, validated extraction fixtures and
bundles, and made Anneal's lockfile the source of truth. The shared `anneal/lean`
package separates pure Rust mathematics from Aeneas-dependent adapters; both
consumers use the same source.

The historical v1 wrapper also repairs a bare `@[discriminant]` annotation to
`@[discriminant isize]` and marks axiom-calling extracted functions noncomputable.
Those are recorded compatibility accommodations, not freshly reproduced defects
of every current zerocopy extraction.

**Needed support:** compatible, reproducible releases of the complete graph and
clear compatibility information. Keep consumer-specific extraction options and
patch identity explicit rather than silently forking pins.

### 7.2 Intel Mac distribution and native library bundling required extra work

The selected upstream release lacks an `x86_64-darwin` Aeneas archive, requiring a
source-build fallback. Charon's upstream nixpkgs dropped Intel Mac support, so
our packaging follows a compatible locked nixpkgs. Darwin library bundling and
signing needed adjustments for flags unsupported by the available signing tool.
A temporary installer path also needed replacing when Intel support disappeared.

These are deployment problems, not evidence that the proof semantics differ on
Intel. Native host validation checks the actual portable archive, relocation,
executables and Lean imports. Building OCaml/Rust/Lean dependencies from source
made Intel validation much slower than using supplied binaries.

**Useful improvements:** reproducible native archives for supported hosts, tested
relocation/read-only installation, complete dependency closure, and explicit
host retirement policy. Our bundle distribution reuses Anneal's existing
exocrate archive mechanism; no new global package manager was introduced.

### 7.3 Cached builds can validate a different source snapshot

We encountered stale-import acceptance while using Lake `--old`; changing source
could leave a previously compiled proposition in the environment. A proof audit
can faithfully inspect that stale environment and still miss the source change.
This is a cache/provenance failure, not a contradiction accepted by Lean's kernel
for the newly edited source.

**Workaround:** rebuild authored roots/shared sources and run source-mutation
controls. Final CI verifies exact source copies, extraction/configuration
identity, both golden/live builds and all discovered annotations. Development
may use incremental cached extraction, but labels its result provisional and
cannot substitute it for final verification.

**Useful improvements:** straightforward hermetic build entry points and
verifiable source-to-artifact identities. Faster development should avoid
unnecessary extraction without weakening the final path. Repeated fresh
admission/kernel checks are real integration cost; optimize through a justified
cache boundary, not by trusting stale reports.

### 7.4 Diagnostics and error provenance materially affect development time

Internal assertions, generic `Unsupported` errors and large mutually recursive
group dumps often identify an implementation location without explaining the
Rust dependency that imported it. Generated names and wrapper propositions can
also make tactic failures harder to relate to Rust.

Our workaround is small permanent native capability fixtures, preserved raw
errors and source snapshots, mapped Lean diagnostics, compiled inspection,
negative controls and exact pin records. A failing check must fail for the
intended reason; a new syntax error is not evidence that a safety audit works.

**Useful improvements:** structured errors naming original item, construct,
originating dependency edge, unsupported stage and available alternative; robust
minimal reproducers; and transactional output publication. Keep unsupported
cases as clear errors rather than generated holes that resemble success.

## 8. Historical findings and investigated capabilities

The reference research is broader than the current zerocopy implementation. We
mechanically searched all 658 `reports/*/REPORT.md` documents on its local branch;
416 mention Aeneas. We then reviewed the selected headings and passages for
additional limitation classes. That search improves coverage, but it does not
independently reproduce every historical assertion. In particular, none of these
reference documents names our October Aeneas pin. The following findings must
retain their original dates and evidence classifications.

Report names below are paths under that branch's `reports/` directory. Each
ends in `/REPORT.md`. The evidence section gives the repository and exact branch
checkpoint, so another researcher can read the original reports and artifacts.

### 8.1 Failed or concurrent generation can leave misleading artifacts

**Observed on older pins, September 29.** A nonzero Aeneas invocation wrote
partial Lean output containing `sorry`. Some partial output could compile with
`sorryAx`. Reusing an output directory after removing a trait or changing output
mode also retained old external templates. Distinct simultaneous requests could
leave artifacts from different requests in one destination.

A Charon 0.1.210 concurrency experiment found malformed JSON even when both
writers returned success: one of six direct collision rounds and one of three
Cargo collision rounds witnessed this. These counts are witnesses, not estimated
failure rates. Different files from `--format all` could also disagree about
completeness.

**Effect:** neither a successful Lean compilation, an existing file, nor the
status of one writer establishes that the complete intended program was
translated. Old declarations can outlive the source that justified them.

**Current defense:** private destinations, checked process status and completeness,
fresh final generation, source/dependency binding, and transitive axiom audits.
A legitimate external primitive is explicitly modeled; `sorryAx` is rejected.

**Useful upstream changes:** transactional publication after complete success,
explicit ownership of a destination, generation identifiers in all outputs,
structured success receipts and cleanup rules. A consumer should still avoid
sharing a destination across writers.

Evidence: `anneal-3730-aeneas-trait-output-shrink-matrix-2026-09-29`,
`anneal-3730-charon-aeneas-boundary-2026-09-29`,
`anneal-3730-aeneas-identity-manifest-2026-09-29`,
`anneal-3730-aeneas-process-contract-2026-09-29`, and
`anneal-3730-charon-concurrency-interruption-2026-09-29`.

### 8.2 A warm Cargo target can retain another source tree's generated input

**Observed on an older toolchain, September 29.** A copied source tree reused
another tree's Cargo target. Extraction saw the copied tree's edited function,
but also the original tree's path-dependent generated constant, `205`. A private
target for the copied tree yielded `217`. Both outputs reported
`has_errors: false`.

**Effect:** an error-free compiler extraction can combine subjects unintentionally
when build-script inputs and output provenance are not isolated. This is a build
identity failure, not evidence of an incorrect arithmetic translator.

**Defense and needed support:** isolate or rebuild when build origin changes;
record generated sources, build environment and compiler inputs as part of the
subject. Better upstream extraction receipts should identify those inputs.
Hashing only handwritten Rust or checking `has_errors` cannot detect this case.

Evidence: `anneal-3730-charon-warm-target-controls-2026-09-29`.

### 8.3 Optional termination generation and effect analysis had separate limitations

**Historical source findings, June 3; not reproduced on the October pin.** The
optional extrinsic termination mode emitted `termination_by`, `decreasing_by`
and `partial_fixpoint` in a combination incompatible with the inspected Lean
4.30.0-rc2 grammar. Lean decreases mode explicitly rejected mutual recursion,
and Lean fuel mode was unavailable.

A separate analysis treated trait-method calls as potentially failing but not
diverging or stateful. Such an analysis flag is not a theorem that every Rust
implementation terminates. These findings are distinct from the observed
exitless-loop rejection and from the backend's ability to denote divergence.

**Our use:** ordinary partial-fixpoint extraction with proof-time total/partial
WP and explicit termination measures. We do not use a native `can_diverge` flag
as proof of successful execution.

**Needed work:** regression-test optional termination output against its exact
Lean pin; give effect summaries an explicit meaning and conservative treatment
of unknown implementations. State, divergence and failure summaries must agree
with whatever effects callers are allowed to observe.

Evidence: `aeneas-extrinsic-termination-nightly-2026-06-03`,
`aeneas-infinite-diverging-execution-nightly-2026-06-03`, and
`aeneas-semantic-omissions-unsafe-rust-nightly-2026-06-03`.

### 8.4 The public libraries do not provide a request-safe incremental service

**Historical source investigation.** Aeneas's translation pipeline used mutable
process-global configuration and error state, recomputed whole-crate contexts,
and exposed no supported request/reset/cancellation/invalidation protocol.
Charon's compiler extraction driver lived in its binary rather than the public
`charon_lib` interface.

**Effect:** keeping one process alive does not automatically make extraction
incremental, isolated or safe to run concurrently. An interrupted request may
also have published partial artifacts. This matters to editor integrations and
our attempts to shorten the development loop.

**Current approach:** ordinary isolated processes; cache only at explicit input
boundaries; offer provisional local proof iteration separately from final CI.

**Needed support:** explicit session state and dependencies, cancellation and
publication semantics, and a reusable driver interface. An incremental daemon
would be useful only if it preserves subject identity and complete invalidation;
it is not needed for batch verification.

Evidence: `aeneas-library-process-architecture-nightly-2026-06-03`,
`aeneas-incremental-translation-feasibility-nightly-2026-06-03`, and
`charon-library-process-server-0-1-210`.

### 8.5 Alias, source-coordinate and safety metadata are not all retained

**Historical source findings and preserved coordinate observations.** Ordinary
Rust type aliases can disappear as independent declarations; generated comments
contain synthesized names and spans rather than the original prose. These are
source-identity limitations, separate from value semantics and nominal structs.

Charon serialized display-width columns, but `Loc::to_byte` added a column to a
byte offset. Wide, combining and other Unicode characters distinguish those
units. A plausible-looking source span is therefore not enough for byte-exact
annotation binding. Our newer physical annotation-origin records use byte
offsets; they do not retroactively change the meaning of the older span API.

The older semantic AST also omitted structural unsafe blocks, unsafe trait/impl
qualifiers and the distinction between static and mutable-static declarations;
function `is_unsafe` survived. Some Rust predicates were omitted, including
`ConstEvaluatable`, `WellFormed`, `HostEffect` and `ConstArgHasType`. The full Rust
well-formedness and authorization context cannot be reconstructed from the
remaining generic-clause list alone. Higher-ranked/lifetime precision also had
known restrictions.

**Effect:** source annotation coverage, safety review, constant-evaluation
premises and theorem binding require evidence from the stage that still has the
relevant fact. This does not mean every erased qualifier changes the functional
return value.

**Needed support:** explicitly typed span units, original byte ranges and owner
identities; retained safety/declaration facts; and a documented account of erased
predicates and their compiler-checked evidence. Ordinary aliases need source
correspondence, not necessarily distinct nominal Lean types.

Evidence: `aeneas-type-alias-handling-nightly-2026-06-03`,
`aeneas-rust-comment-preservation-nightly-2026-06-03`,
`end-to-end-source-correspondence-nightly-2026-06-03-v4-30-0-rc2`,
`cross-tool-utf8-span-columns-2026-09-27`,
`anneal-3731-i079-unicode-charon-spans-2026-09-30`,
`anneal-3731-i079-generated-file-charon-spans-2026-09-30`,
`charon-raw-pointers-unsafe-operations-0-1-210`, and
`charon-traits-generics-nightly-2026-06-03`.

### 8.6 Pointer casts, foreign interfaces and assembly lose distinctions needed by richer models

**Historical source findings; not executed zerocopy regressions on our pin.**
Several pointer cast/coercion and exposed-provenance operations became a common
`CastKind::RawPtr(src, dst)` form. That loss of the original operation's meaning
is separate from the later Lean pointer carrier lacking address and provenance.
A strict-provenance interpretation needs both pieces.

The inspected foreign-function representation omitted `c_variadic` and effective
link-name/ordinal information. Inline assembly omitted operands, register
constraints and options; global assembly was skipped. An external function body
or instruction-set model cannot reconstruct an interface promise already erased.

**Current policy:** these operations are outside our admitted execution fragment.
No general FFI, assembly or provenance claim follows from the byte mathematics.

**Needed support:** retain original cast reason and relevant foreign/assembly
interfaces, or reject them before erasure. Then supply explicit guarded semantic
boundaries. Merely accepting more final LLBC constructors would be insufficient.

Evidence: `charon-raw-pointers-unsafe-operations-0-1-210`,
`rust-extern-foreign-items-nightly-2026-05-31`, and
`rust-inline-global-assembly-nightly-2026-05-31`.

### 8.7 Existing resource-model research is not yet a source translation bridge

**Historical capability review, September 26–27.** The observed separation-logic
prototype, at upstream PR #1352 head `75fb1479…`, supplied typed-slot sequential
heap mathematics and proof interfaces. The reviewed source interpreter still
rejected raw-pointer dereferences. The work did not establish byte storage,
provenance, padding, partial initialization or concurrency semantics for our
extracted Rust.

**Implication:** we should reuse useful libraries, but importing a separation-
logic library or upgrading to a prototype does not itself prove that production
pointer operations have entered that model faithfully. The missing bridge needs
its own supported source fragment, primitive rules and preservation argument.

Evidence: `aeneas-separation-logic-status-2026-09-26` and
`iris-concepts-for-rust-aeneas-separation-logic-2026-09-27`.

Other surveyed historical research covered async/coroutines, experimental generic
const/effect/transmutability features and smart-pointer unsizing. We did not
establish that these blocked our current targets, so they are not presented as
encountered zerocopy regressions. Likewise, an old bound-lifetime resolution issue
was already closed before the June review. Anneal v1's safe-mutation/invariant
closure limitations belong to Anneal's policy and frontend; they are not Aeneas
translator defects. Our conditional contracts deliberately make a weaker claim.

## 9. Recommended upstream work, in order of near-term value

1. **Remove small, confirmed obstacles.** Expose nominal tuple extraction;
   fix duplicate parent-field naming and suffix reconstruction; make provided-
   method exclusion consistent; support explicit pretransformation snapshots,
   exact body-origin reporting and annotation provenance. Each has a narrow
   regression target and removes downstream repair or audit plumbing.
2. **Unblock faithful trait interfaces.** Translate residual associated equalities
   with evidence/transports, then handle the required recursive dictionary
   groups. Use the pointer-free recursive equality fixture before generic
   `KnownLayout`, and retain all Rust constraints throughout.
3. **Make primitive extension and execution admission explicit interfaces.** Bind
   original endpoints, semantic providers, effect classifications and native
   arguments. Preserve fatal forbidden execution, cleanup and implicit guards.
   Emit the information downstream tools currently reconstruct.
4. **Support the next control-flow cases.** Translate exitless loops without
   erasing their effects, and fix the never-returning conversion regression.
   These unlock real production paths before a full resource model exists.
5. **Add faithful pointer values and physical transfer semantics.** Separate
   address/provenance/metadata manipulation from memory permissions. Retain or
   conservatively abstract typed transfer, padding and initialization events.
   Numeric byte proofs and layout calculations can then connect to more actual
   pointer operations without overpromising liveness or provenance placement.
6. **Extend effects/resources only as demanded by the claim.** Independent byte
   choices, recoverable panic, concurrency, destruction and temporal ownership
   need compositional semantics. The existing interaction-tree and WP libraries
   provide infrastructure, but those Rust effects must enter the model and
   survive translation before proofs can discharge them.

The desired end state is not that Aeneas must infer every Rust safety argument.
It is that a downstream proof can state the intended abstraction and explicit
premises, and the extraction either preserves the observations needed for that
claim or rejects the program with a useful explanation. Much of our current
scaffolding exists to enforce that boundary externally.

## 10. Evidence and reproduction pointers

The strongest tracked entry points are:

- [LOWERING_AUDIT.md](LOWERING_AUDIT.md): constructor/handler audit and versioned
  representation premises; includes upstream source coordinates and links.
- [ADMISSION_DESIGN.md](ADMISSION_DESIGN.md): admitted operations, rejected effects,
  original/final inspection and required failure controls.
- [tests/capabilities/README.md](tests/capabilities/README.md): exact native
  `KnownLayout`, macro, primitive and pointer fixture outcomes and replay commands.
- [patches](patches/): the complete local upstream patches.
- [prepare.py](prepare.py), [NativeModels.lean](lean/NativeModels.lean),
  [Check.lean](lean/Check.lean), [ZeroedAudit.lean](lean/ZeroedAudit.lean), and
  [NativeProviderAudit.lean](lean/NativeProviderAudit.lean): naming repair,
  semantic suffixes, compiled and dependency audits.
- [RustRealizability.lean](lean/RustRealizability.lean),
  [TransmuteModel.lean](lean/TransmuteModel.lean), and
  [Proofs/GenericTransmute.lean](lean/Proofs/GenericTransmute.lean): current candidate
  byte bridge, ambiguity coverage and actual generic native proofs.

Historical evidence is preserved locally under the workspace's `.aeneas-work/`
container. Relevant directories include `erasure-audit-20261008`,
`trait-bound-capability-20261013`, `into-bytes-front-end-20261013/evidence`,
`existing-unsafe-path-probe-20261013`, `trait-read-tuple-evidence-20261014`,
`knownlayout-native-20261014`, `transmute-copy-state-20261015`,
`shared-pin-remote-validation-20261007`, and `shared-pin-bundle-evidence-20261007`.
These are historical evidence pointers, not repository-relative replay dependencies
or caches that CI must consume. Current fixtures and pinned commands are the
preferred starting point for a new reproducer.

The local `codex/anneal-sdk-reference-reports` branch retains earlier research in
`reports/*/REPORT.md`. Its reviewed checkpoint is
`a0ff759e7d2d9a953f0ac40b326dd23197bd9188`, in the migration's shared Git store
at `/Users/codex/Codex/Migrated/zerocopy/.git`. For example:

```bash
git --git-dir=/Users/codex/Codex/Migrated/zerocopy/.git show \
  a0ff759e7d2d9a953f0ac40b326dd23197bd9188:reports/anneal-3730-aeneas-trait-output-shrink-matrix-2026-09-29/REPORT.md
```

Those reports use several older pins and include successful capability tests as
well as failures. Their date, exact version and preserved stderr matter; a
historical failure must not silently become a claim about the current runtime.

For upstream source inspection, use the pinned
[Aeneas source tree](https://github.com/AeneasVerif/aeneas/tree/ca282ec2312a96f6a985a4d23a663690816d3f3e)
and [Charon source tree](https://github.com/AeneasVerif/charon/tree/cf02e3f228f97ee7be3a415be56989053063326d).
Source coordinates in this report refer to those trees unless explicitly marked
historical. Existing upstream facilities are often part of the solution; this
report should not be read as a proposal to reimplement their WP, borrow analysis,
trait dictionary extraction, arithmetic tactics or native metadata exporter.
