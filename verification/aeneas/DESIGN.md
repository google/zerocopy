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
or `partial spec`. Original source type parameters and value arguments are
inferred from the verified extraction. Every original type parameter receives
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

Goldens contain complete generated modules. CI checks conservative fuzzy
textual equivalence and independently compiles proofs, required comparisons,
corollaries, and axiom audits for both golden and live models. Inline
mathematical decoders never replace the live extracted function definitions.
Both builds establish the checked properties, not equivalence of all unclaimed
behaviors.

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
- **Broader carriers and effects.** Recursive nominal groups, indexed carriers,
  trait/const generics, and escaping borrow reconstruction remain unsupported
  with explicit errors. Add semantics and admission checks before accepting
  them. Stateful or nondeterministic APIs may need observable traces and
  effects, rather than only result contracts.
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
