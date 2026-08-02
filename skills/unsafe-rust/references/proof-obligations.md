# Proof Obligations, Safety Contracts, and Local Proofs

## Contents

- [Form the theorem](#form-the-theorem)
- [Qualify applicability](#qualify-applicability)
- [Build the evidence-bearing proof kernel](#build-the-evidence-bearing-proof-kernel)
- [Close and lint the proof kernel](#close-and-lint-the-proof-kernel)
- [Certify valid uses](#certify-valid-uses)
- [Write safety documentation](#write-safety-documentation)
- [Write local safety proofs](#write-local-safety-proofs)
- [Carry invariants locally](#carry-invariants-locally)
- [Prove temporal behavior](#prove-temporal-behavior)
- [Review and reconstruct a proof](#review-and-reconstruct-a-proof)

## Form the Theorem

Turn each soundness claim into explicit propositions before writing prose.

For an unsafe API, use this shape:

> For every state and input satisfying preconditions `P`, every permitted
> execution of the implementation is free of undefined behavior and establishes
> documented postconditions `Q`, relative to TCB `T`.

Include ongoing and terminal obligations in `P`; a precondition need not concern
only the instant of the call. State who must maintain each fact, over what
interval, and what event discharges it.

For a safe API, prove soundness with no caller-side safety precondition beyond
well-typed safe use. Also prove any postcondition consumed by the soundness
argument and any broader behavior explicitly placed in scope. Ordinary input
validation may reject values, return an error, or panic as documented, but
soundness may not depend on the safe caller honoring an unenforced rule.

For each local proof site:

1. Obtain the exact preconditions of the operation or contract being used.
2. Normalize conjunctions, implications, quantifiers, lifetimes, and temporal
   clauses into separately reviewable obligations.
3. Derive every obligation from facts available at that point.
4. Obtain and prove every postcondition used later.
5. Establish the invariant state after success and every alternative exit.

Treat every operation, declaration, implementation, or state transition that
supplies or consumes a safety contract as an obligation site. Follow each
obligation until it reaches checked artifact facts, closed derived lemmas or
invariants, authoritative axioms, or explicit TCB entries.

Apply the quantifier-sensitive verdict certificates in `SKILL.md` when a
derivation fails or produces a counterexample. Do not confuse failure of a
universal proof with proof of an existential refutation.

## Qualify Applicability

State or inherit the exact domain of every claim and premise. Include whichever
dimensions can change the proposition, such as:

- source and generated-artifact identity;
- inputs, states, types, signatures, lifetimes, and execution intervals;
- Rust, compiler, standard-library, dependency, and external-contract versions;
- targets, features, profiles, build inputs, and other supported
  configurations; and
- deployment or probabilistic restrictions for separately qualified claims.

A derivation proves only the cases in which every consumed premise applies. If
one proof does not cover the full required domain, partition the claim into
cases, prove each case, and establish that their union is exhaustive. Do not
turn an uncovered case into an implicit exclusion.

Avoid repetitive local boilerplate. A proof may inherit applicability from an
exactly identified project support policy, invariant definition, axiom entry,
or TCB entry. The local proof must still make the inheritance and relevant case
clear enough to review.

Derive the required toolchain/configuration projection and every transformation
of that projection under
[Recover the required supported set](configurations-and-generated-code.md#recover-the-required-supported-set),
then carry it through every premise and case lemma below. The domain covered by
a derivation is the intersection of the applicability domains of every premise
it consumes; the union of valid case lemmas must contain the required domain.

A documented Rust guarantee from version `R` may support a later stable version
only when an exact Rust backwards-compatibility commitment preserves that exact
semantic proposition throughout the later version's relevant edition, target,
feature, and configuration domain. Under this skill's authority policy, record
a compatibility commitment outside the Rust Reference or standard-library
documentation as an explicit TCB premise. An API's stability or `since` badge
establishes only what its applicable authoritative text says it establishes; it
does not by itself prove that every behavioral sentence in current
documentation was guaranteed from that version. Do not extend a guarantee
beyond its original domain or automatically to unstable features,
`RUSTC_BOOTSTRAP`, `-Z` behavior, implementation details, custom targets,
platform availability, or pre-stabilization behavior.

Compatibility does not propagate guarantees backward. Text first documented in
version `R` does not by itself prove the same proposition for earlier versions.
A later clarification can support an earlier version only when applicable
authoritative text expressly gives it historical scope or an accepted TCB
premise establishes that the guarantee already applied. Unchanged
implementation, version history, a documentation diff, or advisory prose is
insufficient by itself. Split the version domain if later text qualifies or
contradicts the older statement. For an open-ended toolchain range, either
prove the claim parametrically relative to a named compatibility premise or
state an audit cutoff and later-release re-audit trigger. A compatibility
premise about abstract semantics does not prove correctness of future compiler
binaries.

Before issuing any affirmative result spanning multiple Rust releases, record
the exact required release predicate and one coverage basis:

- an applicable parametric derivation over the whole predicate;
- an exhaustive partition with applicable premises for every class or member;
  or
- an exact proposition-preserving backwards-compatibility premise whose domain
  covers every later release claimed.

Endpoint documentation, sparse version samples, an earliest supported release,
and an audit cutoff do not prove the releases between them. If the coverage
basis does not contain the claimed release predicate, narrow the proved region
and leave the remainder `UNPROVED`.

## Build the Evidence-Bearing Proof Kernel

Express every material derivation as reviewable edges of this form:

```text
artifact facts
  + applicable Rust/stdlib axioms, verified tool theorems,
    or explicit TCB premises
  + earlier proved lemmas or invariants
  + explicit logic or mathematics
  -> derived proposition
  -> consumer
```

Classify every proposition or premise:

- **Artifact fact:** A literal property of the exact inspected source,
  expansion, generated output, metadata, or other artifact. Cite the location
  or identity that exhibits it. Artifact facts include that tokens,
  declarations, annotations, expressions, branches, attributes, or lexical
  token/AST ordering occur; they do not include the runtime value relation,
  execution order, or other semantic effect of those constructs.
- **Rust axiom:** A semantic proposition entailed by exact applicable text in a
  versioned Rust Reference or standard-library page. Quote and link it.
- **Derived lemma or invariant:** A proposition already derived from identified
  artifact facts, axioms, prior lemmas, and explicit inference. Cite its
  canonical proof and applicability rather than treating its name as a premise.
- **Selected safe-dependency fact:** Supplied by a deliberately selected safe
  dependency contract and recorded in the TCB.
- **Tool-derived fact:** Established by a verified tool theorem whose exact
  proposition, model, scope, and premises entail the needed proposition. Record
  its residual unproved tool/model/translation premises in the TCB.
- **Additional assumption:** External specification, unsafe dependency,
  compiler implementation, platform behavior, deployment restriction,
  probabilistic premise, or other admitted proposition recorded in the TCB.

Pure logic and mathematics need no Rust citation, but state every material step
or witness. Never blur an assumption into a derived fact. If a proposition or
premise does not fit one of these classes or a material inference is unstated,
the proof is incomplete.

Source inspection is not a shortcut around semantic authority. Seeing an `if`,
call, operator, type annotation, match, attribute, or tail expression proves
that the construct occurs. Claims about evaluation order, branch or arm
selection, return, arithmetic, inhabited values, name access, typing/coherence,
configuration selection, or caller-side unsafe obligations require the exact
applicable Rust or library propositions. A proof may derive control flow and
dataflow locally, but those are conclusions from artifact facts plus semantics,
not raw facts supplied by inspection.

For every inferential edge consumed by a certified conclusion, record:

1. the exact conclusion and applicability domain;
2. every premise, its class, source, and applicability;
3. the inference by which the premises entail the conclusion; and
4. the operation, later lemma, postcondition, or verdict that consumes it.

### Preserve Producer Quantifiers

Distinguish the validity of a value of type `T` from a stronger library
invariant attached to its role in an abstraction. Prove both when needed.

Never promote one producer's admission contract into an invariant of its output
type. A constructor, conversion, deserializer, FFI ingress, mutation, or other
producer precondition applies at that invocation. It supports a fact about that
particular result only through a proved postcondition or dataflow relation; it
does not prove that every valid value came through that producer or that later
transitions preserve the property.

To rely on `I` as an invariant of every value in a stated set, provide a
complete derivation over that set without reversing the producer implication.
Such a derivation may, for example, use:

1. applicable authoritative premises that entail `I` for every value in the
   set;
2. an enforced abstraction boundary plus a complete proof that every in-scope
   ingress and producer establishes `I` and every transition preserves it;
3. another applicable derivation, including a verified tool theorem, that
   entails the exact quantified proposition; or
4. the exact universal proposition as an admissible accepted TCB premise under
   the TCB rules.

This enumeration does not replace the entailment requirement or exclude other
valid proof forms. A consumer may instead establish `I` for its particular
values or quantified subset from local checks, proved producer and transition
history, and other applicable premises. If neither derivation closes, leave
the consuming obligation `UNPROVED`.

Likewise, distinguish:

- permission to perform an operation;
- facts established by that operation;
- facts merely preserved by it;
- obligations transferred to a returned pointer, reference, guard, token, or
  caller.

## Close and Lint the Proof Kernel

A proof may be compact, but a reviewer must be able to reverse it. A premise,
intermediate proposition, applicability restriction, or inference is material
when deleting it leaves the remaining explicit kernel insufficient to entail a
certified conclusion; a countermodel may demonstrate that insufficiency. State
every such component. An immediately checkable material artifact fact may be
recorded by an exact cited location without reproducing its literal tokens, but
it may not be absent. Omit only a purely logical rearrangement of already
explicit premises. Never omit the semantic proposition assigned to syntax.

Do not hide a material component behind a name such as “layout rules,” “cfg
semantics,” “the build mapping,” or “the type guarantees it.” A citation verifies
only the proposition the proof extracts from it; an allowlisted page or another
clause on the same page does not silently fill an unstated premise. Unfold
composite behavior to the clauses actually used. When build or generation
stages are relevant, apply
[Prove build and generation pipelines](configurations-and-generated-code.md#prove-build-and-generation-pipelines).

The ordinary proof prose or obligation ledger may carry the kernel. Do not
create a separate graph when the existing proof is already reverse-traceable.
Before certifying `PROVED`, `UNSOUND`, `CONTRACT-BROKEN`, or any regional
result:

1. start at every conclusion used by the certificate and recover its full-case
   applicability, every edge, and every intermediate proposition;
2. check each artifact fact against its exact identity and location, retaining
   material operation order and alternative exits;
3. check every Rust semantic premise against its stated exact proposition,
   versioned quotation, link, qualifications, and applicability;
4. check every other semantic premise against its verified tool theorem,
   dependency contract, or accepted TCB entry;
5. check material mathematical and logical steps by their explicit derivations
   or witnesses; they need no Rust citation;
6. write an implication or quantified proposition for each citation-to-claim
   edge; reject any unjustified converse, inverse, strengthening, or domain
   widening, and state any contrapositive step with its exact negation and
   domain;
7. ensure no projection, shorthand, page-level citation, or later-stage result
   silently supplies a missing premise; and
8. trace forward through every relevant exit to prove the postconditions and
   invariants consumed later.

If a required component remains absent, remove every conclusion that depends on
it, assign a stable root blocker/gap ID to the smallest missing implication,
and apply the exact verdict certificate. Give every dependent obligation a
disposition, but mark it with that root blocker/gap ID rather than presenting
the same omission as multiple independent defects.

Do not equate the absence of one direct sentence with the absence of a proof.
Before declaring a semantic leaf missing, restate the exact proposition,
unfold relevant definitions, search for direct and stronger or orthogonal
applicable guarantees, combine them through explicit intermediate lemmas, and
try to construct a model satisfying the premises while falsifying the goal.
If a model remains possible, state the smallest missing implication. If the
Reference or standard-library documentation is ambiguous, inconsistent, or too
weak, record that exact gap, treat explanatory sources or implementation
behavior only as leads or explicit TCB assumptions, and suggest a narrowly
scoped upstream documentation improvement.

## Certify Valid Uses

A universal API theorem quantifies over its exact valid-use domain, and any
existential refutation needs a proved valid in-scope witness. Establish that
domain generally or instantiate these propositions for the proposed witness:

1. **Scope and source selection:** the relevant item, expansion,
   implementation, or entrypoint exists and is selected in the exact case.
2. **Boundary access and inputs:** a library caller can reach the exposed
   boundary and supply every caller-controlled argument, implementation, or
   capability used by the path; a binary or other entrypoint can receive the
   permitted input/environment that starts the execution. Derive
   implementation-internal values later in the separate execution-reachability
   proof.
3. **Typing and coherence:** the complete use is well typed; every generic,
   trait, lifetime, visibility, coherence, and implementability requirement is
   satisfied.
4. **Boundary contracts:** every applicable documented unsafe caller or
   implementer obligation owned outside the audited scope—including an
   obligation imposed on caller or implementer code supplied by the witness—is
   satisfied. No prose-only condition is imposed on a safe boundary. Do not
   assume an in-scope audited impl, declaration, or boundary assertion; it may
   be the safety proposition the later `UNSOUND` certificate proves false.
5. **Unsafe-context obligations:** every corresponding caller- or
   implementer-side compiler-enforced unsafe-context requirement at the exposed
   call, impl, field, macro, FFI, or other boundary is absent or satisfied.
   This is distinct from the truth of the in-scope safety assertion under
   audit.
6. **TCB qualification:** every dependency, external, deployment, or other
   admitted premise used to validate the path is explicit and applicable.

These are semantic propositions. For example, the inspected absence of the
token `unsafe` in a function declaration does not by itself prove the exact
caller obligation; cite the applicable language rule. For `UNSOUND`, combine
the valid-use certificate with separate execution-reachability, false safety
proposition, and UB-consequence edges. For `CONTRACT-BROKEN`, combine it with a
whole-execution UB-freedom proof and postcondition refutation. Apply the same
discipline, adapted to the proposition being proved, to any other existential
use or execution claim. A purely mathematical witness for a set relation
instead uses the certificate for that relation; it does not acquire
inapplicable API-boundary fields.

## Write Safety Documentation

Give every unsafe function, trait, impl, field, macro boundary, and other unsafe
contract a precise safety specification regardless of visibility. Use `# Safety`
documentation for public contracts. A private contract may cite module-owned
invariants, but must still state every fact its callers or implementers must
establish or continue to uphold. Use precise subjects, intervals, and
quantification.

A complete unsafe API contract should make the following derivable whenever
applicable:

- which values, memory regions, objects, threads, or executions it covers;
- validity, initialization, alignment, size, provenance, accessibility,
  lifetime, aliasing, exclusivity, mutability, and ownership requirements;
- concurrency, atomic ordering, synchronization, reentrancy, callback, signal,
  and thread-affinity requirements;
- target, ABI, feature, allocator, unwinding, linkage, or environmental
  restrictions;
- what may be observed, read, written, moved, copied, destroyed, or retained;
- whether an invariant may be suspended, for how long, and what must not happen
  before restoration;
- obligations attached to return values or capabilities;
- behavior on panic, unwind, cancellation, early return, or partial progress;
- documented postconditions on success and every other documented outcome.

Use this list as a discovery prompt. Derive the actual requirements from the
exact operation and applicable authoritative contracts, and add every other
obligation those contracts create.

Define relative terms. Replace phrases such as “valid pointer,” “properly
initialized,” “no aliases,” “live,” “same allocation,” “correct layout,” and
“used normally” with the exact propositions intended. Do not use “the caller
guarantees” unless the current boundary is unsafe and its documentation actually
requires the cited fact.

Safety preconditions must be sufficient; they need not be mathematically
weakest. Nevertheless, avoid irrelevant or unknowable conditions. Every stated
condition becomes part of the API contract and its evolution constraints.

Document postconditions with the same precision. If callers may rely on a
result, state:

- the state/value relationship established;
- the resources, aliases, or ownership transferred;
- which prior invariants remain true;
- when the guarantee begins and ends;
- distinctions among normal return, error, panic, and unwind.

## Write Local Safety Proofs

Place a `SAFETY` comment immediately adjacent to the smallest cohesive unsafe
operation or block. Prefer one proof unit per independently reviewable
obligation set.

For new code, require an explicit `unsafe { ... }` block for each unsafe
operation even inside an `unsafe fn`, and enable `unsafe_op_in_unsafe_fn` at
`deny` or `forbid` when compatible with project policy. Use documentation and
undocumented-unsafe-block lints as completeness aids where available; lint
success is not a proof.

Use this structure:

```rust
// SAFETY:
// Obligation: `<operation>` requires P1, P2, and P3.
// Artifact facts:
// - A1: <literal construct or lexical token/AST ordering> occurs at <location>.
// Semantic premises:
// - S1: AXIOM-... / TCB-... states <exact applicable proposition>.
// Derivation:
// - A1 and S1 imply P1 because ...
// - ...
// Result:
// - The operation establishes Q.
// - Q re-establishes/preserves/transfers invariant I.
unsafe { operation() }
```

Use ordinary prose when clearer, but retain each logical component. Do not write:

- “safe because this is unsafe code”;
- “the pointer is valid” without defining and proving the required properties;
- “checked above” without identifying the dominating check and relevant values;
- “guaranteed by the type/caller/API” without naming the exact contract clause;
- “this is how the standard library does it”;
- “Miri/tests pass” as a universal derivation;
- “obviously,” “trivially,” or “cannot happen” in place of proof;
- circular arguments in which an invariant is justified only by code that
  already assumes it.

A proof may cite a canonical checked proof or TCB entry to avoid duplicating
large quotations. Keep enough local text to show which proposition is used and
how it entails the local obligation.

When one unsafe block contains multiple operations, prove each operation in
program order. Include facts established by earlier operations only after
proving those operations' postconditions.

## Carry Invariants Locally

State each safety invariant near the representation or boundary that owns it.
Give it a stable name when multiple proofs cite it. Specify:

- the objects and states over which it quantifies;
- when it is required to hold;
- who may rely on it;
- every operation permitted to establish, mutate, suspend, transfer, consume,
  or destroy it;
- what must be true while it is suspended;
- how panic, unwind, cancellation, reentrancy, callbacks, and destruction affect
  it.

Define the invariant's actual enforcement boundary and prove every producer,
transition, and consumer within it. Apply
[Use module privacy](api-boundaries-and-evolution.md#use-module-privacy) to
choose that boundary for new code or compute the real access region of existing
code.

An invariant is local when each consumer can cite a named proposition whose
current truth is established by a local boundary. Its subject may still be
global state. Do not accept an informal “global invariant” that no boundary
owns or re-establishes.

## Prove Temporal Behavior

Treat time and interference explicitly:

- Determine the interval during which each pointer, reference, lock, capability,
  borrow, allocation, and invariant fact remains usable.
- Check every possible intervening call, callback, destructor, panic, unwind,
  cancellation point, signal interaction, and reentrant entry.
- For concurrency, quantify over every permitted thread interleaving and weak
  memory behavior within scope, not one observed schedule.
- If an operation returns a capability whose safe methods could violate an
  invariant, place the ongoing obligation in the unsafe boundary's contract or
  return a representation that enforces it.
- If a guard restores an invariant in `Drop`, prove restoration on all paths on
  which `Drop` runs and separately address paths on which destruction can be
  skipped, duplicated, reordered, or aborted.
- If an invariant is suspended across code not controlled by the abstraction,
  treat that code as adversarial unless it is an explicitly trusted dependency.

Cryptographic infeasibility and low probability do not turn a possible
execution into an unconditional Rust soundness proof. Move such premises to an
explicit conditional application claim and TCB entry.

## Review and Reconstruct a Proof

For each proof:

1. Reconstruct the required preconditions from the callee or language/library
   contract rather than trusting the comment's summary.
2. Open every citation and verify its exact proposition, version, and scope.
3. Check each artifact fact against the exact artifact, and each derived local
   lemma—including its quantifier, producer/transition history, and
   applicability—against its complete kernel, dataflow, and alternative paths.
4. Expand every named invariant and ensure it is established initially and
   preserved by every permitted transition.
5. Check quantifiers, arithmetic boundaries, zero-sized and empty cases,
   overflow, partial initialization, overlapping ranges, alias duration,
   provenance, destruction, unwinding, reentrancy, concurrency, and
   configuration-dependent behavior when relevant.
6. Verify every postcondition used downstream.
7. Search for circularity, vacuity, hidden trust, and stronger conclusions than
   the cited facts entail.
8. Apply [Close and lint the proof kernel](#close-and-lint-the-proof-kernel)
   to every conclusion used by a verdict or regional result and every claimed
   set relationship.
9. Record every root missing implication and blocked dependent conclusion, then
   apply the verdict certificate in `SKILL.md`: report `UNPROVED` if a required
   implication remains absent and no existential refutation closes, or the
   applicable refutation verdict if one does.

If validation requires a material derivation absent from the existing safety
comment, include that reconstructed derivation—or the smallest missing
portion—in the review. Apply the material-component definition in
[Close and lint the proof kernel](#close-and-lint-the-proof-kernel). Give its
citations, applicability, and relationship to the required preconditions and
postconditions. Report the implementation result separately from the deficient
proof artifact:

- If the reconstruction succeeds, the implementation obligation may be proved,
  but report the inadequate comment and provide proposed replacement wording.
- If the reconstruction fails, leave the obligation unproved unless it instead
  closes one of the existential certificates in `SKILL.md`.

When changes are authorized, update the adjacent proof rather than leaving the
reconstructed reasoning only in the review. A canonical checked proof or named
invariant may hold shared detail; do not demand redundant prose when the local
comment already identifies the exact proposition and complete derivation path.

Do not use reconstruction to repair a caller-facing contract retroactively. An
undocumented caller obligation remains hidden under the current API contract,
even if adding it would make the implementation proof succeed.

These examples identify common omissions; they are not a substitute for reading
the applicable authoritative contracts.
