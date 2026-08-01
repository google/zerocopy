# Proof Obligations, Safety Contracts, and Local Proofs

## Contents

- [Form the theorem](#form-the-theorem)
- [Qualify applicability](#qualify-applicability)
- [Separate kinds of premises](#separate-kinds-of-premises)
- [Write safety documentation](#write-safety-documentation)
- [Write local safety proofs](#write-local-safety-proofs)
- [Carry invariants locally](#carry-invariants-locally)
- [Prove temporal behavior](#prove-temporal-behavior)
- [Cite authoritative axioms](#cite-authoritative-axioms)
- [Search for indirect derivations](#search-for-indirect-derivations)
- [Review a proof](#review-a-proof)

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
obligation until it reaches checked local facts, named invariants,
authoritative axioms, or explicit TCB entries.

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

## Separate Kinds of Premises

Classify every premise:

- **Local fact:** Established by inspected code, control/data flow, a type, or a
  named invariant. Cite the exact check, branch, assignment, ownership fact, or
  invariant clause.
- **Rust axiom:** Entailed by exact applicable text in a versioned Rust Reference
  or standard-library page. Quote and link it.
- **Selected safe-dependency fact:** Supplied by a deliberately selected safe
  dependency contract and recorded in the TCB.
- **Tool-derived fact:** Established by a verified tool theorem whose exact
  proposition, model, scope, and premises entail the local fact. Record only its
  residual unproved tool/model/translation premises in the TCB.
- **Additional assumption:** External specification, unsafe dependency,
  compiler implementation, platform behavior, deployment restriction,
  probabilistic premise, or other admitted proposition recorded in the TCB.

Never blur an assumption into a derived fact. If a premise does not fit one of
these classes, the proof is incomplete.

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
// Facts:
// - F1 follows from <exact check, type fact, or invariant clause>.
// - F2 follows from TCB-... / AXIOM-... .
// Derivation:
// - F1 and F2 imply P1 because ...
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

## Cite Authoritative Axioms

For every Rust or standard-library ground-truth proposition:

1. Select documentation applicable to the audited compiler/library version.
2. Link the narrowest applicable sections, including versions in the URLs.
3. Quote the smallest sufficient set of excerpts whose propositions participate
   in the derivation.
4. State the proposition derived from each excerpt and justify the inference
   that combines them.
5. Check that qualifications, definitions, linked clauses, and surrounding
   scope do not weaken it.
6. Have the reviewer open the source and independently confirm the derivation.

Apply [Qualify applicability](#qualify-applicability) when a citation and the
claim concern different Rust versions.

If the Reference or standard-library documentation is missing, ambiguous,
internally inconsistent, or too weak, record the exact missing proposition.
Treat explanatory sources or current implementation behavior only as leads or
explicit additional assumptions. Recommend an upstream documentation report
when appropriate.

## Search for Indirect Derivations

Do not equate the absence of a single direct documentation sentence with the
absence of a proof. Before reporting an authoritative documentation gap or
finalizing an important obligation as unproved:

1. Restate the exact semantic property required and unfold relevant project
   definitions.
2. Search for applicable direct guarantees.
3. Search for stronger, more general, or orthogonal authoritative facts whose
   conjunction could entail the property.
4. State every intermediate lemma and justify each inference rather than merely
   collecting citations.
5. Check the applicability of every premise and intermediate lemma.
6. Try to construct a model that satisfies the premises while falsifying the
   conclusion. If one remains possible, identify the missing implication.

This search does not weaken the fail-closed rule. If no complete admissible
derivation is established, the obligation remains unproved. Distinguish “this
audit did not complete a proof” from the stronger claim that authoritative
documentation cannot support one.

When a universal soundness derivation does not close, separately ask whether
the established facts close an existential refutation. Identify a valid
in-scope use or execution, prove reachability of the relevant operation or
semantic event, prove its exact required safety proposition false there, and
trace that failure to the applicable authoritative or explicitly trusted UB
consequence. If every link is proved, apply `UNSOUND`; if any link is absent,
the failed universal obligation remains `UNPROVED`. Do not demand a fact about
every input to establish one existential witness, and do not infer a witness
merely from the absence of a universal proof.

## Review a Proof

For each proof:

1. Reconstruct the required preconditions from the callee or language/library
   contract rather than trusting the comment's summary.
2. Open every citation and verify its exact proposition, version, and scope.
3. Check each claimed local fact—including its quantifier, producer/transition
   history, and applicability domain—against the actual dataflow and all
   alternative paths.
4. Expand every named invariant and ensure it is established initially and
   preserved by every permitted transition.
5. Check quantifiers, arithmetic boundaries, zero-sized and empty cases,
   overflow, partial initialization, overlapping ranges, alias duration,
   provenance, destruction, unwinding, reentrancy, concurrency, and
   configuration-dependent behavior when relevant.
6. Verify every postcondition used downstream.
7. Search for circularity, vacuity, hidden trust, and stronger conclusions than
   the cited facts entail.
8. Record every missing implication so it cannot be forgotten, apply
   [Search for indirect derivations](#search-for-indirect-derivations), and
   apply the verdict certificate in `SKILL.md`: report `UNPROVED` if a required
   implication remains absent and no existential refutation closes, or the
   applicable refutation verdict if one does.

If validation requires a material derivation absent from the existing safety
comment, include that reconstructed derivation—or the smallest missing
portion—in the review. A derivation is material when it supplies a necessary
logical bridge that is neither stated nor an immediate syntactic or
type-enforced fact visible at the proof site. Give its citations,
applicability, and relationship to the required preconditions and
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
