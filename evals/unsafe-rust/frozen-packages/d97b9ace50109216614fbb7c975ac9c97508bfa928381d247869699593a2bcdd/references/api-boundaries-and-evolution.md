# API Boundaries, Invariants, and Contract Evolution

## Contents

- [Enumerate every surface](#enumerate-every-surface)
- [Place the safety boundary](#place-the-safety-boundary)
- [Use module privacy](#use-module-privacy)
- [Handle unsafe fields](#handle-unsafe-fields)
- [Audit traits and sealing](#audit-traits-and-sealing)
- [Audit macros and hidden APIs](#audit-macros-and-hidden-apis)
- [Distinguish selected dependencies from caller code](#distinguish-selected-dependencies-from-caller-code)
- [Prove documented behavior](#prove-documented-behavior)
- [Evolve contracts deliberately](#evolve-contracts-deliberately)

## Enumerate Every Surface

For soundness, enumerate every language-reachable way untrusted safe code can
construct, obtain, observe, mutate, replace, borrow, move, copy, drop, implement,
or invoke the abstraction.

Apply this checklist explicitly:

- public fields;
- constructors, including literals, constants, defaults, conversions,
  deserialization, builders, and generated constructors;
- safe inherent and extension methods;
- safe trait methods, blanket implementations, default methods, trait objects,
  and auto traits;
- public associated types and constants where their choices affect unsafe code;
- safe free functions and statics;
- indexing, dereference, iteration, operators, formatting, cloning, comparison,
  hashing, panic, and destruction behavior when implemented;
- exported declarative macros, procedural macros, derives, attributes, and APIs
  produced by them;
- reexports and feature- or target-dependent public items;
- callbacks and user-provided implementations invoked internally;
- FFI entrypoints callable without a Rust-side unsafe obligation;
- language-reachable `#[doc(hidden)]` items.

This is an advisory discovery list, not an exhaustive statement of Rust's
semantics. Inspect the exact source, expansions, metadata, and applicable
authoritative documentation for additional surfaces.

For each safe surface, prove that every behavior available to well-typed safe
code preserves soundness. For each unsafe surface, prove that its complete
documented contract is sufficient and that its implementation establishes all
documented postconditions for every valid use.

Determine the controlling contract from the actual published or otherwise
applicable normative text. Examples, rationale, tests, names, existing safety
comments, and inferred design intent may aid discovery but may not narrow or
replace that contract.

## Place the Safety Boundary

Mark an operation unsafe when callers or implementers must establish a
soundness-critical proposition that the implementation cannot establish from
enforced types, checked state, module-owned invariants, and deliberately trusted
dependencies.

Do not expose a safe API with a prose-only safety precondition. Documentation
cannot make a well-typed safe use invalid for the purpose of soundness.

Conversely, do not move an obligation to callers merely because doing so is
convenient. A safe wrapper may discharge an unsafe callee's requirements with
validation, construction, privacy, typestate, synchronization, or a local proof.

Treat each unsafe declaration or call as a contract boundary. An unsafe helper
can propagate an obligation through fields and later calls without immediately
performing an operation that exhibits undefined behavior. Follow the obligation
through the dataflow until it is discharged.

An `unsafe impl` is an assertion that the implementation satisfies the unsafe
trait's contract. Prove that assertion and every method-level obligation.

For FFI declarations, distinguish the declaration-time assertion that the
foreign contract is correct from each call's preconditions and from the foreign
implementation's behavior. Record external ABI and implementation trust
explicitly.

## Use Module Privacy

For new invariant-bearing representations:

1. Put the representation and all safely accessible fields in the smallest
   practical leaf module.
2. Keep those fields private to that module.
3. Make all code outside the module—including parents, siblings, cousins, and
   the rest of the same crate—use checked safe APIs or documented unsafe APIs.
4. Treat each operation inside the module that can affect the invariant as a
   proof site.

Do not use `pub(super)`, `pub(crate)`, or another broad safe visibility merely
because current same-crate code is trusted socially. Such visibility expands
the region in which safe edits can silently violate the invariant and makes
human review materially harder.

Existing crates need not be rejected solely for violating this authoring
discipline. Compute and audit the actual Rust visibility region, including
fields in ancestors or descendants that the code can access and all code that
can access the representation. Report broad safe visibility as proof-surface
debt.

Represent every distant fact by a named invariant or contract that each producer
preserves and each consumer can use locally.

## Handle Unsafe Fields

When the exact audited Rust version supplies compiler-enforced unsafe fields, a
properly declared unsafe field is an explicit unsafe API boundary. It may have
any intentional visibility, analogously to an unsafe function, because untrusted
safe code cannot perform the gated uses without accepting its documented
obligations.

Require field documentation to make the obligations for all applicable
operations derivable, including:

- initialization and replacement;
- reads, copies, and moves;
- shared and mutable borrows;
- pattern matching, destructuring, aggregate update, and whole-value operations;
- writes through direct access or an escaped capability;
- transfer or suspension of the enclosing invariant;
- the state required before control returns to untrusted safe code.

Audit the exact compiler version's enforcement rather than assuming a proposed
or future design. Separately prove every implicit safe action not gated by field
projection, especially destruction and compiler- or derive-supplied trait
behavior. An unsafe modifier does not relax the language validity invariant of
the field's Rust type and does not make arbitrary drop glue conditional.

When authoritative Reference or standard-library text does not specify the
feature sufficiently, record the exact semantics relied upon as a documentation
gap and explicit TCB premise. An RFC or current implementation may explain the
intent but is not a Rust axiom under this skill's authority policy.

## Audit Traits and Sealing

Treat every safe trait implementation supplied by a caller as adversarial safe
code. Unsafe code may rely only on facts enforced by Rust's types and semantics,
module-owned state, or explicit TCB entries—not on a caller faithfully
implementing behavioral prose.

If unsafe code requires an implementer to uphold a soundness-critical
obligation, use one of these structures:

- make the trait unsafe and document the complete implementer contract;
- seal the trait so only deliberately controlled implementations are possible;
- validate the needed property before unsafe use;
- redesign the representation or boundary so the property follows locally.

Prove that sealing is effective under Rust privacy and name resolution for every
supported configuration and macro expansion. A documentation claim,
`#[doc(hidden)]`, obscure path, or conventional “sealed” name does not by itself
prevent downstream implementations.

For an unsafe trait:

- state representation and behavioral obligations at the trait and method
  levels;
- prove every in-scope `unsafe impl`;
- ensure safe methods remain sound for every valid implementation;
- ensure generic unsafe consumers rely on no stronger fact than the contract;
- audit associated types, constants, default methods, specialization, trait
  objects, auto traits, negative impls, and generated impls when applicable.

For a sealed safe trait, selected implementations may be audited as controlled
code, but downstream safe callers remain adversarial. Recheck sealing whenever
visibility, reexports, macros, or configuration changes.

## Audit Macros and Hidden APIs

Classify a macro invocation by the obligations rustc actually enforces for the
expanded use, not merely by the absence or presence of `unsafe` in the invocation
tokens. A macro can be constructed so that expansion succeeds only in an unsafe
context. If no caller-side unsafe obligation is compiler-enforced, treat the
macro as a safe API and prove every accepted safe invocation sound.

Auditing only handwritten macro or proc-macro source is insufficient when sound
output depends on:

- caller tokens, types, paths, hygiene, spans, or name resolution;
- `cfg`, features, target facts, environment, or build-script data;
- generated identifiers, item visibility, attributes, or impl selection;
- compiler expansion order or version;
- downstream code into which the macro expands.

Inspect expansions to discover API and caller obligations. Then apply
[Audit generated and expanded code](configurations-and-generated-code.md#audit-generated-and-expanded-code)
to prove closure over every supported accepted input, output, and
configuration. Include generated public APIs in the same safe/unsafe surface
audit as handwritten items.

Treat `#[doc(hidden)]` as a documentation and compatibility signal only to the
extent promised by the project. It does not create Rust privacy. A
language-reachable safe hidden item must remain sound for direct safe use and
may not hide a safety precondition. The project may separately exclude its
behavior or continued existence from SemVer promises.

## Distinguish Selected Dependencies From Caller Code

A deliberately selected dependency is code whose use and version the project
author intentionally chose. A function argument, callback, generic parameter,
trait object, plugin, implementation of a safe trait, or downstream macro input
is caller-controlled even when its type originates in a selected dependency.

Apply the selected-safe-dependency exception only to the deliberately chosen
implementation and documented API behavior, never to behavior chosen by the
caller. Determine whether reexports, dependency-defined traits, feature
unification, or plugins move a surface across that boundary.

For exact identity, contract channels, safe versus unsafe dependency trust, and
update triggers, apply
[Record dependency contracts](tcb-and-evidence.md#record-dependency-contracts).

## Prove Documented Behavior

Soundness is the minimum universal property. The mandatory postcondition scope
includes every documented postcondition of an unsafe API in scope and every
guarantee consumed by an in-scope soundness proof. Prove broader safe-API
behavior only when the user or audit explicitly places it in scope.

At minimum, an unsafe API implementation is responsible for both:

1. avoiding undefined behavior for every valid use; and
2. establishing every documented postcondition when its safety preconditions
   and other documented conditions are met.

Do not label a postcondition failure “sound” and stop. Report it separately as
`CONTRACT-BROKEN`, while also determining whether downstream unsafe code can
turn the broken guarantee into unsoundness.

Do not invent a universal standard for undocumented robustness. State the exact
behavioral claim being reviewed: panic freedom, determinism, resource bounds,
constant time, atomicity, rollback, leak freedom, progress, or another property.
Record its authority and scope separately from Rust soundness.

## Evolve Contracts Deliberately

Treat safety documentation and documented postconditions as compatibility
contracts, not comments that can be edited independently of code.

Analyze every change by provider and consumer:

- Strengthening a caller precondition invalidates previously valid calls.
- Weakening a caller precondition admits more calls and increases the
  implementation's proof burden.
- Weakening a provider postcondition invalidates existing caller reasoning.
- Strengthening a provider postcondition increases what callers may rely upon.
- Strengthening an unsafe trait implementer's obligation can invalidate existing
  impls.
- Strengthening guarantees required from trait implementations can likewise
  invalidate existing impls even when it benefits trait consumers.
- Weakening guarantees supplied through a trait can invalidate generic
  consumers.

Under a conventional SemVer contract, invalidating existing valid callers,
implementers, or documented reasoning is normally breaking even when Rust type
signatures do not change. Determine and record the actual project's
compatibility policy rather than treating SemVer folklore as an axiom.

An exact pin freezes identity but does not authorize an undocumented semantic
claim. A fork, out-of-band agreement, or consumer-specific promise may supply an
additional contract for its exact recorded scope; otherwise audit or explicitly
admit the implementation proposition. Update the TCB and repeat affected proofs
before changing any identity, contract, or agreement.

When the supported Rust range changes, apply
[Qualify applicability](proof-obligations.md#qualify-applicability), update any
compatibility premises in the TCB, and re-audit every proof whose documentation,
edition, target, feature, configuration, or implementation claim may differ.

For every contract change, search callers, implementers, safety comments, TCB
entries, generated output, and downstream-facing documentation for proofs that
consume the changed proposition.

Changing safety prose does not retroactively narrow valid uses of an already
published version. If that version's implementation failed its published
contract, it had a soundness or contract defect. Treat the correction as
remediation requiring compatibility analysis, affected-version disclosure, and
review of downstream proofs—not as proof that the old implementation was sound.

When redesign is authorized, apply
[Designing Unsafe Abstractions for Provability](abstraction-design.md) without
letting the proposed contract alter the verdict for the current artifact.
