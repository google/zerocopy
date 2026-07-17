<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Trust and incremental adoption

**Status:** Open design discussion.

Anneal must be useful before an entire codebase has been modeled, while making
it impossible to confuse a partially trusted result with an end-to-end proof.
It must also support genuinely external semantics that may remain axiomatic for
the foreseeable future. V2 therefore needs first-class accounting for trust,
incompleteness, and adoption state.

## Settled constraints

- V2 ultimately reduces the trusted computing base to a small, explicit set of
  trusted leaves rather than claiming to prove every primitive immediately.
- Near-term trusted leaves are expected to include unsafe standard-library
  operations, compiler intrinsics, raw pointer dereferences, FFI, and inline or
  out-of-line assembly where no transparent model is selected.
- The architecture must allow a trusted leaf to be replaced later by a formal
  model or proof. Assembly ISA models are one possible future example.
- Anneal's own standard library will likely use supported axiom syntax to state
  the behavior and safety preconditions of primitives and standard APIs.
- User-authored axioms are likely necessary for FFI for a long time, perhaps
  permanently for some environments. It remains open whether library authors
  or consumers normally publish them.
- In a fully adopted codebase, axioms should be reserved for genuinely external
  semantics or explicitly designated foundational primitive leaves rather than
  used merely to avoid proofs.
- Incremental adoption must allow some selected obligations to be justified by
  prose safety comments. These gaps must be explicit in the result.
- Axioms and not-yet-proven specifications must appear in a TCB audit log or
  equivalent trust ledger; they must not disappear behind a successful exit
  code.
- The ledger must cover more than source axioms. It must identify relevant
  versions or assumptions for Anneal, Aeneas, Charon, rustc, LLVM and other
  toolchain dependencies, and both host hardware running verification and
  target hardware running the generated binary.
- For non-axiomatic soundness specifications, Anneal must guarantee
  specification adequacy rather than delegating it entirely to human review.
- For a user-authored axiom defining a non-soundness property, the user supplies
  the intended ground truth. Anneal is responsible for enforcing and reporting
  the axiom, not for deciding whether it captures the user's real-world intent.

## Distinct forms of trust and incompleteness

V2 should not assume that all missing proofs mean the same thing. At minimum,
the design must evaluate distinctions among:

- an axiom representing genuinely external semantics;
- an Anneal-maintained primitive semantic assumption;
- a specification whose proof is intended but not complete;
- a call site temporarily justified by a prose `// SAFETY:` explanation;
- source or generated code intentionally outside the adoption scope;
- an opaque or unsupported construct;
- an admitted Lean theorem or equivalent escape hatch;
- a compiler, translator, kernel, runtime, or hardware assumption; and
- a model/tool failure that prevents any defensible claim.

These may share implementation machinery, but users need to know why each item
is trusted, who owns it, what it affects, and how it can be retired.

## Questions to resolve

### What does command success mean?

Candidate policies include:

- `cargo anneal verify` fails on every incomplete proof but permits explicitly
  approved axioms with a ledger;
- a separate incremental profile succeeds with a clearly conditional status;
- one command returns structured assurance grades and uses configurable exit
  policy; or
- distinct commands separate end-to-end verification from partial checking.

The design must avoid a state in which users or CI interpret “success” as a
stronger claim than the artifact supports. Open details include:

- whether unrequested property kinds appear as gaps;
- whether a deliberately excluded dependency is an error or audited
  assumption;
- how policy changes affect reproducibility;
- whether CI can impose a budget or allowlist for trust gaps; and
- what downstream crates may rely on from a partially verified dependency.

### How are incomplete proofs represented?

An explicit “specification present, proof incomplete” status may be preferable
to encoding incremental work as an axiom. It is analogous in purpose to Lean's
`sorry`, but V2 need not expose that mechanism directly.

Questions include:

- Is incompleteness attached to a theorem, obligation, source region, property
  kind, or artifact?
- Does it preserve the intended specification for callers while marking its
  proof as trusted?
- Can a project prohibit new gaps while grandfathering existing ones?
- Does each gap have an owner, rationale, expiration, or issue link?
- How are transitive gaps summarized without losing their origin?
- Can a proof later replace the gap without changing the public verification
  interface?

### How do prose justifications work?

Prose support is required, but its semantics are open. It could be represented
as a specialized admitted obligation associated with a Rust unsafe boundary,
or as a separate trust category with Rust-oriented diagnostics.

We need to decide:

- which comments Anneal recognizes and how they bind to exact compiler-resolved
  operations;
- whether prose is allowed only for soundness or for arbitrary property kinds;
- whether the text is included verbatim or hashed in the ledger;
- whether ordinary Rust linting conventions are reused;
- what happens when code moves and a comment no longer binds unambiguously; and
- how the tool guides conversion from prose to a machine proof.

This intersects with [Rust safety integration](rust-safety-integration.md).

### Who authors and distributes external specifications?

For FFI and platform APIs, the specification might be authored by:

- each Rust consumer;
- the C, C++, assembly, or platform library author;
- an Anneal standard-library or ecosystem package; or
- a third-party verification authority.

V2 needs identities, versioning, target constraints, and a way to distinguish a
widely reviewed specification from a local assertion without turning social
trust into a misleading proof claim. Specifications may eventually be backed
by proofs in another system or by a formal ISA model.

### What exactly is in the ledger?

Candidate fields include:

- the concrete Cargo artifact: target, features, `cfg`s, panic strategy,
  dependency graph, environment inputs, and generated code identity;
- selected property kinds and their transitive dependencies;
- proved, axiomatic, incomplete, prose-justified, skipped, opaque, unsupported,
  and failed obligations;
- trusted leaves and their specification versions;
- admitted Lean declarations or unchecked escape hatches;
- coverage gaps and reachability assumptions;
- Anneal, Aeneas, Charon, Lean, rustc, LLVM, linker, and other tool versions;
- host OS and hardware assumptions that affect the verification run;
- target ABI, platform, and hardware assumptions that affect execution;
- proof and source hashes, timestamps, and reproducibility information; and
- the provenance, owner, and rationale for each trust entry.

The exact schema, stability guarantee, serialization, signing, and diff format
are open. The ledger should be machine-readable and should also support a human
audit view.

## Evaluation criteria

An acceptable design must be fail-closed about unsupported semantics, preserve
the difference between proof and trust, support useful incremental adoption,
and make transitive assumptions visible. It should reward shrinking the TCB,
allow external models to replace axioms, and produce stable artifacts suitable
for code review and CI policy.

Useful experiments include a crate with one prose-justified call, a dependency
with an incomplete functional proof, an FFI binding with target-specific
axioms, and the same code verified under two compiler or hardware assumptions.
The source coverage needed to populate the ledger is discussed in
[source/model adequacy](source-model-adequacy.md).
