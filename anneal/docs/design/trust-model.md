<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Trust model

Anneal does not eliminate trust by moving a program into Lean. It aims to make
the trusted computing base explicit, reviewable, and capable of shrinking as
stronger models become available. The near-term end-to-end TCB is broad; it
must not be described as small merely because the program-facing semantic leaf
boundary is small.

This document states required trust boundaries. The exact audit-ledger schema
and command modes remain open; see
[trust and incremental adoption](open-questions/trust-and-incremental-adoption.md).

## What trust means

An Anneal result is conditional on every component and assumption required to
turn checked proofs into a fact about execution on target hardware. Some
components are trusted because formally verifying them is outside Anneal's
present scope. Others are semantic assumptions that define which executions
the claim covers. Both must be visible.

The TCB is broader than the list of `axiom` declarations in generated Lean. It
may include:

- Anneal and the adequacy of its generated obligations;
- Charon's extraction and serialization of compiler-resolved Rust;
- Aeneas's translation and Lean semantics;
- Lean's kernel and the code that prepares proofs for checking;
- rustc and LLVM behavior relevant to the source/binary claim;
- the interpretation of Rust's normative semantics and target ABI;
- specifications of trusted primitive operations;
- FFI libraries, assembly, operating-system or firmware behavior; and
- host hardware executing the verifier and target hardware executing the
  binary.

Listing a component does not assert that it can never be verified. It records
the current end-to-end dependency honestly.

## Two trust boundaries

Do not conflate:

- the **end-to-end TCB**, which includes every implementation and assumption
  needed to connect a checked Lean theorem to execution on target hardware;
  and
- the **trusted semantic leaf boundary**, the program operations whose behavior
  is specified axiomatically rather than proved from a deeper model.

V2 aims initially for a small, explicit, replaceable set of semantic leaves.
That does not make the current compiler, translation, proof-checking, platform,
and hardware TCB small. Work can shrink either boundary, and the audit ledger
must make clear which kind of trust a change actually removed.

## Trusted leaves

V2 should reduce opaque program semantics to a small, explicit set of trusted
leaves. Expected near-term categories include:

- raw-pointer dereference and related primitive memory operations;
- unsafe standard-library functions and compiler intrinsics;
- inline or out-of-line assembly;
- foreign-function interfaces; and
- platform operations whose semantics are not yet modeled.

Anneal's standard library will likely express the safety preconditions and
behavior of these operations using the same axiom mechanism exposed for
external semantics. The Anneal authors are responsible for ensuring that the
soundness preconditions of Anneal-provided leaves are adequate for the Rust
semantics claimed.

A leaf is a boundary, not a permanent exemption. For example, a formal Lean
model of an instruction set could make selected assembly transparent; a
verified foreign library could replace an FFI axiom. The architecture must
permit such refinement without changing every caller contract.

## Soundness axioms and user correctness axioms

An axiomatic soundness specification claims correspondence with Rust or an
external operational semantics. It can be incorrect. Anneal must identify who
owns that specification and expose it for audit.

An axiom defining a user property has a different role. If a user declares
what "implements protocol X" means at an external boundary, there may be no
independent meaning available to Anneal. Anneal is responsible for propagating
and enforcing the declared property, not for guessing whether it captures the
user's intent.

FFI sits across both cases. A specification may need to describe memory-safety
preconditions fixed by Rust and functional behavior chosen by a library API.
FFI axioms will likely be necessary for the foreseeable future. It remains open
whether they are normally authored and distributed by a foreign library's
maintainer, written by each Rust consumer, or shared through a separately
reviewed specification package.

## Incomplete adoption is not axiomatic truth

Anneal must support codebases that adopt verification gradually. At least two
forms of incompleteness are expected:

- a declared formal obligation whose proof is not finished; and
- a prose safety justification accepted in place of a formal proof.

Neither should be represented to users as a theorem proved by Anneal. They may
permit a conditional or incremental check, but must remain distinguishable
from both completed proofs and genuinely external axioms.

V1 used `unsafe(axiom)` to hide a body and trust its specification. That can
verify callers relative to the leaf; it does not prove the leaf. V2 must make
that distinction explicit in the result.

## Audit ledger

Every result must make it possible to audit what remains trusted, assumed, or
incomplete. The ledger must include at least:

### Proof and coverage

- the exact claim, selected properties, and guarantees being reported;
- each trusted leaf and axiom, with origin and affected property kinds;
- each incomplete or admitted proof;
- each prose justification and its source location;
- opaque, skipped, unsupported, or unmodeled items;
- coverage gaps and the claims they prevent; and
- dependencies among properties and assumptions.

### Compilation subject

- source revision and compilation-subject identity;
- target triple, features, `cfg` values, dependencies, and panic strategy;
- proc-macro and build-generated Rust included in the artifact;
- relevant environment variables and build inputs; and
- ABI, operating-system, firmware, or external-service assumptions.

### Toolchain identity

- Anneal, Aeneas, and Charon versions or revisions;
- Rust compiler, standard library, and LLVM versions;
- Lean, Mathlib, and other proof-library versions;
- build and translation options; and
- any downstream patches that alter semantics.

These toolchain fields identify the verification evidence and trust boundary;
they do not necessarily identify a different Rust compilation subject. See
[verification subject and result identity](verification-artifact.md).

### Execution substrate

- the host hardware or trusted execution environment on which verification ran,
  to the degree needed to reproduce or assess the result; and
- the target hardware model or concrete implementation assumed for generated
  code.

If a result stops at a source/model claim and does not claim execution of a
binary, the ledger should state that target-hardware execution is outside the
claim rather than imply that it was verified. Host hardware executing the
proof checker may still remain in the practical TCB.

The useful level of hardware identity may differ between reproducibility,
fault-adversarial assurance, and ordinary builds. The schema is open, but the
ledger may not silently pretend that software proves itself independently of
the machine executing the proof checker or program.

## Trust and command success

An approved axiom may be compatible with a successful result when the output
states that the claim is relative to that axiom. An incomplete proof or prose
justification may instead belong in a separate incremental mode. Whether
`cargo anneal verify` categorically rejects all incompleteness or whether
profiles provide clearly named conditional checks is unresolved.

Whatever interface is chosen:

- a successful exit must have a documented meaning;
- omitted proof coverage must not disappear from reports;
- model/tool failures must not be interpreted as source behavior; and
- users must be able to compare ledgers as trust is reduced over time.

“Fail closed” means that Anneal must not silently emit a claim stronger than
its evidence supports. It does not predetermine one exit-code policy: an
explicitly named incremental mode may succeed with a weaker, conditional claim
if every condition and gap is exposed.

## Shrinking the TCB

Designs should separate stable client-facing contracts from the current depth
of a model. That makes it possible to replace:

- an unsafe primitive axiom with a proved Rust operational model;
- an assembly axiom with an ISA-level proof;
- an FFI axiom with a verified foreign implementation;
- a compiler assumption with a translation-validation or verified-compilation
  result; or
- an informal hardware assumption with a formal hardware model.

Shrinking trust is valuable only if the new model connects to the same
end-to-end claim. Moving an assumption into an opaque helper, generated file,
or upstream tool without recording it does not reduce the TCB.
