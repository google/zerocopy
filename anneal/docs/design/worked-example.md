<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Worked example: an unsafe-backed byte buffer

This schematic example connects the concepts in the
[verification model](verification-model.md),
[verification subject and result identity](verification-artifact.md), and
[trust model](trust-model.md). It is intended to help a reader reason from the
project's requirements to a concrete proof shape.

The example is deliberately syntax-neutral. Names such as `BufferInvariant`,
`owns`, and `AbstractSequence` are explanatory notation, not proposed Anneal
annotations or Lean APIs. Likewise, the division into the outcomes and
property names below is illustrative; the final
[property and outcome taxonomy](open-questions/property-kinds-and-outcomes.md)
remains open.

## What is settled and what is illustrative

The following facts are **settled requirements**:

- soundness is foundational, and primitive safety obligations cannot be
  weakened by a user contract
  ([ANNEAL-REQ-005](settled-requirements.md#anneal-req-005-soundness-is-foundational)
  and
  [ANNEAL-REQ-006](settled-requirements.md#anneal-req-006-soundness-obligations-are-adequate));
- resource semantics must not become freely duplicable propositions
  ([ANNEAL-REQ-008](settled-requirements.md#anneal-req-008-resource-semantics-are-preserved));
- local caller, callee, and contract obligations must compose globally
  ([ANNEAL-REQ-009](settled-requirements.md#anneal-req-009-local-contract-obligations)
  and
  [ANNEAL-REQ-010](settled-requirements.md#anneal-req-010-local-results-compose-globally));
- a safe API cannot make Rust soundness depend on an unchecked obligation of
  its safe caller;
- type invariants may carry soundness and other property kinds
  ([ANNEAL-REQ-014](settled-requirements.md));
- panic and unwind paths relevant to soundness must be modeled
  ([ANNEAL-REQ-011](settled-requirements.md#anneal-req-011-long-running-and-exceptional-behavior));
- initial claims concern one fixed compilation artifact
  ([ANNEAL-REQ-017](settled-requirements.md#anneal-req-017-initial-claims-are-artifact-scoped));
- every result must expose its trusted and incomplete dependencies
  ([ANNEAL-REQ-021](settled-requirements.md#anneal-req-021-results-carry-an-audit-ledger)).

Everything specific to `ByteBuffer` is **illustrative**: the Rust API, the
primitive leaves, the abstract predicates, the proof decomposition, the
outcome descriptions, and the ledger presentation. None of them settles an
open design question.

## The example abstraction

Imagine a crate with this safe interface:

```rust
pub struct ByteBuffer { /* private raw-pointer representation */ }

impl ByteBuffer {
    pub fn replace(&mut self, index: usize, value: u8) -> u8;
}
```

Internally, `ByteBuffer` owns a heap allocation and records a raw pointer,
length, and capacity. A schematic implementation of `replace` is:

1. if `index >= len`, panic before touching the raw allocation;
2. otherwise call an unsafe primitive that replaces the byte at
   `ptr + index` and returns the previous byte; and
3. return the previous byte.

This resembles an implementation using `ptr::replace`, but the example does
not assert that `ptr::replace` should be Anneal's actual semantic leaf.

## The trusted primitive leaf

Suppose the Anneal standard library currently treats a primitive operation
called `replace_byte` as a trusted leaf. Its safety guard requires that:

- the pointer identifies a live allocation with suitable provenance;
- the selected address is in bounds and properly aligned;
- the selected byte is initialized; and
- the caller holds exclusive authority to write that byte.

The leaf's illustrative resource transition is:

```text
owns(allocation, bytes)  *  index < length(bytes)
    -- replace_byte(index, value) -->
owns(allocation, bytes[index := value])  *  old = bytes[index]
```

Here `*` is only mnemonic notation for resource composition. Crucially,
`owns(allocation, bytes)` is consumed and replaced by the operation. It is not
an ordinary hypothesis that a proof may duplicate and use for two writes. The
exact resource logic or monadic machinery needed to enforce this discipline is
an [open design question](open-questions/memory-resources-and-effects.md).

The primitive specification is trusted only at this boundary. Anneal must
still generate and check the guard at each call, and the ledger must identify
the specification as trusted. A future lower-level memory model could prove
the same leaf contract and remove that trust without changing `ByteBuffer`'s
public contract.

## The type invariant

For an abstract byte sequence `xs`, imagine an internal invariant with two
components:

```text
BufferInvariant(buffer, xs) :=
    there is one live allocation described by buffer.ptr/len/capacity
    * buffer has the exclusive owns(allocation, bytes) capability
    * buffer.len = length(xs)
    * the initialized prefix of bytes equals xs
```

The ownership component is soundness-relevant and resource-bearing. The
sequence relation supports an illustrative user-defined property,
`AbstractSequence`. A final design might represent those components together
or separately; this example does not decide that question.

Holding a mutable reference to a valid `ByteBuffer` allows its implementation
to open the invariant according to controlled rules. It does not give arbitrary
proof code two copies of `owns`. Before control leaves the method normally or
by unwinding through relevant cleanup, the invariant must be available in the
state required at that boundary.

Constructors must establish the invariant. Mutating methods must transform and
restore it. Destruction must consume the allocation capability exactly once.
Checking only `replace` while leaving construction, other field mutation, or
destruction unguarded would not establish the abstraction's soundness.

## Contracts at the safe boundary

The safe method has **no caller obligation whose violation permits undefined
behavior**. Every type-correct safe caller may pass any `usize`. In particular,
`index < len` is not a Rust safety precondition of `replace`.

The API can nevertheless have ordinary outcome and functional contracts. One
illustrative contract says:

- if `index` is out of bounds, the method panics without changing the abstract
  sequence;
- if the method returns normally, the return value is the old byte at
  `index`, and the new abstract sequence differs only by storing `value` at
  that index; and
- throughout either behavior, the method remains sound.

A caller seeking a no-panic result could prove the ordinary condition
`index < len`. Failure to prove that condition means the no-panic claim is
unavailable; it must not turn the safe call into undefined behavior. Whether
Anneal presents no-panic as a built-in policy, a property kind, or some other
construct remains open.

## Local proof obligations

For this example, a single symbolic execution could produce the following
obligations. That shared execution is illustrative rather than a commitment to
the final proof architecture.

### Entry

- Obtain `BufferInvariant(buffer, xs)` under the rules for a mutable borrow.
- Retain exactly one allocation capability while the invariant is open.

### Out-of-bounds branch

- Show that no raw-memory primitive is invoked.
- Show that the buffer state still represents `xs`.
- Under the artifact's unwind strategy, show that cleanup observes all
  invariants and capabilities needed for soundness.
- Establish the contract's panic behavior. No normal-return postcondition is
  claimed on this branch.

### In-bounds branch

- Derive every `replace_byte` guard from the branch condition and the opened
  invariant; a user-written postcondition cannot substitute for a missing
  provenance, initialization, or ownership fact.
- Apply the leaf's resource transition once.
- Re-establish `BufferInvariant(buffer, xs[index := value])` with the returned
  allocation capability.
- Establish that the returned byte equals `xs[index]`.

### Exit

- Restore the invariant before returning control to safe code.
- Record dependencies between the user-defined `AbstractSequence` result and
  the foundational soundness proof.

Whether these facts are enforced through propositional arguments in translated
Lean definitions, sidecar WP theorems, or another complete mechanism remains
[unresolved](open-questions/source-model-adequacy.md). The requirement is that
Anneal cannot omit the primitive guard or a relevant control-flow branch.

## Panic and unwind

Because the bounds check occurs before the invariant is opened for mutation,
the panic branch has an unchanged buffer. With an unwind panic strategy, the
model must nevertheless follow cleanup and destruction far enough to prove
that resources remain valid and are consumed correctly. A panic is a source
behavior, not a verifier failure.

Thus this method may satisfy soundness for every index while failing a blanket
no-panic claim. If a particular artifact uses `panic=abort`, the artifact and
claim differ; a proof for the unwind build is not automatically a proof for the
abort build. The example says nothing about whether outcome distinctions
become first-class axes in the final interface.

Long-running behavior does not arise in this method. A server loop would use
the same general compositional idea but prove invariant preservation over each
finite execution prefix rather than require normal termination.

## Global composition

Assume that the artifact also proves:

- every constructor establishes `BufferInvariant`;
- every other safe operation preserves it for all type-correct uses;
- destruction consumes its allocation exactly once;
- every call to a trusted memory or allocation leaf establishes that leaf's
  guard; and
- no relevant item or control-flow edge is skipped.

The local results then compose. Safe clients can use `ByteBuffer` without
examining its raw-pointer implementation or proving `index < len` for
soundness. The artifact is sound relative to the recorded primitive
specifications, translation adequacy, toolchain, and environmental assumptions.
If `AbstractSequence` is selected, clients may also use the proved sequence
contract without reopening the representation.

This composition does not prove that a trusted leaf specification matches
Rust, that a user chose a useful abstract sequence contract, or that an
unchecked artifact variant has the same behavior. Those are different trust,
specification-adequacy, and artifact-identity questions.

## A concrete compilation-subject record

The following fictional values demonstrate the scope of one result:

| Field | Illustrative value |
| --- | --- |
| Package and source | `byte-buffer 0.1.0` at revision `abc123` |
| Target | `x86_64-unknown-linux-gnu` |
| Cargo features | `checked-replace` |
| Relevant `cfg` | the compiler-resolved set for this invocation |
| Dependency graph | the exact locked dependency and standard-library revisions |
| Panic strategy | `unwind` |
| Generated Rust | expanded proc-macro and build-generated Rust ingested by Charon |
| Environment | relevant build inputs and environment recorded by the compilation-subject identity |

This is one claim, not a claim about all feature combinations, targets, panic
strategies, dependency resolutions, or downstream crate uses. The exact
compilation-subject and result schemas are still being designed; see
[verification subject and result identity](verification-artifact.md).

## An illustrative audit-ledger entry

The same result could report the following information. The grouping and
format are illustrative; the obligation to expose the information is settled.

| Ledger category | Example contents |
| --- | --- |
| Proved obligations | `ByteBuffer` constructors, `replace`, other relevant methods, and destruction preserve the selected soundness invariant; `replace` establishes `AbstractSequence` on normal return |
| Trusted leaves | allocation, deallocation, and `replace_byte`, including specification owners and affected property kinds |
| User or external axioms | none in this small crate, or separately listed if its allocator crosses an external boundary |
| Incomplete proofs | none; otherwise listed distinctly from axioms |
| Prose justifications | none; otherwise listed with source location and the conditional claim they permit |
| Unsupported or skipped coverage | none for this claim; any gap would identify the claim it prevents |
| Property dependencies | `AbstractSequence` depends on the soundness obligations used to justify its source model |
| Compilation subject | revision, target, features, resolved `cfg`, dependencies, panic strategy, generated Rust, and relevant environment |
| Toolchain identity | exact Anneal, Charon, Aeneas, rustc, LLVM, Lean, and proof-library revisions and options |
| Execution substrate | recorded assumptions or identities for the host verifier and target hardware, ABI, operating system, and allocator |

An incremental run in which `replace` has only a prose safety comment would
place that fact under prose justifications, not under proved obligations or
trusted external semantics. The command's final status would depend on the
eventual success-mode design, but the gap could not disappear from the ledger.

## What the example does not decide

This example does not choose:

- Rust annotation, contract, or proof syntax;
- a final taxonomy of properties, policies, outcomes, or effects;
- the encoding of type invariants or exclusive capabilities;
- proof arguments versus sidecar theorems;
- the precise Rust, Charon, Aeneas, and Anneal semantic boundary;
- whether `replace_byte` is actually a primitive leaf;
- how Anneal maps its property system onto Rust's `unsafe` machinery; or
- the exact compilation-subject, verification-result, ledger, command-mode, or
  diagnostic schemas.

Those choices must be resolved through the applicable
[open-question documents](open-questions/README.md), not inferred from this
teaching example.
