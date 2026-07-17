<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Worked example: an unsafe-backed byte buffer

This schematic example connects the concepts in the
[verification model](verification-model.md) and
[result and trust model](result-and-trust.md). It is a teaching example, not a
normative design: `ByteBuffer`, the primitive leaves, predicates, proof
decomposition, outcome names, and result presentation below are all
illustrative. Names such as `BufferInvariant`, `owns`, and
`AbstractSequence` are explanatory notation rather than proposed Anneal or Lean
syntax. Open choices remain governed by the
[open-question ledger](open-questions/README.md).

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

## An illustrative result record

One fictional result for this example might be summarized as follows. The
record is intentionally compact; it demonstrates how the subject, claim,
evidence, and residual dependencies fit together rather than proposing a
schema.

| Part | Illustrative contents |
| --- | --- |
| Compilation subject | `byte-buffer 0.1.0` at revision `abc123`; target `x86_64-unknown-linux-gnu`; feature `checked-replace`; compiler-resolved `cfg`; locked dependencies; `panic=unwind`; expanded generated Rust; relevant environment inputs |
| Claim | Soundness for the covered artifact, plus `AbstractSequence` for normal returns from `replace`; no claim over other targets, features, panic strategies, dependency resolutions, or downstream clients |
| Checked evidence | Constructors establish `BufferInvariant`; relevant methods preserve it; destruction consumes the allocation once; every covered memory-leaf call establishes its guard; `replace` proves its sequence contract |
| Residual dependencies | Trusted allocation, deallocation, and `replace_byte` specifications; no user axioms, incomplete proofs, prose justifications, or unsupported coverage in this fictional run |
| Provenance | Exact Anneal, Charon, Aeneas, rustc, LLVM, Lean, and proof-library identities and options, plus relevant host and target platform assumptions |

If an incremental run relied only on prose for the `replace_byte` call, that
fact would move into the residual dependencies rather than checked evidence.
The eventual command-status policy remains open, but the conditional
dependency could not disappear from the reported result. See the canonical
[result and trust model](result-and-trust.md).
