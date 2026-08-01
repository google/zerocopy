# Mode K Frozen Blind-Scoring Rubric

> **Evaluator-only material. Never expose this file to a report agent.**

## K — multi-issue regression

### Exact results

Within the exact target/profile scope declared in `REQUEST.md`, safe
implementations of `callback_index::Position` may return any `usize`. For a
one-byte slice, an implementation returning 1 gives valid safe
calls to both `read` and `write`, each of which executes its respective
out-of-bounds unchecked operation. Both safe surfaces are independently
`UNSOUND`.

`local_proof::last` is sound. On the nonempty branch, `len > 0`, so
`index = len - 1` is defined and `index < len`; that discharges
`get_unchecked(index)`. The existing comment states none of this and does not
identify the callee obligation. The report must expose the reconstructed proof
and separately classify the implementation as proved and the proof artifact as
deficient.

For `published_lane`, the unsafe trait contract makes valid implementations
responsible for both `INDEX < 2` and the exact `NAME`/`INDEX` relation. The shown
`High` implementation satisfies both clauses. `read` consumes only the first
clause and is sound for every valid implementation. Unknown downstream
consumers mean the unused `NAME` clause cannot be weakened from the published
1.x contract merely because `read` does not consume it.

### Atoms

- **K1:** For `callback_index::read`, construct the arbitrary-safe-impl witness,
  prove the length-1/index-1 precondition failure and UB consequence, and report
  this safe surface `UNSOUND`.
- **K2:** Independently give the same complete disposition for
  `callback_index::write`; do not stop after K1.
- **K3:** For `local_proof::last`, reconstruct the nonempty -> `len > 0` ->
  `len - 1 < len` derivation, connect it to the exact unchecked-index contract,
  and report the implementation obligation proved.
- **K4:** Separately report the existing `local_proof::last` safety comment
  materially deficient and provide replacement proof content that identifies
  the unchecked-index obligation and the K3 derivation.
- **K5:** Prove that `High` satisfies both clauses of its unsafe-trait contract:
  `INDEX < 2` and the exact `NAME`/`INDEX` relation.
- **K6:** Prove `published_lane::read` sound for every valid implementation of
  the complete `Lane` contract by consuming its `INDEX < 2` clause.
- **K7:** Retain the `NAME` clause and explain that unknown public
  implementers/consumers prevent weakening the published 1.x contract merely
  because the only visible consumer uses `INDEX`.
- **K8:** Propose a repair that preserves callable read and write operations at
  positions chosen by safe callers and locally couples and checks each chosen
  position against the particular slice. Deleting or making the APIs
  uncallable, or merely sealing or eliminating the caller-implementable trait,
  does not meet that functional requirement.

Score each atom independently. Compact shared reasoning may serve K1 and K2
only if it explicitly names both operations and shows that the witness reaches
each contract; do not infer the second disposition from the first.

### Hard errors

Hard error if the report:

- trusts arbitrary safe `Position` implementations;
- misses either safe surface while claiming complete coverage;
- calls either safe surface sound;
- rejects the correct `last` implementation because its comment is bad;
- explicitly calls the deficient comment adequate;
- relies on that comment as the proof;
- claims complete requested coverage while omitting the reconstruction;
- weakens the published trait contract from visible use alone;
- treats sealing alone as satisfying the stated functional repair;
- claims a callable caller-position API is repaired without locally coupling
  the selected position to the particular slice; or
- certifies an unimplemented repair.

A mere omitted comment-quality disposition fails K4 but is not independently a
hard error.

### Authority

- Rust 1.82.0 slice `get_unchecked`:
  `https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked`
- Rust 1.82.0 slice `get_unchecked_mut`:
  `https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut`
- Rust 1.82.0 slice `len` and `is_empty`:
  `https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len`
  and
  `https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty`
- Rust 1.82.0 Reference, arithmetic binary operators and integer overflow:
  `https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators`
- Rust 1.82.0 Reference, unsigned integer value domains:
  `https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types`
- Rust 1.82.0 Reference, unsafe traits:
  `https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits`
- Rust 1.82.0 Reference, unsafe-trait proof obligations:
  `https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-traits-unsafe-trait`
