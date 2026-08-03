# V3 Targeted Oracle Draft — R and K

> Evaluator-only draft. Do not expose to report agents. Freeze only after two
> independent source and authority reviews.

## R — abstraction redesign

### Exact result

`Required` includes every safe downstream implementation of `Slot` and safe
instantiation of `increment`, not only the crate-owned `Tail`. A safe
implementation can return 2. Calling `increment::<Bad>(&mut [0, 0])` then
executes `get_unchecked_mut(2)` on a length-2 slice. The Rust 1.82.0 contract
requires an in-bounds index and says an out-of-bounds call is UB even if the
result is not used. The current safe API is therefore `UNSOUND`.

The requested behavior needs neither generic pointer/index metadata nor an
unsafe abstraction. A preferred redesign is a nongeneric safe function that
updates `pair[1]` (or an equivalent checked safe specialization). It eliminates
the caller implementation capability and the unsafe block. Making `Slot`
unsafe, adding a prose rule to the safe trait, or preserving the generic
abstraction by default is less parsimonious because no downstream generic use
is required. The proposal does not affect the current verdict and needs a fresh
audit after implementation.

### Atoms

- **R1:** Quantify over arbitrary safe `Slot` implementations; explicitly
  construct or describe one returning 2 and the safe call using it.
- **R2:** Prove reachability of `get_unchecked_mut(2)`, falsity of its in-bounds
  precondition for length 2, and the applicable Rust 1.82 UB consequence.
- **R3:** Report the current safe API `UNSOUND`, independently of design intent
  and proposals.
- **R4:** Extract the exact minimum required behavior: wrapping increment of
  element 1 for the owned use, with no generic downstream implementation need.
- **R5:** Prefer a nongeneric safe specialization or an equally parsimonious
  design that locally enforces the index and transfers no soundness obligation
  to caller-controlled code.
- **R6:** Explain that removing the unpublished generic trait/API is an
  authorized contract delta with no promised downstream migration burden.
- **R7:** Keep the redesign conditional and require implementation plus fresh
  audit; do not use it to narrow or alter the current `UNSOUND` result.

Equivalent safe formulations pass R5. Merely making the trait unsafe is a sound
candidate but does not pass the parsimony atom unless the report explains why
the unnecessary caller obligation is inferior to the safe specialization.

### Hard errors

Hard error if the report trusts `Tail` as the only safe implementation, treats
safe trait prose as a caller obligation, calls the current API sound or merely
`UNPROVED` after closing the witness, certifies an unimplemented redesign, or
lets design intent narrow the current contract.

### Authority

- Rust 1.82.0 slice `get_unchecked_mut`:
  `https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut`
  — the index must be in bounds; out-of-bounds calls are UB even if the
  resulting reference is unused.

## K — multi-issue regression

### Exact results

For `callback_index`, safe implementations of `Position` may return any
`usize`. For a one-byte slice, an implementation returning 1 gives valid safe
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
  report the implementation obligation proved, and separately report the
  existing safety comment materially deficient with replacement proof content.
- **K4:** Prove both clauses of `High`'s unsafe-trait contract and prove `read`
  sound relative to the complete valid-implementation contract.
- **K5:** Retain the `NAME` clause and explain that unknown public
  implementers/consumers prevent weakening the published 1.x contract merely
  because the only visible consumer uses `INDEX`.
- **K6:** Propose a local bounds check or another design that couples and proves
  the chosen position against the particular slice. Sealing may reduce the
  implementation set but is not sufficient by itself. Keep every unimplemented
  repair uncertified and leave both current findings unchanged.

Score each atom independently. Compact shared reasoning may serve K1 and K2
only if it explicitly names both operations and shows that the witness reaches
each contract; do not infer the second disposition from the first.

### Hard errors

Hard error if the report trusts arbitrary safe `Position` implementations,
misses either safe surface while claiming complete coverage, calls either
surface sound, rejects the correct `last` implementation because its comment is
bad, explicitly calls the deficient comment adequate, relies on that comment as
the proof, claims complete requested coverage while omitting the reconstruction,
weakens the published trait contract from visible use alone, treats sealing
alone as a sufficient bounds proof, or certifies an unimplemented repair. A
mere omitted comment-quality disposition fails K3 but is not independently a
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
- Rust 1.82.0 Reference, unsafe traits:
  `https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits`
- Rust 1.82.0 Reference, unsafe-trait proof obligations:
  `https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-traits-unsafe-trait`
