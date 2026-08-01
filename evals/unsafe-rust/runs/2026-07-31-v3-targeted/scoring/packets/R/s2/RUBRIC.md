# Mode R Frozen Blind-Scoring Rubric

> **Evaluator-only material. Never expose this file to a report agent.**

## R — abstraction redesign

### Exact result

Within the exact target/profile scope declared in `REQUEST.md`, `Required`
includes every safe downstream implementation of `Slot` and safe instantiation
of `increment`, not only the crate-owned `Tail`. A safe
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
- **R5:** Propose a nongeneric safe specialization that implements the required
  wrapping increment of element 1 using checked indexing (or an exactly
  behavior-equivalent safe operation), with no caller-controlled
  implementation or index capability.
- **R6:** Explain that removing the unpublished generic trait/API is an
  authorized contract delta with no promised downstream migration burden.
- **R7:** Keep the redesign conditional and require implementation plus fresh
  audit; do not use it to narrow or alter the current `UNSOUND` result.

Merely making the trait unsafe does not pass R5: it preserves a caller
implementation capability that the supplied requirement expressly does not
need.

### Hard errors

Hard error if the report:

- trusts `Tail` as the only safe implementation;
- treats safe trait prose as a caller obligation;
- calls the current API sound or merely `UNPROVED` after closing the witness;
- certifies an unimplemented redesign; or
- lets design intent narrow the current contract.

### Authority

- Rust 1.82.0 slice `get_unchecked_mut`:
  `https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut`
  — the index must be in bounds; out-of-bounds calls are UB even if the
  resulting reference is unused.
- Rust 1.82.0 `u32::wrapping_add`:
  `https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add`
  — wrapping modular addition supplies the requested update semantics.
