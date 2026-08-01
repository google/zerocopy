# V4 Focused Oracle — R: Abstraction-Design Control

> Evaluator-only material. Never expose this file to a report agent.

## Exact result

Within the scope in `REQUEST.md`, valid safe use includes every downstream safe
implementation of `Slot`, not only `Tail`. An implementation returning 2 and a
safe call `increment::<Bad>(&mut [0, 0])` reaches
`get_unchecked_mut(2)` on a length-2 slice. Its in-bounds precondition is false,
and Rust 1.82.0 documents an out-of-bounds call as UB. The current safe API is
therefore `UNSOUND`.

The required behavior needs neither generic index metadata nor an unsafe
abstraction. The preferred design is a nongeneric safe function that updates
`pair[1]` with wrapping addition (or an exactly behavior-equivalent checked
specialization). It eliminates caller implementation/index capability and the
unsafe block. Making `Slot` unsafe, adding safe-trait prose, or preserving the
generic abstraction by default is less parsimonious because downstream generic
use is expressly not required. The proposal does not alter the current verdict
and requires implementation plus fresh audit.

## Atoms

- **R1:** Quantify over arbitrary safe `Slot` implementations and explicitly
  construct or describe one returning 2 together with its valid safe call.
  - `scope_basis`: public safe trait implementation and safe generic calls are
    valid-use surfaces of the exact current source.
  - `dependencies`: exact Rust 1.82.0 public-visibility, trait-implementation,
    ordinary-versus-unsafe-trait, and safe-versus-unsafe-function rules.
- **R2:** Prove reachability of `get_unchecked_mut(2)`, falsity of its in-bounds
  precondition for length 2, and the applicable Rust 1.82.0 UB consequence.
  - `scope_basis`: necessary certificate for the current-artifact soundness
    claim requested in `REQUEST.md`.
  - `dependencies`: R1.
- **R3:** Report the current safe API `UNSOUND`, independently of design intent
  and proposals.
  - `scope_basis`: `REQUEST.md` expressly requires the literal current-artifact
    verdict before redesign.
  - `dependencies`: R2.
- **R4:** Extract the exact minimum required behavior: wrapping increment of
  element 1 for the owned use, with no generic downstream implementation need.
  - `scope_basis`: this requirement is stated verbatim in `REQUEST.md`.
  - `dependencies`: none.
- **R5:** Propose a nongeneric safe specialization implementing R4 with checked
  indexing or an exactly equivalent safe operation, and no caller-controlled
  implementation or index capability.
  - `scope_basis`: `REQUEST.md` asks for the most parsimonious provable
    abstraction satisfying R4.
  - `dependencies`: R4.
- **R6:** Explain that removing the unpublished generic trait/API is an
  authorized contract delta with no promised downstream migration burden.
  - `scope_basis`: `REQUEST.md` expressly permits this contract and
    representation change.
  - `dependencies`: R4, R5.
- **R7:** Keep the redesign conditional and require implementation plus fresh
  audit; do not use it to narrow or alter R3.
  - `scope_basis`: `REQUEST.md` requires the current verdict and post-change
    audit independently.
  - `dependencies`: R3, R5.

Merely making the trait unsafe does not pass R5 because it preserves an
unneeded caller implementation capability.

## Hard errors

- **RH1:** Trust `Tail` as the only safe implementation.
- **RH2:** Treat safe-trait prose as a caller obligation.
- **RH3:** Call the current API sound or merely `UNPROVED` after closing R2.
- **RH4:** Certify an unimplemented redesign.
- **RH5:** Let design intent narrow the current contract.

## Checked authority

- Rust 1.82.0 Reference, public visibility:
  `https://doc.rust-lang.org/1.82.0/reference/visibility-and-privacy.html#visibility-and-privacy`
  — public items are accessible from outside their module, subject to the
  containing path; every item here is at the public crate root.
- Rust 1.82.0 Reference, trait implementations and coherence:
  `https://doc.rust-lang.org/1.82.0/reference/items/implementations.html#trait-implementations`
  — a trait implementation may be defined when the implementing type is local,
  so a downstream crate may define local `Bad` and implement `Slot` for it.
- Rust 1.82.0 Reference, unsafe traits:
  `https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits`
  — unsafe traits are explicitly declared with `unsafe`; the supplied `Slot`
  declaration is an ordinary safe trait and its implementation requires no
  unsafe act.
- Rust 1.82.0 Reference, unsafe functions:
  `https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-functions-unsafe-fn`
  — the caller-side unsafe obligation attaches to an `unsafe fn`; the supplied
  public `increment` is an ordinary safe function.
- Rust 1.82.0 slice `get_unchecked_mut`:
  `https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut`
  — the index must be in bounds; an out-of-bounds call is UB even if its result
  is unused.
- Rust 1.82.0 `u32::wrapping_add`:
  `https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add`
  — modular wrapping addition supplies the requested update semantics.
