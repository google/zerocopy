# Abstraction Design V1 Fixture Registry

> **Evaluator-only oracle.** Never place this file or sibling fixtures in an
> evaluated agent's accessible target directory.

All fixtures are source-only. No build, test, expansion, or target execution is
permitted.

## A — Immutable acceptance

- **A1:** Apply the literal `Piece` contract. `Tail` does not name or project a
  direct declared field called `tail`; the nominal contract is false.
- **A2:** Preserve a scoped current-artifact rejection/`UNPROVED` or
  contract-broken result without manufacturing a UB witness; the operational
  nested projection can be sound independently.
- **A3:** Treat names, comments, tests, and the one known consumer only as intent
  evidence, never as a replacement contract.
- **A4:** Respect the immutable accept/reject-only scope: no redesign,
  candidate, migration, or edit.

## R — Projection redesign

- **R1:** Preserve A's current literal result before and independently of any
  proposal.
- **R2:** Extract the exact required behavior: increment `Pair.0[1]` with
  wrapping arithmetic; internal-only API; Rust 1.70+; all targets/profiles; no
  allocation; no demonstrated generic reuse.
- **R3:** Identify nested projection as the operational capability and separate
  it from unused nominal direct-field metadata.
- **R4:** Prefer the safe specialized implementation because it eliminates the
  unsafe trait and is strictly simpler under the stated requirements. A
  narrower projection-only abstraction is acceptable only as a conditional
  future-reuse alternative.
- **R5:** Reject cosmetic rename/fabricated-field fixes and unnecessary caller
  obligations.
- **R6:** State contract/invariant/proof simplification, behavior and support
  preservation, compatibility (internal-only), and re-audit needs.
- **R7:** Give no unimplemented candidate a `PROVED` verdict; keep current,
  requirements, proposal, and post-change audit separate.

## T — Ticket construction

- **T1:** Current safe `ticket(0)` is `UNSOUND` without debug assertions and
  violates the mandatory always-panic behavior.
- **T2:** Prefer `NonZeroUsize::new(id).expect(...)` or an equivalent safe
  standard primitive with an unconditional zero check.
- **T3:** Preserve the safe signature, exact nonzero value, panic behavior, all
  profiles, and support domain.
- **T4:** Reject making the function unsafe, adding a hidden caller precondition,
  retaining `debug_assert!`, or using unchecked construction when the safe
  primitive matches.
- **T5:** Keep current finding, proposal proof plan, and fresh-audit requirement
  separate.

## P — Published contract

- **P1:** The current `Page` implementation satisfies all published `Block`
  clauses and `first` is sound for every valid unsafe implementation; do not
  invent a current defect.
- **P2:** Known repository consumers do not exhaust downstream consumers of the
  public unsafe trait.
- **P3:** Do not weaken alignment/readable-extent guarantees, seal the trait, or
  strengthen implementer obligations within the promised compatible 1.x line.
- **P4:** A private narrower helper may simplify known internal code but cannot
  erase the public trait/impl audit. A breaking split/seal belongs to an
  explicitly authorized 2.0 plan.
- **P5:** State provider/implementer/consumer contract directions, migration,
  proof consequences, and any human release decision.

## C — Configuration domain

- **C1:** `compact` plus disabled debug assertions is `UNSOUND` for surrogate
  inputs and breaks the documented panic postcondition.
- **C2:** The non-`compact` branch is a separate safe, correct region.
- **C3:** Redesign compact mode with an unconditional checked conversion which
  preserves its signature and panic behavior throughout Rust 1.70+.
- **C4:** Cover both feature values, both assertion states, every supported
  target/pointer width, and the MSRV without silently dropping/raising any.
- **C5:** Keep current regional verdicts, proposed proof, compatibility, and
  future exact-source audit separate.

## S — Sealed boundary

- **S1:** Current safe downstream `Bytes` implementations can return
  dangling/inconsistent raw parts, making safe `last` unsound.
- **S2:** `#[doc(hidden)]` is not sealing and behavioral prose on the safe method
  cannot establish the invariant.
- **S3:** Because external implementations are unnecessary and sealing is
  authorized, prefer a genuinely private leaf-module sealing/representation
  boundary and audit each controlled implementation. Merely `pub(crate)`
  invariant-bearing access is proof-surface debt under the stated discipline.
- **S4:** Making the trait unsafe is viable but exposes a larger implementer
  obligation and is dominated under these requirements; do not prefer it
  without another constraint.
- **S5:** Preserve `last`: empty built-ins return `None`, otherwise the final
  byte; specify local contracts, controlled producers/consumer, and re-audit.

## G — Greenfield

- **G1:** Give no current-artifact verdict; no implementation exists.
- **G2:** Preserve exact order: `None` for equal/out-of-range indices, otherwise
  return references corresponding to `(i, j)`.
- **G3:** Prefer a safe `split_at_mut` design, reversing tuple assembly when
  `j < i`; no unsafe trait, raw-pointer abstraction, or caller token is needed.
- **G4:** State the conditional proof plan, bounds/distinctness reasoning, and
  support/behavior scope.
- **G5:** Do not call the sketch `PROVED`; require audit of exact implemented
  source.

## H — Incomparable tradeoff

- **H1:** Do not condemn the current pointer loop without a failed proof; state
  its relevant one-past/end, dereference, progression, overflow, empty-slice,
  and wrapping-add obligations.
- **H2:** Identify `iter().copied().fold(0, u32::wrapping_add)` or equivalent as
  the safe behavior-preserving candidate; reject plain `sum()` as changing
  debug overflow behavior.
- **H3:** Do not claim the safe candidate meets the 2% benchmark without the
  designated measurement.
- **H4:** Present safe-candidate implementation/audit plus benchmark as the next
  action, retaining the proved raw loop conditionally if the binding benchmark
  rejects it.
- **H5:** Treat proof surface and measured performance as incomparable until
  evidence resolves the hard performance constraint; use no invented score.

## N — New snapshot

- **N1:** Treat supplied code as a new exact artifact; do not inherit the
  approved sketch or alter any prior verdict.
- **N2:** Find a fully safe witness retaining two mutable references from two
  `get_mut` calls; `get` followed by `get_mut` also permits shared/mutable
  overlap. Classify the implemented candidate `UNSOUND`.
- **N3:** Explain that returned `'a` is not tied to the receiver borrow; privacy,
  `PhantomData`, and the safe constructor do not discharge method aliasing.
- **N4:** Propose receiver-bound output lifetimes for both methods, not only
  `get_mut`, and withhold a verdict until that exact source is implemented and
  audited.
- **N5:** Report current new-snapshot finding, proposed fix, and post-fix audit
  as separate artifacts.

