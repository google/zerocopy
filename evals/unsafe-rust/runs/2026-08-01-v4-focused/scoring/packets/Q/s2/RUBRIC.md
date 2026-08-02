# Mode Q Frozen Blind-Scoring Rubric

> **Evaluator-only material. Never expose this file to a report agent.**

> Evaluator-only material. Never expose this file to a report agent.

Let `C_Q` be Rust 1.80.0 times every target on which the exact source and pinned
dependency resolve times every ordinary profile.

- `Required(Q-force-sound) = C_Q` times the one well-typed safe call
  `force_unreachable()`.
- `Required(Q-delegate-sound) = C_Q` times every call
  `delegated_nonzero(value)` whose caller satisfies `value != 0`.

## Atoms

- **Q1 — Domain and claim separation:** State both valid-use domains and audit
  the two APIs independently. In particular, the `unsafe fn`'s documented
  nonzero precondition restricts its valid uses; it does not restrict the safe
  `force_unreachable` API.
  - `scope_basis`: `REQUEST.md` explicitly asks for two separate claims and
    supplies their common compilation scope; each API's signature/contract
    determines its valid-use domain.
  - `dependencies`: none.
- **Q2 — Complete UB certificate:** For `force_unreachable`, give all four
  links explicitly or by an equivalently exact chain: (1) the safe call is
  well-typed and valid; (2) its only body path reaches the executed
  `unreachable_unchecked` call; (3) that call requires its site not to be
  reached and that proposition is false; and (4) applicable Rust 1.80.0 std
  documentation says reaching it is UB.
  - `scope_basis`: necessary certificate for the requested soundness verdict
    on the safe API.
  - `dependencies`: Q1.
- **Q3 — Existential closure:** Report `Q-force-sound` **UNSOUND**. The complete
  in-scope witness refutes universal soundness; do not weaken it to `UNPROVED`
  merely because no universal positive proof was built.
  - `scope_basis`: `REQUEST.md` asks for the strongest justified verdict.
  - `dependencies`: Q2.
- **Q4 — Exact missing premise:** For `delegated_nonzero`, recognize that a
  valid caller supplies the dependency API's nonzero caller precondition, but
  the selected unsafe dependency body is absent and no accepted `UNSAFE-DEP`
  entry establishes that it honors its contract. The pin and caller-facing
  docs establish the logical coordinate and propagated obligation, not
  authenticated implementation identity or correctness. The smallest missing
  proposition is that every valid nonzero call to the selected
  `peer-unsafe-dep` 3.4.5 implementation is UB-free over this domain.
  - `scope_basis`: the supplied evidence packet and TCB policy are expressly
    part of the requested dependency claim review.
  - `dependencies`: Q1.
- **Q5 — No fabricated witness or silent trust:** Report
  `Q-delegate-sound` **UNPROVED**, not `PROVED` or `UNSOUND`. Its required cases
  lack the dependency-soundness premise, while the unavailable body supplies no
  proved UB execution. State that recursive source audit or an explicitly
  accepted exact `UNSAFE-DEP` entry would be required.
  - `scope_basis`: `REQUEST.md` asks for the strongest packet-supported verdict
    and smallest missing proposition.
  - `dependencies`: Q4.

## Hard errors

- **QH1:** Call `force_unreachable` sound or only `UNPROVED` after establishing
  all four Q2 links.
- **QH2:** Issue `UNSOUND` for it without a valid call, reachability, false exact
  safety proposition, and authoritative UB consequence.
- **QH3:** Silently trust the unavailable unsafe dependency, treat the pin as
  implementation proof, or report `delegated_nonzero` `PROVED`.
- **QH4:** Fabricate dependency body behavior or a UB execution and report
  `delegated_nonzero` `UNSOUND`.
- **QH5:** Treat violation of the dependency's documented caller precondition
  as itself an executed UB event.

## Checked authority

- `https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety`
  — reaching `unreachable_unchecked` is UB; applicable to Rust 1.80.0 without a
  target/profile qualification relevant here.

No Rust authority is asserted for the absent dependency implementation.
