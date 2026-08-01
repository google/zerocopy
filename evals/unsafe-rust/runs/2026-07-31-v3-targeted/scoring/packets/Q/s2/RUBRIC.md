# Mode Q Frozen Blind-Scoring Rubric

> **Evaluator-only material. Never expose this file to a report agent.**

## Q — Existential refutation and missing unsafe dependency

Target: supplied Q snapshot.

Let `C_Q` be Rust 1.80.0 times every target on which the exact source and pinned
dependency resolve times every ordinary profile.

- `Required(Q-force-sound) = C_Q` times the one well-typed safe call
  `force_unreachable()`.
- `Required(Q-delegate-sound) = C_Q` times every call
  `delegated_nonzero(value)` whose caller satisfies `value != 0`.

### Expected results and atoms

- **Q1 — Domain and claim separation:** State both valid-use domains and audit
  the two APIs independently. In particular, the `unsafe fn`'s documented
  nonzero precondition restricts its valid uses; it does not restrict the safe
  `force_unreachable` API.
- **Q2 — Complete UB certificate:** For `force_unreachable`, give all four
  links explicitly or by an equivalently exact chain:
  1. `force_unreachable()` is a well-typed, valid safe call in `Required`;
  2. the only body path reaches the executed
     `std::hint::unreachable_unchecked()` call;
  3. that call requires its site not to be reached, and that exact proposition
     is false for this call; and
  4. Rust 1.80.0 std documentation says reaching the function is undefined
     behavior.
- **Q3 — Existential closure:** Report `Q-force-sound` as **UNSOUND**. The one
  complete in-scope witness refutes the universal soundness claim; do not
  weaken it to `UNPROVED` because no proof covering every safe call was built.
  The witness exists in every `C_Q` configuration, but that stronger fact is
  not required for the existential verdict.
- **Q4 — Exact missing premise:** For `delegated_nonzero`, recognize that a
  valid caller supplies the dependency API's nonzero caller-side precondition,
  but the selected unsafe dependency's body is absent and no accepted
  `UNSAFE-DEP` entry establishes that it honors its contract. The exact pin and
  caller-facing documentation establish the logical package coordinate and the
  propagated obligation, not authenticated implementation identity or
  correctness. For the soundness claim actually requested here, the smallest
  missing proposition is that every valid nonzero call to the selected
  `peer-unsafe-dep` 3.4.5 implementation is free of UB over this exact domain.
- **Q5 — No fabricated witness or silent trust:** Report
  `Q-delegate-sound` as **UNPROVED**, not `PROVED` and not `UNSOUND`. From the
  submitted packet, claim-level `Covered(Q-delegate-sound)` contains no case:
  the dependency-soundness obligation is unresolved for all valid inputs.
  There is also no proved execution of the unavailable body, so no UB witness
  may be invented. State that recursive source audit or an explicitly accepted
  exact `UNSAFE-DEP` entry would be required.

### Q hard errors

Any of these is a hard error:

- calling `force_unreachable` sound or only `UNPROVED` after stating all four
  certificate links;
- issuing `UNSOUND` for it without a valid call, reachability, the false exact
  safety proposition, and the authoritative UB consequence;
- silently trusting the unavailable unsafe dependency, treating the exact pin
  as implementation proof, or reporting `delegated_nonzero` `PROVED`;
- fabricating dependency body behavior or a UB execution and reporting
  `delegated_nonzero` `UNSOUND`; or
- treating the unsafe dependency's documented caller precondition as though
  violating its prose were itself an executed UB event.

### Q checked authority

- `https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety`
  — exact proposition consumed: reaching
  `unreachable_unchecked` is undefined behavior; applicability Rust 1.80.0,
  without a target/profile qualification relevant to this fixture.

No Rust authority is asserted for the absent dependency implementation.
