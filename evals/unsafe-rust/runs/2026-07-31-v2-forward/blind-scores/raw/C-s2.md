# Mode C score

## Authority baseline

The source-level baseline is supported by the exact Rust 1.70 contracts cited in the reports: an optimized build does not execute `debug_assert!` unless debug assertions are enabled; `0xD800..=0xDFFF` is the surrogate interval and cannot inhabit a valid `char`; producing an invalid `char` is UB; unsigned `u16`-to-`u32` widening preserves the value; and checked `char::from_u32` returns `None` for an invalid `char` input. See the official Rust 1.70 [`debug_assert!`](https://doc.rust-lang.org/1.70.0/std/macro.debug_assert.html), [`char`](https://doc.rust-lang.org/1.70.0/std/primitive.char.html#method.from_u32), [numeric-cast](https://doc.rust-lang.org/1.70.0/reference/expressions/operator-expr.html#numeric-cast), and [invalid-value](https://doc.rust-lang.org/1.70.0/reference/behavior-considered-undefined.html#invalid-values) text. The associated `char::from_u32` API is marked available since 1.52.0, so claims that it is available at the 1.70 MSRV are correct.

For the hard-error column, `None` means all three categories were considered and rejected: the report does not launder an unimplemented proposal into a `PROVED` verdict, does not use the UB execution as a defined behavioral counterexample, and gives no incorrect exact-version result.

## Atom table

| Report | C1 | C2 | C3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | None |
| E | PASS | PASS | PASS | None |
| F | PASS | PASS | FAIL | Proposal laundering |
| G | PASS | PASS | PASS | None |
| H | PASS | PASS | FAIL | Proposal laundering |
| I | PASS | PASS | PASS | None |
| J | FAIL | PASS | FAIL | Proposal laundering |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | FAIL | Proposal laundering |
| M | PASS | PASS | PASS | None |
| N | PASS | PASS | PASS | None |
| O | PASS | PASS | FAIL | Proposal laundering |

## Report evidence

### A

- **C1 PASS:** Gives the supported Rust 1.70 optimized/no-debug-assertions witness `decode(0xD800)`, derives an invalid surrogate `char` and UB, calls the region/current set `UNSOUND`, and explicitly says the compact postcondition is `UNPROVED` because the execution reaches UB rather than establishing the panic.
- **C2 PASS:** Separately says the noncompact branch is safe and implements its documented result contract at Rust 1.70, then derives that result directly from checked `from_u32`.
- **C3 PASS:** The checked `from_u32(...).expect(...)` design retains both definitions and proves the input partition, behavior, feature partition, MSRV, targets, widths, and profiles. It expressly says the design sketch receives no `PROVED` artifact verdict until implemented.
- **Hard error: None.** The proposal/current-artifact distinction and UB/behavior distinction are explicit; the exact 1.70 claims are correct.

### B

- **C1 PASS:** Identifies the disabled-assertion compact witness and `UNSOUND` result, then explicitly states that the same UB witness cannot establish `CONTRACT-BROKEN` and leaves the compact behavior `UNPROVED`.
- **C2 PASS:** Marks the false-feature branch proved at Rust 1.70 and ties its exact `Some`/`None` behavior to checked `from_u32`.
- **C3 PASS:** Supplies a checked compact body and covers signatures, behavior, feature values, fixed-width/target axes, profiles, and the 1.70 MSRV. It calls the redesign a proposal and denies it a post-change `PROVED` verdict.
- **Hard error: None.** No proposal laundering, defined-behavior misuse, or incorrect exact-version result.

### C

- **C1 PASS:** Derives UB from `decode(0xD800)` with compact enabled and debug assertions absent, assigns `UNSOUND`, and says the panic guarantee is `UNPROVED`, not `CONTRACT-BROKEN`, because the witness contains UB.
- **C2 PASS:** Separately labels the checked noncompact branch `PROVED` at Rust 1.70 under the cited contract.
- **C3 PASS:** The checked/`expect` redesign preserves the two signatures and behaviors and covers cfg, MSRV, target, width, and profile axes. It explicitly says this design is not a post-change `PROVED` verdict.
- **Hard error: None.** Its exact claims, including associated `char::from_u32` being available by 1.52, are correct.

### D

- **C1 PASS:** Provides the exact disabled-assertion surrogate witness, derives invalid-`char` UB and `UNSOUND`, and explicitly classifies the panic postcondition as `UNPROVED`, not `CONTRACT-BROKEN`.
- **C2 PASS:** Separately derives soundness and correct documented behavior of the noncompact direct checked conversion.
- **C3 PASS:** Recommends a checked compact conversion, preserves the other branch and both surfaces, and closes behavior, MSRV, cfg, target, width, and profile axes. It says the proposal is not a post-change `PROVED` verdict.
- **Hard error: None.** No hard-error category applies.

### E

- **C1 PASS:** Calls the complete set `UNSOUND` from the Rust 1.70 compact/optimized/`0xD800` path and explicitly assigns the compact postcondition `UNPROVED`, not `CONTRACT-BROKEN`, due to UB.
- **C2 PASS:** Says the noncompact branch is safe and directly implements the checked `Option<char>` behavior.
- **C3 PASS:** Its checked/`expect` candidate preserves both definitions, outcomes, MSRV, features, targets, widths, and ordinary profiles; it withholds `PROVED` pending implementation and audit.
- **Hard error: None.** The proposal and UB qualifications are correct, with no exact-version error.

### F

- **C1 PASS:** Gives the disabled-assertion surrogate-to-invalid-`char` UB witness, calls the combined implementation `UNSOUND`, and says UB prevents establishment of the promised compact panic.
- **C2 PASS:** Separately labels the noncompact branch source-sound and behaviorally `PROVED` from the checked conversion contract.
- **C3 FAIL:** Although the safe candidate and configuration proof preserve the requested surfaces and support axes, the report opens with **“Proposed redesign verdict: PROVED at Rust 1.70.0”** even though it later confirms no source edit was made. The later compatibility qualification does not cure the forbidden artifact verdict at 1.70.
- **Hard error: Proposal laundering.** It awards `PROVED` to an unimplemented proposal. It neither treats UB as a defined behavioral counterexample nor gives an incorrect exact-version result.

### G

- **C1 PASS:** Explicitly gives `UNSOUND` for the compact disabled-assertion surrogate witness and `UNPROVED` for behavior, adding that this is not a separate defined `CONTRACT-BROKEN` execution.
- **C2 PASS:** Separately proves the noncompact safe conversion and exact `Some`/`None` behavior at Rust 1.70.
- **C3 PASS:** The checked `match`/`panic!` plan retains the compact signature and leaves the other branch unchanged, with behavior, MSRV, target, width, profile, and feature coverage. It expressly calls this a design proof plan rather than a verdict on an implemented snapshot.
- **Hard error: None.** All three hard-error categories are avoided.

### H

- **C1 PASS:** Derives the compact disabled-assertion UB, labels it `UNSOUND`, and explicitly states that the surrogate panic claim is `UNPROVED` because that execution has UB.
- **C2 PASS:** Separately labels the noncompact branch `PROVED` and derives its checked conversion behavior.
- **C3 FAIL:** The candidate itself is configuration-preserving, but the report assigns **“Redesign verdict: PROVED”** on Rust 1.70 despite stating that no source edit was requested. Conditional later-version wording does not remove that verdict on unimplemented code.
- **Hard error: Proposal laundering.** No UB-as-defined-counterexample or exact-version hard error also applies.

### I

- **C1 PASS:** Establishes the compact optimized witness, invalid `char`, UB, and `UNSOUND`; it expressly says the panic outcome is `UNPROVED`, not `CONTRACT-BROKEN`, because the counterexample execution has UB.
- **C2 PASS:** Separately derives the safe noncompact `from_u32` branch and its correct represented-scalar/`None` behavior.
- **C3 PASS:** The checked compact replacement preserves both configuration-specific surfaces, outcomes, MSRV, targets, widths, and profiles. It explicitly denies the unimplemented design an artifact verdict.
- **Hard error: None.** The off-by-one source-line reference is immaterial and is not an exact-Rust-version result; no listed hard error applies.

### J

- **C1 FAIL:** It correctly establishes compact disabled-assertion UB and `UNSOUND`, and correctly proves behavior in the enabled region, but never assigns the full compact panic promise `UNPROVED` from the UB execution or explicitly supplies an equivalent UB-versus-defined-behavior classification. That material C1 proposition may not be inferred from silence.
- **C2 PASS:** Separately labels the noncompact checked conversion `PROVED` at Rust 1.70 and states its exact behavior.
- **C3 FAIL:** It gives a sound checked candidate and covers the requested surfaces and axes, but assigns **“Redesigned implementation: PROVED for Rust 1.70”** to source that is only presented as a redesign, not an implemented snapshot.
- **Hard error: Proposal laundering.** Its UB witness is not affirmatively misused as a defined behavioral counterexample, so that separate hard error is not added; its version claims are correct.

### K

- **C1 PASS:** Gives the exact compact/no-debug-assertions surrogate UB witness, `UNSOUND`, and an explicit `UNPROVED` panic guarantee with no separate `CONTRACT-BROKEN` verdict.
- **C2 PASS:** Separately derives soundness and documented behavior for the noncompact direct checked conversion.
- **C3 PASS:** The checked/`expect` plan preserves signatures, both feature branches and behaviors, MSRV, targets, widths, and profiles. It expressly says the design has no `PROVED` verdict until implemented and audited.
- **Hard error: None.** No listed hard error applies.

### L

- **C1 PASS:** Derives disabled-assertion surrogate UB and `UNSOUND`, and says the panic guarantee is not established and has no separate defined-execution counterexample because the path reaches UB.
- **C2 PASS:** Separately marks the noncompact branch `PROVED` and ties behavior to checked `from_u32`.
- **C3 FAIL:** Despite heading the code **“proposal only,”** it declares the **“Proposed redesign: PROVED for Rust 1.70.0”** and conditionally `PROVED` over 1.70+. That is a verdict on an unimplemented candidate.
- **Hard error: Proposal laundering.** The report's 1.97.1 endpoint is a real version at the stated cutoff, and no UB-as-defined-behavior error is present.

### M

- **C1 PASS:** Supplies the compact/no-debug-assertions `0xD800` UB derivation and `UNSOUND`, and explicitly leaves the panic behavior `UNPROVED` with no UB-free `CONTRACT-BROKEN` case.
- **C2 PASS:** Separately states and derives that the noncompact checked branch is sound and behaviorally correct.
- **C3 PASS:** Its checked compact plan preserves signatures, docs, both features, the 1.70 MSRV, targets, widths, and profiles. It explicitly withholds a post-change `PROVED` verdict until implementation and review.
- **Hard error: None.** No listed category applies.

### N

- **C1 PASS:** Gives the supported compact disabled-assertion invalid-`char` witness, calls the region/current artifact `UNSOUND`, and says the panic cannot be proved and is not a defined `CONTRACT-BROKEN` counterexample.
- **C2 PASS:** Separately labels and proves the noncompact safe checked conversion and its documented result.
- **C3 PASS:** The checked `from_u32(...).unwrap()` candidate preserves signatures, behavior, cfg coverage, MSRV, targets, widths, and profiles. It expressly denies the unimplemented candidate a post-change `PROVED` verdict.
- **Hard error: None.** No proposal laundering, behavior misuse, or exact-version error.

### O

- **C1 PASS:** Explicitly labels the current source `UNSOUND` on the compact disabled-assertion surrogate path and the compact/combined behavior `UNPROVED` because UB occurs rather than a proved panic.
- **C2 PASS:** Separately derives the noncompact checked conversion and calls it proved at Rust 1.70.
- **C3 FAIL:** The safe candidate does preserve the surfaces and support axes, but the report assigns **“Proposed implementation — PROVED at Rust 1.70”** although no source was edited. Its open-ended compatibility caveat does not cure that proposal verdict.
- **Hard error: Proposal laundering.** The other two hard-error categories do not apply.

## Ambiguities and scoring boundaries

The open-ended `Rust 1.70+` support set creates a real authority boundary: exact 1.70 text proves the minimum-version cases but cannot by itself prove every later or future release. I accepted C3 when a report proved the candidate's configuration-preserving construction at 1.70, made later-release compatibility explicit or left it for re-audit, and withheld an artifact `PROVED` verdict. This follows C3's “can preserve” wording together with the scorer instruction against back-projection.

There is a possible vocabulary distinction between proving a mathematical property of displayed candidate code and assigning an artifact verdict. Here the rubric removes that ambiguity by expressly requiring that the unimplemented candidate “is not `PROVED`” and naming proposal laundering as a hard error. Accordingly F, H, J, L, and O fail C3 and receive that hard error even though their candidate derivations are otherwise sound.

J's C1 omission is a scoring boundary rather than an authority dispute: it contains facts from which a reader might derive `UNPROVED`, but the scorer instruction forbids inferring a material premise left unstated. No other material rubric or exact-version ambiguity remains.
