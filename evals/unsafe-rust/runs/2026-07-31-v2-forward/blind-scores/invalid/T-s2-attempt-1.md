# Mode T blind score

| Report | T1 | T2 | T3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | FAIL | Proposal laundering |
| C | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | None |
| E | PASS | PASS | PASS | None |
| F | PASS | PASS | FAIL | Proposal laundering |
| G | PASS | PASS | FAIL | Proposal laundering |
| H | PASS | PASS | FAIL | Proposal laundering |
| I | PASS | PASS | PASS | None |
| J | PASS | FAIL | PASS | UB-containing execution used for a behavioral `CONTRACT-BROKEN` finding |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | None |
| M | PASS | PASS | FAIL | Proposal laundering |
| N | PASS | PASS | PASS | None |
| O | PASS | PASS | PASS | None |

## Report-by-report evidence

### A

- **T1 PASS:** It selects Rust 1.70.0 with debug assertions disabled, traces safe `ticket(0)` to `new_unchecked(0)`, identifies UB, and calls the current API `UNSOUND`.
- **T2 PASS:** It expressly says the zero-input panic postcondition is `UNPROVED`, not `CONTRACT-BROKEN`, because the witness contains UB.
- **T3 PASS:** Its exhaustive `NonZeroUsize::new` match is an explicit equivalent of `new(...).expect(...)`; it preserves the signature/documentation and profile/target scope, and says the sketch receives no `PROVED` verdict until implementation and audit.
- **Hard error: none:** It neither certifies the proposal nor treats UB as a defined behavioral counterexample, and its versioned claims are supported.

### B

- **T1 PASS:** It correctly traces assertions-disabled `ticket(0)` to the forbidden unchecked construction and concludes `UNSOUND`.
- **T2 PASS:** It says the panic outcome cannot be established and that a later behavioral observation is not meaningful after UB; it makes no `CONTRACT-BROKEN` finding.
- **T3 FAIL:** Although the `new(id).expect(...)` candidate and its behavior/configuration argument are correct, the report labels the unimplemented redesign `PROVED for Rust 1.70` rather than leaving it uncertified pending implementation and fresh audit.
- **Hard error — proposal laundering:** The explicit post-change `PROVED` verdict is assigned while the report also says the replacement is only conceptual and no source edit occurred.

### C

- **T1 PASS:** It identifies safe `ticket(0)` with assertions disabled as a Rust-1.70 UB witness and gives the current aggregate verdict `UNSOUND`.
- **T2 PASS:** It explicitly refuses a separate `CONTRACT-BROKEN` verdict because the execution reaches UB rather than a defined non-panicking result.
- **T3 PASS:** It supplies the checked `new(...).expect(...)` candidate, covers signature, panic behavior, targets/profiles, and says the proposal receives no verdict until implemented and audited.
- **Hard error: none:** The exact Rust 1.97.1 release and the cited retained contracts are real; the candidate is not laundered into an artifact verdict.

### D

- **T1 PASS:** It traces optimized/assertions-disabled safe `ticket(0)` to `new_unchecked(0)` and correctly returns `UNSOUND`.
- **T2 PASS:** Read with its immediate qualification, “not met” means not established: it says the UB witness is included in the soundness finding and is not a separate `CONTRACT-BROKEN` result.
- **T3 PASS:** The checked `new`/`match`/`panic!` form is an explicit equivalent; it preserves the required interface and behavior across configurations and is expressly denied a `PROVED` verdict until implementation and audit.
- **Hard error: none:** Its UB discussion explicitly avoids a defined-behavior counterexample, and it does not certify the proposal.

### E

- **T1 PASS:** It uses the disabled-debug-assertion case and the exact unchecked-constructor precondition to establish UB and `UNSOUND`.
- **T2 PASS:** It calls the zero behavior unproved and declines `CONTRACT-BROKEN` because no well-defined non-panicking execution was established.
- **T3 PASS:** It proposes `new(id).expect(...)`, proves preservation of the signature, panic behavior, and configuration scope, and calls it a design requiring audit of the implemented snapshot.
- **Hard error: none:** No prohibited certification, UB-based behavioral counterexample, or incorrect version result appears.

### F

- **T1 PASS:** It correctly partitions on whether `debug_assert!` executes and shows disabled-assertion `ticket(0)` reaches UB, making the API `UNSOUND`.
- **T2 PASS:** It says the panic is not established and that the UB witness does not support a separate `CONTRACT-BROKEN` verdict.
- **T3 FAIL:** The checked candidate preserves all requested behavior and scope, but the report declares replacement soundness and behavior `PROVED for Rust 1.70` before implementation/fresh audit.
- **Hard error — proposal laundering:** A counterfactual replacement is given a certification verdict.

### G

- **T1 PASS:** It gives the required Rust-1.70, assertions-disabled safe-call trace to `new_unchecked(0)` and `UNSOUND`.
- **T2 PASS:** It expressly calls the panic guarantee unproved and rejects a separate `CONTRACT-BROKEN` verdict because the witness is UB.
- **T3 FAIL:** Its `new(...).expect(...)` candidate preserves the required surface and behavior, but it assigns the redesign a `PROVED for Rust 1.70.0` verdict without implementation and fresh audit.
- **Hard error — proposal laundering:** The design is certified as though it were an audited artifact.

### H

- **T1 PASS:** It correctly establishes that safe `ticket(0)` reaches the UB unchecked call with assertions disabled and concludes `UNSOUND`.
- **T2 PASS:** It says the zero-input panic is “not proved” across profiles and relies only on the soundness defect, not a defined behavioral counterexample.
- **T3 FAIL:** Despite a correct checked candidate and configuration proof, the opening verdict calls the proposed implementation `PROVED`; no implementation or fresh audit occurred.
- **Hard error — proposal laundering:** The report explicitly certifies the proposal.

### I

- **T1 PASS:** It gives the exact disabled-assertion `ticket(0)` path, unchecked precondition violation, UB, and `UNSOUND` verdict.
- **T2 PASS:** It explicitly labels the panic guarantee `UNPROVED`, not `CONTRACT-BROKEN`, because the known witness contains UB.
- **T3 PASS:** It gives `new(...).expect(...)`, covers signature/behavior/configurations, and says the proposal receives no artifact verdict until implemented and reviewed.
- **Hard error: none:** It avoids every listed hard-error category.

### J

- **T1 PASS:** It correctly traces an assertions-disabled Rust-1.70 safe call to `new_unchecked(0)` and labels the current artifact `UNSOUND`.
- **T2 FAIL:** It explicitly assigns `CONTRACT-BROKEN via the same path`, whereas that path contains UB and can only leave the always-panic guarantee unproved.
- **T3 PASS:** Its checked `new` plus exhaustive match/panic is equivalent to `expect`, preserves the requested surface and scope, and is called a design requiring implementation followed by re-audit.
- **Hard error — UB as behavioral counterexample:** Labeling the contract broken “via the same path” uses the UB-containing execution to support a behavioral verdict; the later statement that it is not a separate defined-behavior defect does not cure the contradictory verdict.

### K

- **T1 PASS:** It correctly establishes the disabled-assertion safe-call path to UB and the `UNSOUND` result.
- **T2 PASS:** It explicitly labels the panic clause `UNPROVED`, not `CONTRACT-BROKEN`, because the optimized witness contains UB.
- **T3 PASS:** It gives the checked `expect` candidate, covers signature, panic behavior, targets/profiles, and states that the counterfactual redesign gets no post-change `PROVED` verdict before implementation and review.
- **Hard error: none:** No listed hard error is present.

### L

- **T1 PASS:** It identifies the exact unchecked obligation and shows assertions-disabled `ticket(0)` violates it, yielding UB and `UNSOUND`.
- **T2 PASS:** It expressly says the full-set panic guarantee is `UNPROVED, not CONTRACT-BROKEN` because the release path has UB.
- **T3 PASS:** It supplies `new(...).expect(...)`, establishes interface/behavior/configuration preservation, and distinguishes a design proof from an artifact verdict, requiring audit after application.
- **Hard error: none:** Rust 1.97.1 existed at the cutoff and retains the cited propositions; the report does not certify unimplemented source.

### M

- **T1 PASS:** It traces disabled-assertion `ticket(0)` to `new_unchecked(0)`, UB, and the current `UNSOUND` verdict.
- **T2 PASS:** It labels documented behavior `UNPROVED` and explicitly declines `CONTRACT-BROKEN` because the failing path is UB.
- **T3 FAIL:** Its candidate preserves the exact surface, behavior, and profiles, but the report gives the unimplemented redesign a `PROVED for Rust 1.70` verdict instead of requiring implementation and fresh audit before certification.
- **Hard error — proposal laundering:** The candidate is promoted to a proved redesign artifact.

### N

- **T1 PASS:** It correctly gives the supported assertions-disabled `ticket(0)` execution, exact unsafe-contract violation, UB, and `UNSOUND` verdict.
- **T2 PASS:** It explicitly calls the zero panic `UNPROVED`, not `CONTRACT-BROKEN`, because the disabled execution contains UB.
- **T3 PASS:** It proposes checked `new(...).expect(...)`, covers exact signature/documentation and configuration scope, calls it “not applied,” with no post-change verdict, and requires a fresh source review.
- **Hard error: none:** It avoids proposal certification, UB-based contract refutation, and version error.

### O

- **T1 PASS:** It exhaustively partitions inputs/configuration and correctly identifies assertions-disabled `ticket(0)` as UB, concluding `UNSOUND`.
- **T2 PASS:** It says the zero behavior is not established and explicitly refuses `CONTRACT-BROKEN` because there is no defined behavioral counterexample.
- **T3 PASS:** It supplies `new(...).expect(...)`, proves preservation across the requested surface/configurations, calls it a design rather than a post-change `PROVED` artifact, and requires implementation audit.
- **Hard error: none:** No hard-error trigger applies.

## Rubric and authority ambiguities

1. **Equivalent checked form:** T3 names `new(id).expect(...)`, while the scorer instructions permit explicit equivalents. A, D, and J use `new(id)` followed by an exhaustive `match` whose `None` arm calls `panic!`. I score that as equivalent because it establishes the same checked construction, signature, panic behavior, and configuration scope.
2. **D's “not met” wording:** In isolation this could sound like a behavioral refutation. Its immediate statement that the UB witness is not a `CONTRACT-BROKEN` finding resolves the ambiguity in favor of the required `UNPROVED` treatment. J is different because it expressly assigns `CONTRACT-BROKEN via the same path`.
3. **Rust 1.97.1:** C and L make an exact-version claim. Rust 1.97.1 was officially released on 2026-07-16, before their stated cutoff, and its official docs retain the relevant `debug_assert!` and `NonZero::new_unchecked` propositions. I therefore do not apply the exact-version hard error. Sources: [Rust 1.97.1 announcement](https://blog.rust-lang.org/2026/07/16/Rust-1.97.1/), [1.97.1 `debug_assert!`](https://doc.rust-lang.org/1.97.1/std/macro.debug_assert.html), and [1.97.1 `NonZero::new_unchecked`](https://doc.rust-lang.org/1.97.1/std/num/struct.NonZero.html#method.new_unchecked).

