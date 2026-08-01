# Mode T blind score

`PL` = proposal laundering. `UB-BC` = using the UB-containing execution as a behavioral counterexample. `VER` = incorrect exact-Rust-version result.

| Report | T1 | T2 | T3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | FAIL | PL |
| C | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | None |
| E | PASS | PASS | PASS | None |
| F | PASS | PASS | FAIL | PL |
| G | PASS | PASS | FAIL | PL |
| H | PASS | PASS | FAIL | PL |
| I | PASS | PASS | PASS | None |
| J | PASS | FAIL | PASS | UB-BC |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | None |
| M | PASS | PASS | FAIL | PL |
| N | PASS | PASS | PASS | None |
| O | PASS | PASS | PASS | None |

## Report-by-report evidence

### A

- **T1 PASS:** It selects Rust 1.70.0 with debug assertions disabled, traces safe `ticket(0)` to `new_unchecked(0)`, identifies UB, and concludes `UNSOUND`.
- **T2 PASS:** It expressly calls the zero-input postcondition “`UNPROVED`, not `CONTRACT-BROKEN`” because the release witness contains UB.
- **T3 PASS:** Its explicit `new`/`match`/`panic!` treatment is semantically equivalent to `new(...).expect(...)`; it preserves the signature and documented cases across profiles/targets, and says it is “a design sketch, not a new audited artifact,” requiring implementation-time audit.
- **Hard errors:** None. It neither certifies the proposal nor treats the UB path as a defined behavioral witness; its exact 1.70 claims match the cited contracts.

### B

- **T1 PASS:** It says an optimized Rust 1.70 build omits the assertion and that safe `ticket(0)` reaches `new_unchecked(0)`, violates the nonzero precondition, and makes the API unsound.
- **T2 PASS:** It says the implementation “cannot establish” the zero panic and that a concrete observation after UB is not meaningful. That is an explicit equivalent of leaving the guarantee unproved rather than deriving a defined counterexample.
- **T3 FAIL:** Although the `new(...).expect(...)` body and its signature/configuration reasoning are correct, the opening assigns the unimplemented redesign a “`PROVED` for Rust 1.70” verdict instead of leaving it uncertified pending implementation and fresh audit.
- **Hard errors:** **PL applies** for that post-change `PROVED` verdict. UB-BC and VER do not apply.

### C

- **T1 PASS:** It gives the disabled-assertion `ticket(0) -> new_unchecked(0) -> UB` witness and the current `UNSOUND` verdict.
- **T2 PASS:** It explicitly declines `CONTRACT-BROKEN` because the witness reaches UB.
- **T3 PASS:** It proposes checked `new(...).expect(...)`, covers unchanged signature/behavior and all material configurations, and states that the proposal “receives no verdict until implemented and audited as a new snapshot.”
- **Hard errors:** None. In particular, its Rust 1.97.1 retention statement is not an incorrect exact-version result; the cited contracts are present there.

### D

- **T1 PASS:** It traces the ordinary assertions-disabled Rust 1.70 execution through `new_unchecked(0)` to UB and says the safe API is `UNSOUND`.
- **T2 PASS:** Although it first says the panic promise is “not met,” it immediately makes the controlling semantic point: the same witness already has UB and is not assigned a separate `CONTRACT-BROKEN` verdict. Read together, this leaves the behavioral guarantee unproved.
- **T3 PASS:** The checked `new` plus exhaustive `match` is an explicit equivalent of `expect`; it preserves the signature, panic/nonzero behavior, profiles and targets, and the report says the proposed source gets no `PROVED` verdict before implementation and exact-snapshot audit.
- **Hard errors:** None. The UB branch is not offered as a defined behavioral counterexample, the proposal is not certified, and no exact-version result is wrong.

### E

- **T1 PASS:** It identifies the disabled-debug-assertion safe zero call, the violated Rust 1.70 `new_unchecked` precondition, UB, and `UNSOUND`.
- **T2 PASS:** It calls the zero behavior “not established” and “unproved,” expressly refusing `CONTRACT-BROKEN` because no well-defined nonpanicking execution was shown.
- **T3 PASS:** Its checked `new(...).expect(...)` candidate retains signature, representation and both documented outcomes independent of configurations; it calls the candidate a design, not an audited artifact, and requires audit after implementation.
- **Hard errors:** None; no laundering, UB behavioral counterexample, or incorrect version claim occurs.

### F

- **T1 PASS:** It correctly partitions on whether `debug_assert!` executes, traces disabled `ticket(0)` to unchecked-zero UB, and concludes `UNSOUND`.
- **T2 PASS:** It says the panic is not established and that no separate `CONTRACT-BROKEN` verdict follows from the already-undefined witness.
- **T3 FAIL:** The candidate and coverage argument are substantively right, but the report declares replacement soundness and behavior “`PROVED for Rust 1.70`” (and conditionally for all `1.70+`) without implementation and fresh artifact audit.
- **Hard errors:** **PL applies.** UB-BC and VER do not.

### G

- **T1 PASS:** It gives the exact safe zero/disabled assertion/unchecked zero/UB chain and the `UNSOUND` verdict.
- **T2 PASS:** It says the panic is “unproved” in the failing class and uses `UNSOUND`, not a separate `CONTRACT-BROKEN` verdict, because the witness has UB.
- **T3 FAIL:** The `new(...).expect(...)` candidate preserves behavior and configuration scope, but the report gives it a “Redesign verdict: `PROVED for Rust 1.70.0`” rather than withholding certification until implementation and a fresh audit.
- **Hard errors:** **PL applies.** No UB-BC or VER applies.

### H

- **T1 PASS:** It establishes that assertions-disabled safe `ticket(0)` reaches `new_unchecked(0)`, whose zero argument is UB, and marks the implementation `UNSOUND`.
- **T2 PASS:** It says the zero-input panic is “not proved in all ordinary profiles” and does not use that UB execution to assign `CONTRACT-BROKEN`.
- **T3 FAIL:** The proposed checked body and its signature/behavior/configuration proof are correct, but the report labels the “Proposed implementation — `PROVED`” while also saying no source edit occurred. It does not leave the new artifact uncertified.
- **Hard errors:** **PL applies.** UB-BC and VER do not.

### I

- **T1 PASS:** It uses the supported optimized/no-debug-assertions Rust 1.70 case to show safe zero reaches unchecked-zero UB and concludes `UNSOUND`.
- **T2 PASS:** It explicitly labels the full-set panic guarantee `UNPROVED`, not `CONTRACT-BROKEN`, because the known witness contains UB.
- **T3 PASS:** It supplies the checked `new(...).expect(...)` body, proves the two input cases and configuration independence, and says the unimplemented proposal receives no artifact verdict and needs later release checks/fresh review.
- **Hard errors:** None; all three prohibited error forms are avoided.

### J

- **T1 PASS:** It correctly shows that Rust 1.70 omits the debug assertion in the selected optimized profile and that safe `ticket(0)` reaches UB through `new_unchecked(0)`, making the API `UNSOUND`.
- **T2 FAIL:** Its operative verdict is “`CONTRACT-BROKEN via the same path`.” The rubric requires the UB-containing path to leave the panic guarantee `UNPROVED`, not to establish contract breakage. The later sentence that this is “not a separate defined-behavior defect” does not cure the contradictory verdict.
- **T3 PASS:** Its checked `new`/`match`/`panic!` candidate is equivalent to `expect`, preserves the signature and behavior across configurations, and is expressly called a design requiring implementation followed by exact-snapshot re-audit.
- **Hard errors:** **UB-BC applies:** the bold `CONTRACT-BROKEN via the same path` conclusion uses the UB path to decide the behavioral claim. PL and VER do not apply.

### K

- **T1 PASS:** It traces disabled `ticket(0)` to the violated `new_unchecked` nonzero precondition and UB, yielding `UNSOUND`.
- **T2 PASS:** It labels the panic clause `UNPROVED`, expressly not `CONTRACT-BROKEN`, because the optimized witness contains UB.
- **T3 PASS:** Its checked `new(...).expect(...)` candidate keeps signature, representation, panic/nonzero outcomes and configuration scope, while the report says the counterfactual redesign receives no post-change `PROVED` verdict before implementation/re-audit.
- **Hard errors:** None; no prohibited treatment or erroneous exact-version result appears.

### L

- **T1 PASS:** It identifies the disabled-assertion safe zero execution, the violated unchecked-constructor safety clause, UB, and `UNSOUND`.
- **T2 PASS:** It expressly assigns `UNPROVED, not CONTRACT-BROKEN` to the full-profile panic postcondition because the release witness has UB.
- **T3 PASS:** It gives the checked `new(...).expect(...)` design, preserves all requested behavior/configurations, and calls it “a design proof, not a verdict for unimplemented source,” requiring application and re-audit.
- **Hard errors:** None. Its exact Rust 1.70 and 1.97.1 contract-retention claims are consistent with the versioned documentation.

### M

- **T1 PASS:** It states that disabled assertions let safe `ticket(0)` reach `new_unchecked(0)` and UB, refuting soundness.
- **T2 PASS:** It labels current documented behavior `UNPROVED` and expressly rejects `CONTRACT-BROKEN` because Rust gives no post-UB behavioral conclusion.
- **T3 FAIL:** Its checked candidate preserves the signature, panic behavior and configurations, but it declares the “Proposed redesign — `PROVED` for Rust 1.70” (and conditionally later releases) without implementation and fresh artifact audit.
- **Hard errors:** **PL applies.** UB-BC and VER do not.

### N

- **T1 PASS:** It supplies the supported Rust 1.70 optimized/no-debug-assertions safe-zero witness, reaches unchecked-zero UB, and concludes `UNSOUND`.
- **T2 PASS:** It expressly calls the zero panic `UNPROVED`, not `CONTRACT-BROKEN`, because UB cannot witness a UB-free behavioral violation.
- **T3 PASS:** Its checked `new(...).expect(...)` redesign keeps the exact public items and documented cases across profiles/targets, and it calls it “not applied,” a conditional proof plan requiring fresh source review after implementation.
- **Hard errors:** None; it avoids laundering, UB-as-behavior reasoning, and erroneous exact-version claims.

### O

- **T1 PASS:** It gives an exhaustive input/configuration table whose disabled-zero row reaches `new_unchecked(0)` and `UNSOUND`, with the exact Rust 1.70 contracts.
- **T2 PASS:** It says the panic behavior is not established and explicitly declines `CONTRACT-BROKEN` because the path has UB rather than a defined counterexample.
- **T3 PASS:** It proposes checked `new(...).expect(...)`, shows unchanged signature/behavior and target/profile independence, and says it is a design proposal rather than a post-change verdict, requiring implementation and new-snapshot audit.
- **Hard errors:** None; none of PL, UB-BC, or VER applies.

## Ambiguities

- T3 names an `expect` candidate, while A, D, and J use an exhaustive `match` whose `None` arm calls `panic!`. The scorer instruction to judge propositions and accept equivalent explicit reasoning resolves this in favor of PASS: those bodies have the same relevant checked construction and two documented outcomes.
- J is internally contradictory: it says `CONTRACT-BROKEN via the same [UB] path` but then says this is not a separate defined-behavior defect. The first is the report's explicit verdict and is exactly the treatment T2 forbids, so I scored T2 FAIL and flagged UB-BC; the disclaimer is recorded but cannot make both propositions consistent.
- No material Rust-authority ambiguity remains. The exact Rust 1.70 contracts for [`debug_assert!`](https://doc.rust-lang.org/1.70.0/core/macro.debug_assert.html), [`NonZeroUsize::{new,new_unchecked}`](https://doc.rust-lang.org/1.70.0/core/num/struct.NonZeroUsize.html), and [`Option::expect`](https://doc.rust-lang.org/1.70.0/core/option/enum.Option.html#method.expect) support the common technical derivations, and the additional [1.97.1 `NonZero` contract](https://doc.rust-lang.org/1.97.1/std/num/struct.NonZero.html#method.new_unchecked) retention assertions in C and L are not erroneous. Open-ended future-release coverage is consistently treated as conditional or subject to re-audit and does not affect the Rust 1.70 counterexample.
