# Mode T blind score

`PASS` means every material proposition in the atom is established (including an explicit equivalent treatment). `FAIL` identifies a missing or contrary material proposition. Hard errors are assessed independently.

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
| J | PASS | FAIL | PASS | UB execution used as a behavioral counterexample |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | None |
| M | PASS | PASS | FAIL | Proposal laundering |
| N | PASS | PASS | PASS | None |
| O | PASS | PASS | PASS | None |

Totals: T1 15/15 PASS; T2 14/15 PASS; T3 10/15 PASS; 6 reports have a hard error.

## Report-by-report evidence

### A

- **T1 PASS:** It selects Rust 1.70.0 with debug assertions disabled, follows safe `ticket(0)` to `new_unchecked(0)`, cites the exact 1.70 contracts, concludes UB, and labels the current API `UNSOUND`.
- **T2 PASS:** It expressly calls the zero-input postcondition `UNPROVED, not CONTRACT-BROKEN`, because the witness contains UB and is not a UB-free behavioral counterexample.
- **T3 PASS:** Its `NonZeroUsize::new`/`match`/`panic!` body is an explicit equivalent to `new(...).expect(...)`; it preserves the body-level signature and documented cases across profiles. It says the sketch receives no `PROVED` verdict and requires audit of the implemented snapshot.
- **Hard error: none:** It neither certifies the proposal nor treats UB as defined behavior; its material Rust premises are tied to Rust 1.70 documentation.

### B

- **T1 PASS:** It establishes that an ordinary assertions-disabled Rust 1.70 build lets safe `ticket(0)` reach `new_unchecked(0)`, violating the cited nonzero precondition and making the API `UNSOUND`.
- **T2 PASS:** It says the path cannot establish the documented panic and that observation after UB is not meaningful; it does not use the path as a defined contract counterexample.
- **T3 FAIL:** Although the `new(id).expect(...)` candidate and its behavior/configuration proof are otherwise adequate, the report opens with `Proposed redesign verdict: PROVED for Rust 1.70`. That contradicts the required unimplemented-and-unaudited status.
- **Hard error — proposal laundering:** Restricting the certification to Rust 1.70 and leaving the open-ended later range unproved does not cure certification of source that was never implemented and freshly audited.

### C

- **T1 PASS:** It gives the required disabled-assertion `ticket(0) -> new_unchecked(0) -> UB` execution and current `UNSOUND` verdict using exact Rust 1.70 documentation.
- **T2 PASS:** It explicitly declines `CONTRACT-BROKEN` because the counterexample reaches UB rather than a defined non-panicking outcome.
- **T3 PASS:** It proposes `new(id).expect(...)`, proves preservation of nonzero return, zero panic, signature, targets, and profiles, then states that the proposal receives no verdict until implemented and audited as a new snapshot.
- **Hard error: none:** No proposal certification or UB-based behavioral counterexample appears, and its additional exact-version 1.97.1 continuity statement is not incorrect.

### D

- **T1 PASS:** It uses the Rust 1.70 disabled-debug-assertion path to show `ticket(0)` calls `new_unchecked(0)`, reaches UB, and makes the safe API `UNSOUND`.
- **T2 PASS:** Although it initially says the promise is “not met,” it immediately makes the controlling distinction: the witness has UB and is not assigned a separate non-UB `CONTRACT-BROKEN` verdict. In context this is failure of proof, not a defined counterexample.
- **T3 PASS:** The checked `new` plus exhaustive `match` and `panic!` is equivalent to `expect`; the report covers the signature, both input cases, and configuration scope, and withholds `PROVED` pending implementation and audit.
- **Hard error: none:** The contextual qualification prevents the “not met” wording from using UB as defined behavior; the proposal remains uncertified.

### E

- **T1 PASS:** It follows assertions-disabled `ticket(0)` to the exact Rust 1.70 `new_unchecked(0)` UB condition and concludes `UNSOUND`.
- **T2 PASS:** It says the panic behavior is unproved and rejects `CONTRACT-BROKEN` because no well-defined non-panicking execution was established.
- **T3 PASS:** It supplies `new(id).expect(...)`, verifies both inputs and configuration independence while preserving the public surface, and calls it a design requiring audit after implementation.
- **Hard error: none:** The proposal is not awarded a post-change verdict, the UB path is not a behavioral counterexample, and the cited Rust premises are version matched.

### F

- **T1 PASS:** It gives the safe zero-input, disabled-assertion Rust 1.70 UB path and an unqualified current `UNSOUND` verdict.
- **T2 PASS:** It says the zero panic is not established and that the already-undefined witness warrants no separate `CONTRACT-BROKEN` verdict.
- **T3 FAIL:** The `new(id).expect(...)` body and preservation proof are adequate, but it declares replacement soundness and behavior `PROVED for Rust 1.70` and, conditionally, for 1.70+. It never preserves the candidate’s required uncertified status.
- **Hard error — proposal laundering:** The explicit compatibility premise only qualifies version reach; it cannot certify an unimplemented, unaudited replacement.

### G

- **T1 PASS:** It identifies disabled assertions, safe zero input, violation of the exact Rust 1.70 unchecked-constructor contract, UB, and current `UNSOUND`.
- **T2 PASS:** It calls the panic guarantee unproved and explains that the witness itself reaches UB rather than supporting `CONTRACT-BROKEN`.
- **T3 FAIL:** Despite a correct `new(id).expect(...)` design and case/configuration argument, it assigns `Redesign verdict: PROVED for Rust 1.70.0` instead of requiring implementation and fresh audit.
- **Hard error — proposal laundering:** Its open-ended-version qualification does not remove the prohibited verdict on the unimplemented Rust 1.70 candidate.

### H

- **T1 PASS:** It correctly partitions the inputs/assertion settings and shows that the disabled-zero branch reaches Rust 1.70 `new_unchecked(0)` UB, establishing current `UNSOUND`.
- **T2 PASS:** It says the zero panic is not proved over all profiles and treats soundness failure, not a defined contract counterexample, as the terminal result.
- **T3 FAIL:** The report validates a suitable `new(id).expect(...)` replacement, but begins with `Proposed implementation — PROVED` for Rust 1.70 and conditionally for later releases. It does not require a post-implementation snapshot audit before that verdict.
- **Hard error — proposal laundering:** A conditional TCB can qualify premises but cannot turn proposed text into an audited artifact.

### I

- **T1 PASS:** It explicitly derives the assertions-disabled safe `ticket(0)` path to `new_unchecked(0)`, cites Rust 1.70, concludes UB, and labels the current API `UNSOUND`.
- **T2 PASS:** It labels the full-set zero panic `UNPROVED, not CONTRACT-BROKEN` because the known witness contains UB.
- **T3 PASS:** It gives the checked `new(id).expect(...)` candidate, proves signature/behavior/configuration preservation, and explicitly says a proposal receives no artifact verdict and needs a fresh implemented-snapshot review.
- **Hard error: none:** All three prohibited hard-error patterns are avoided.

### J

- **T1 PASS:** It correctly shows that Rust 1.70 with debug assertions disabled permits safe `ticket(0)` to reach `new_unchecked(0)` UB and labels the API `UNSOUND`.
- **T2 FAIL:** It expressly assigns `CONTRACT-BROKEN via the same path`, whereas that path contains UB and can establish only that the panic guarantee is unproved.
- **T3 PASS:** Its checked `new`/`match`/`panic!` candidate is equivalent to `expect`, preserves the safe public contract and profile scope, and is explicitly left as a design pending implementation and re-audit.
- **Hard error — UB execution used as a behavioral counterexample:** The later sentence that this is “not a separate defined-behavior defect” does not retract the explicit `CONTRACT-BROKEN` verdict “via the same path”; the report assigns the forbidden behavioral result nonetheless.

### K

- **T1 PASS:** It provides the complete safe-zero, assertions-disabled, Rust 1.70 unchecked-zero UB derivation and current `UNSOUND` verdict.
- **T2 PASS:** It explicitly labels the panic clause `UNPROVED`, rejects `CONTRACT-BROKEN`, and explains why UB cannot witness defined failure to panic.
- **T3 PASS:** It gives `new(id).expect(...)`, covers both inputs and all relevant configurations while preserving the public surface, and withholds a post-change verdict until exact-source audit.
- **Hard error: none:** It avoids proposal certification, defined post-UB reasoning, and incorrect version results.

### L

- **T1 PASS:** It correctly derives UB from disabled `debug_assert!` plus safe zero input under the exact Rust 1.70 contracts and concludes current `UNSOUND`.
- **T2 PASS:** It expressly says `UNPROVED, not CONTRACT-BROKEN`, because the disabled execution contains UB.
- **T3 PASS:** It proposes `new(id).expect(...)`, proves preservation across inputs and configurations, and says this is not a verdict for unimplemented source; application must be followed by re-audit of the new snapshot.
- **Hard error: none:** Its “intended post-change” result is conditional on applying and re-auditing, so it is not proposal laundering; no incorrect exact-version result was found.

### M

- **T1 PASS:** It establishes the disabled-assertion `ticket(0) -> new_unchecked(0) -> UB` witness and current `UNSOUND` verdict from exact Rust 1.70 contracts.
- **T2 PASS:** It labels behavior `UNPROVED` and explicitly refuses `CONTRACT-BROKEN` because Rust supplies no post-UB behavioral conclusion.
- **T3 FAIL:** Its checked `new(id).expect(...)` source and preservation reasoning are suitable, but it declares `Proposed redesign — PROVED for Rust 1.70, all targets and profiles` without first requiring implementation and a fresh snapshot audit.
- **Hard error — proposal laundering:** The compatibility TCB qualifies later versions only and does not validate the unimplemented proposal as an artifact.

### N

- **T1 PASS:** It uses exact Rust 1.70 documentation to show safe `ticket(0)` reaches unchecked zero with assertions disabled, causing UB and current `UNSOUND`.
- **T2 PASS:** It explicitly marks zero panic `UNPROVED`, not `CONTRACT-BROKEN`, because the disabled execution contains UB.
- **T3 PASS:** The report proposes `new(id).expect(...)`, preserves the exact public items and configuration-independent behavior, calls it a conditional proof plan rather than a verdict, and requires fresh review after implementation.
- **Hard error: none:** It avoids all enumerated hard errors.

### O

- **T1 PASS:** It gives the exact disabled-debug-assertion path from safe zero input to Rust 1.70 `new_unchecked(0)` UB and concludes current `UNSOUND`.
- **T2 PASS:** It declines `CONTRACT-BROKEN` because the branch is undefined rather than a defined execution violating only the postcondition.
- **T3 PASS:** It supplies `new(id).expect(...)`, establishes both documented branches and profile/target independence while preserving the signature, and explicitly withholds `PROVED` until implementation and audit.
- **Hard error: none:** No proposal laundering, defined post-UB counterexample, or wrong exact-version conclusion appears.

## Ambiguities

No authority ambiguity changes a score. The Rust 1.70 propositions material to T1–T3 are supported by the exact-version standard-library pages the reports cite; the additional Rust 1.97.1 continuity statements in C and L agree with the exact-version [`debug_assert!`](https://doc.rust-lang.org/1.97.1/std/macro.debug_assert.html), [`NonZero::new_unchecked`](https://doc.rust-lang.org/1.97.1/std/num/struct.NonZero.html#method.new_unchecked), and [`Option::expect`](https://doc.rust-lang.org/1.97.1/std/option/enum.Option.html#method.expect) documentation and do not produce an incorrect exact-version result.

Two wording questions were resolved directly by the scorer instructions rather than by guessing:

1. T3 names `new(id).expect(...)`, while A, D, and J use `new` plus an exhaustive `match` whose `None` arm calls `panic!`. This is the same checked construction and explicit case proof, so it passes under the instruction that equivalent explicit reasoning passes.
2. D says the panic promise is “not met,” which alone could suggest a behavioral counterexample. Its immediately following statement says the witness has UB and expressly refuses a non-UB `CONTRACT-BROKEN` verdict. Read as a whole, D leaves the promise unestablished and therefore passes T2 and the hard-error check.
