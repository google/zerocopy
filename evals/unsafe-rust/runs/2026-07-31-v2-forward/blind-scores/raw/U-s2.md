# Mode U blind score

I scored each report against the three atoms in `RUBRIC.md`. “No hard error” means the report neither calls the API sound, uses the zero-input UB execution as a behavioral counterexample, asserts guaranteed observations around that UB, nor conflates/omits the independent input-one refutation.

| Report | U1 | U2 | U3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | None |
| D | PASS | **FAIL** | PASS | **YES — zero-path behavioral refutation** |
| E | PASS | PASS | PASS | None |
| F | PASS | PASS | PASS | None |
| G | PASS | PASS | PASS | None |
| H | PASS | PASS | PASS | None |
| I | PASS | PASS | PASS | None |
| J | PASS | PASS | PASS | None |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | None |
| M | PASS | PASS | PASS | None |
| N | PASS | PASS | PASS | None |
| O | PASS | PASS | PASS | None |

Atom totals: A–C and E–O score 3/3; D scores 2/3 and has one applicable hard error.

## Report-by-report evidence

### A

- **U1 PASS:** It derives that the literal `0` arm is selected, quotes the exact Rust 1.80.0 `unreachable_unchecked` rule, and concludes that the valid safe call `classify(0)` is UB and the API is `UNSOUND`.
- **U2 PASS:** It says the zero-input panic promise is “not established” and that “UB cannot supply a guaranteed panic outcome”; its `CONTRACT-BROKEN` verdict is explicitly based independently on input one.
- **U3 PASS:** It separately derives that `classify(1)` normally returns `2`, states `2 != 1`, and calls this a defined counterexample.
- **Hard error: none.** It makes no defined behavioral observation from the zero-input UB execution and does not conflate it with the input-one refutation.

### B

- **U1 PASS:** S-1 follows the valid input `0` through the matching arm to the exact-versioned UB contract and concludes `UNSOUND`.
- **U2 PASS:** B-1 says the zero path supplies no defined panic and that the promised panic is “not established”; the report does not use that path as its contract-breaking witness.
- **U3 PASS:** B-2 independently follows input `1` to a normal result of `2 != 1` and labels it `CONTRACT-BROKEN`.
- **Hard error: none.** The aggregate behavioral verdict is grounded in B-2, while B-1 remains an absence of proof/guarantee.

### C

- **U1 PASS:** S1 identifies the unrestricted safe zero call, reaches `unreachable_unchecked`, applies its Rust 1.80.0 contract, and concludes `UNSOUND`.
- **U2 PASS:** D1 expressly labels the zero panic clause `UNPROVED` and says UB can establish neither a defined panic nor a UB-free behavioral counterexample.
- **U3 PASS:** D2 expressly identifies `classify(1)` as a separate UB-free normal return of `2`, refuting the identity postcondition.
- **Hard error: none.** It cleanly separates the zero soundness witness from the one behavioral witness.

### D

- **U1 PASS:** It correctly derives that safe `classify(0)` selects the zero arm, reaches `unreachable_unchecked`, and is UB/`UNSOUND` under the exact 1.80.0 contract.
- **U2 FAIL:** It does not leave the panic clause unproved. It says “Both documented clauses fail,” says zero reaches UB “rather than providing the promised panic,” and labels F-01 at line 8 both `UNSOUND` and `CONTRACT-BROKEN`.
- **U3 PASS:** Independently, it correctly derives that `classify(1)` is defined, returns `2`, and refutes the normal-return clause.
- **Hard error: YES.** The explicit behavioral-failure/`CONTRACT-BROKEN` conclusion from the zero-input UB execution is the rubric’s prohibited use of that execution as a behavioral refutation. It does not miss the independent input-one finding, and it makes no separate claim that a post-UB runtime manifestation is guaranteed.

### E

- **U1 PASS:** O-SOUND gives the valid safe zero witness, exact match reasoning, and the exact Rust 1.80.0 UB contract.
- **U2 PASS:** O-PANIC explicitly labels the clause `UNPROVED` and states that the UB execution cannot witness `CONTRACT-BROKEN`.
- **U3 PASS:** O-IDENTITY uses the independent, UB-free `classify(1)` execution returning `2 != 1`.
- **Hard error: none.** All three dispositions are explicitly separated.

### F

- **U1 PASS:** F1 identifies the safe zero call, the reached unsafe operation, and the exact 1.80.0 rule that reaching it is UB, yielding `UNSOUND`.
- **U2 PASS:** Although it uses “not upheld,” it immediately gives the controlling proposition: Rust supplies “no guaranteed panic outcome,” and B1 is “subsumed by S1.” Read as a proposition rather than a preferred label, this leaves the panic guarantee unestablished rather than supplying a defined non-panic witness.
- **U3 PASS:** F2 explicitly uses input `1` as an independent defined path returning `2`, and bases `CONTRACT-BROKEN` on it.
- **Hard error: none.** It does not claim an observed result for zero or use zero as the independent behavioral counterexample.

### G

- **U1 PASS:** S1/U1 follow safe input zero to the reached call and the exact-versioned UB rule, concluding `UNSOUND`.
- **U2 PASS:** B1 says the zero arm establishes no defined outcome and the panic promise is “not proved”; it classifies the case only as already `UNSOUND`.
- **U3 PASS:** B2 independently derives a defined normal return of `2` for input `1` and `CONTRACT-BROKEN`.
- **Hard error: none.** The report explicitly keeps the two witnesses distinct.

### H

- **U1 PASS:** F1 uses the Rust 1.80.0 literal/match rules and `unreachable_unchecked` contract to prove the valid safe zero call reaches UB.
- **U2 PASS:** It says the zero panic promise “is not established” and that UB supplies no defined panic behavior; it does not call that a UB-free contract counterexample.
- **U3 PASS:** F2 independently uses input one, avoids the unsafe arm, and derives the normal result `2 != 1`.
- **Hard error: none.** Its behavioral `CONTRACT-BROKEN` verdict is expressly tied to input one.

### I

- **U1 PASS:** It partitions the input domain, follows zero into `unreachable_unchecked`, quotes the exact Rust 1.80.0 UB contract, and concludes `UNSOUND`.
- **U2 PASS:** It says the separate zero panic promise is “not established” because that path is UB rather than a defined panic.
- **U3 PASS:** It independently identifies the input-one arm as a defined normal return of `2 != input`.
- **Hard error: none.** No defined zero-input behavioral observation is asserted, and the report does not conflate the witnesses.

### J

- **U1 PASS:** It derives that valid safe input zero selects the unsafe arm and violates the exact 1.80.0 callee contract, producing UB.
- **U2 PASS:** It says zero “does not establish” the promised Rust-defined panic and that after UB no behavior is guaranteed; it treats this as the soundness finding, not the contract-breaking witness.
- **U3 PASS:** It uses the separate defined call `classify(1)` returning `2` as the postcondition counterexample.
- **Hard error: none.** Its table and prose keep “No guaranteed panic” distinct from `CONTRACT-BROKEN` on input one.

### K

- **U1 PASS:** Its exhaustive derivation takes the valid zero input to `unreachable_unchecked` and applies the exact-versioned UB axiom, proving `UNSOUND`.
- **U2 PASS:** It expressly labels the zero panic clause `UNPROVED` and says the UB execution cannot serve as the UB-free witness required for `CONTRACT-BROKEN`.
- **U3 PASS:** It expressly identifies `classify(1)` as an independent UB-free normal return of `2 != 1`.
- **Hard error: none.** It states the rubric’s required separation directly.

### L

- **U1 PASS:** S1 follows safe input zero to the reached call and quotes the exact Rust 1.80.0 rule that this is UB, yielding `UNSOUND`.
- **U2 PASS:** B1 says the UB rule “supplies UB, not a panic postcondition,” that backend behavior cannot establish the source guarantee, and that “no panic guarantee is established.” That is an equivalent `UNPROVED` treatment, despite the row also carrying the soundness label.
- **U3 PASS:** B2 separately uses input one, states that it executes no unsafe operation, and derives a normal result of `2 != 1` and `CONTRACT-BROKEN`.
- **Hard error: none.** It does not turn the zero path into the behavioral refutation.

### M

- **U1 PASS:** S1/U1 use exact-versioned literal/match and `unreachable_unchecked` premises to show that valid safe input zero reaches UB and refutes soundness.
- **U2 PASS:** The controlling claim in the verdict is that the zero panic promise “is not established as defined Rust behavior.” The table’s “not satisfied as a defined source behavior” is read in that stated epistemic sense: there is no defined panic path/guarantee, not an asserted UB-free non-panic outcome.
- **U3 PASS:** B2 is explicitly “refuted without UB” by the independent normal return `classify(1) == 2`.
- **Hard error: none.** In full context, `CONTRACT-BROKEN` is grounded only in input one, and no zero-input runtime observation is claimed.

### N

- **U1 PASS:** S1 follows the safe zero call through the exact match rules to the exact Rust 1.80.0 UB contract and concludes `UNSOUND`.
- **U2 PASS:** B1 expressly labels the clause `UNPROVED` and says the UB execution supplies neither a panic nor a UB-free `CONTRACT-BROKEN` witness.
- **U3 PASS:** B2 expressly uses the independent UB-free input-one execution returning normally with `2 != 1`.
- **Hard error: none.** The report directly observes the whole-execution restriction.

### O

- **U1 PASS:** S1 uses valid zero, exact-versioned pattern/match rules, and the exact 1.80.0 unsafe-function contract to derive UB and `UNSOUND`.
- **U2 PASS:** The verdict and B2 expressly label the zero panic promise `UNPROVED` and say the UB execution cannot prove a UB-free behavioral refutation.
- **U3 PASS:** B1 independently derives the UB-free input-one normal return of `2 != 1` and `CONTRACT-BROKEN`.
- **Hard error: none.** The witness separation is explicit despite the report’s local B1/B2 identifier ordering.

## Ambiguity

No rubric ambiguity changes an atom or hard-error decision. Two reports use potentially sharp shorthand: F says the zero promise is “not upheld,” and M says it is “not satisfied as a defined source behavior.” Their surrounding text explicitly says the panic is not established/guaranteed and grounds `CONTRACT-BROKEN` independently in input one. Under `SCORER.md`’s instruction to score propositions rather than preferred vocabulary, both are equivalent to `UNPROVED`. D is materially different because it expressly says the zero clause *fails* and assigns `CONTRACT-BROKEN` to the line-8 UB finding.

All material authority used for the UB finding is version-matched: every report invokes the Rust/core 1.80.0 `unreachable_unchecked` contract. I treated the reports’ explicit evaluation of the literal arms and direct return expressions as source derivation, not as an unverified version-backprojection; none relies on later documentation, project policy, tests, CI, or implementation behavior.
