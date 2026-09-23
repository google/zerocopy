# Mode C adjudication

## Result

The sole disputed cell, **J/C1, is FAIL**. Every other atom and every hard-error decision is preserved from the scorers' agreement.

J expressly establishes a supported compact build with debug assertions disabled in which safe `decode(0xD800)` produces an invalid surrogate `char` and reaches UB. It also calls the existing implementation `UNSOUND over the published support set`. But C1 additionally requires the compact surrogate-panic promise to be only `UNPROVED` from that UB-containing execution. J never states that disposition and never explicitly gives the permitted equivalent reasoning that the UB execution cannot be used as a defined failure-to-panic counterexample. Its only documented-behavior verdict for the compact branch is regional: with debug assertions enabled, the implementation and documented behavior are `PROVED`. The later statement that no safety proof can be reconstructed for the failing branch addresses the unchecked conversion's safety precondition, not the panic postcondition.

That missing material proposition cannot be supplied from Rust authority or inferred from the report's partition. Exact Rust documentation could verify the premise that the execution has UB, but it cannot add J's omitted behavior-status derivation. This is therefore an atom failure, not the separate hard error for affirmatively using UB as a defined behavioral counterexample; J does not make that affirmative misuse.

## Final atom table

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
| J | **FAIL** | PASS | FAIL | Proposal laundering |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | FAIL | Proposal laundering |
| M | PASS | PASS | PASS | None |
| N | PASS | PASS | PASS | None |
| O | PASS | PASS | FAIL | Proposal laundering |

Totals: C1 14/15 PASS; C2 15/15 PASS; C3 10/15 PASS. Five reports have a hard error.

## Report-by-report evidence

### A

- **C1 PASS:** A gives the Rust 1.70 compact/optimized `decode(0xD800)` invalid-`char` UB witness, calls the result `UNSOUND`, and explicitly calls the compact postcondition `UNPROVED` because that execution reaches UB.
- **C2 PASS:** It separately derives the noncompact scalar-or-`None` behavior directly from checked `char::from_u32`.
- **C3 PASS:** Its checked `from_u32(...).expect(...)` candidate preserves both signatures, behavior, cfg partition, MSRV, targets, widths, and profiles, and it explicitly withholds a `PROVED` artifact verdict.
- **Hard error: None:** A distinguishes UB from a defined behavioral counterexample, does not prove an unimplemented artifact, and conditions post-1.70 claims rather than back-projecting exact-version authority.

### B

- **C1 PASS:** B supplies the disabled-assertion surrogate UB witness and expressly says the UB witness proves `UNSOUND` but leaves compact behavior `UNPROVED`, not `CONTRACT-BROKEN`.
- **C2 PASS:** It separately establishes the checked noncompact branch's exact `Some`/`None` behavior.
- **C3 PASS:** The checked candidate closes signatures, behavior, feature, target, width, profile, panic-strategy, and MSRV obligations while denying it a post-change `PROVED` verdict.
- **Hard error: None:** Its proposal/artifact and UB/defined-behavior distinctions are explicit, and later-version coverage is left conditional.

### C

- **C1 PASS:** C derives UB for compact `decode(0xD800)` without debug assertions, assigns `UNSOUND`, and explicitly labels the panic promise `UNPROVED`, not `CONTRACT-BROKEN`.
- **C2 PASS:** It separately calls the direct checked noncompact branch `PROVED` at Rust 1.70.
- **C3 PASS:** The checked/`expect` design preserves all requested surfaces and axes, and C says it is not a post-change `PROVED` verdict.
- **Hard error: None:** No laundering occurs; the associated `from_u32` availability-by-1.52 statement is compatible with its cited Rust 1.70 API page.

### D

- **C1 PASS:** D supplies the disabled-debug-assertion witness, value-preserving cast, invalid-`char` UB rule, `UNSOUND` result, and explicit `UNPROVED` rather than `CONTRACT-BROKEN` behavior disposition.
- **C2 PASS:** It derives the noncompact branch's soundness and documented result from checked conversion.
- **C3 PASS:** Its checked/`expect` proposal preserves both signatures and all support axes and is expressly not given a post-change `PROVED` verdict.
- **Hard error: None:** D neither treats UB as defined behavior nor launders the proposal, and its future claim is explicitly conditional.

### E

- **C1 PASS:** E derives the Rust 1.70 release-profile UB witness and explicitly calls the compact postcondition `UNPROVED`, not `CONTRACT-BROKEN`.
- **C2 PASS:** It separately establishes the safe noncompact checked conversion's documented behavior.
- **C3 PASS:** The checked candidate preserves the complete configuration set and surfaces, with `PROVED` withheld until implementation and audit.
- **Hard error: None:** The report avoids both laundering forms and makes later semantics conditional; its 1.52 availability statement is not an incorrect exact-version result.

### F

- **C1 PASS:** F proves disabled-assertion surrogate UB and says it prevents establishment of the promised compact panic.
- **C2 PASS:** It separately derives the noncompact checked branch's soundness and behavior.
- **C3 FAIL:** Despite no source edit, F states `Proposed redesign verdict: PROVED at Rust 1.70.0` and conditionally `PROVED` later.
- **Hard error: Proposal laundering:** That explicit verdict launders an unimplemented candidate. F does not also use UB as a defined behavior counterexample or give an incorrect exact-version result.

### G

- **C1 PASS:** G gives the supported UB witness and `UNSOUND`, calls full-set behavior `UNPROVED`, and expressly rejects a separate defined `CONTRACT-BROKEN` finding.
- **C2 PASS:** Its table separately proves the noncompact checked behavior at Rust 1.70.
- **C3 PASS:** The checked `match` plan preserves the required surfaces and axes and is explicitly a design proof plan, not an implemented-snapshot verdict.
- **Hard error: None:** No proposal, behavior, or exact-version laundering occurs.

### H

- **C1 PASS:** H completely derives compact disabled-assertion UB and explicitly says the universal panic claim is `UNPROVED` because the execution has UB.
- **C2 PASS:** It separately proves the noncompact direct checked conversion.
- **C3 FAIL:** H says `Redesign verdict: PROVED` on Rust 1.70 although it also says no source edit was requested.
- **Hard error: Proposal laundering:** The unimplemented redesign receives a forbidden verdict; no additional hard-error category applies.

### I

- **C1 PASS:** I supplies the safe surrogate UB witness, `UNSOUND`, and explicit `UNPROVED`, not `CONTRACT-BROKEN`, treatment of the compact panic promise.
- **C2 PASS:** It separately derives the noncompact branch's represented-scalar/`None` behavior.
- **C3 PASS:** The checked candidate preserves all requested signatures and configurations, and I says the unimplemented design receives no artifact verdict.
- **Hard error: None:** The immaterial off-by-one source-line reference is not an exact-version result, and neither laundering form appears.

### J

- **C1 FAIL (adjudicated):** J establishes the compact/no-debug-assertions safe-call UB witness and calls the implementation `UNSOUND`, but omits the required `UNPROVED` disposition for the compact panic promise and any explicit equivalent UB-versus-defined-behavior reasoning. Regional proof of behavior with debug assertions enabled does not fill that omission.
- **C2 PASS:** J separately says the noncompact `char::from_u32` branch is `PROVED` at Rust 1.70 and states its checked result behavior.
- **C3 FAIL:** J labels the displayed but unimplemented candidate `Redesigned implementation: PROVED for Rust 1.70`.
- **Hard error: Proposal laundering:** That candidate verdict is proposal laundering. J does not affirmatively use the UB execution as a defined behavioral counterexample, and its exact-version API statements are not erroneous.

### K

- **C1 PASS:** K gives the disabled-assertion surrogate UB witness and explicitly assigns `UNPROVED`, with no separate `CONTRACT-BROKEN` verdict.
- **C2 PASS:** It separately proves the noncompact checked scalar/`None` behavior.
- **C3 PASS:** Its checked/`expect` plan preserves the complete support set and surfaces and explicitly has no `PROVED` verdict before implementation and audit.
- **Hard error: None:** K avoids both laundering forms and makes later-version coverage conditional.

### L

- **C1 PASS:** L derives compact release-profile UB and says the panic guarantee is not established, with no separate defined-execution counterexample.
- **C2 PASS:** It separately derives the noncompact checked behavior.
- **C3 FAIL:** Its code is headed `proposal only`, yet it calls the proposed redesign `PROVED for Rust 1.70.0` and conditionally `PROVED` for 1.70+.
- **Hard error: Proposal laundering:** The proposal-only/`PROVED` combination triggers the hard error. Its stated 1.97.1 endpoint and explicit compatibility premise add no exact-version hard error.

### M

- **C1 PASS:** M gives every step of the disabled-assertion surrogate UB witness and explicitly assigns `UNPROVED` to documented behavior, with no UB-free `CONTRACT-BROKEN` case.
- **C2 PASS:** It separately establishes the noncompact checked conversion's soundness and behavior.
- **C3 PASS:** The checked candidate preserves all surfaces and axes, and M withholds a post-change `PROVED` verdict.
- **Hard error: None:** Current claims are exact-versioned, later coverage is conditional, and neither laundering form occurs.

### N

- **C1 PASS:** N supplies the disabled-debug-assertion UB witness and explicitly says the panic cannot be proved and is not a defined `CONTRACT-BROKEN` counterexample.
- **C2 PASS:** It separately proves the noncompact checked branch's precise behavior.
- **C3 PASS:** The checked/`unwrap` candidate preserves the requested support set and surfaces, with no post-change `PROVED` verdict before implementation and review.
- **Hard error: None:** N avoids proposal laundering, UB-path laundering, and incorrect exact-version claims.

### O

- **C1 PASS:** O gives the compact disabled-assertion UB witness, `UNSOUND`, and explicit `UNPROVED` behavior because UB occurs rather than a proved panic.
- **C2 PASS:** It separately proves the noncompact checked branch at Rust 1.70.
- **C3 FAIL:** Although no source was edited, O declares `Proposed implementation — PROVED at Rust 1.70` and conditionally `PROVED` later.
- **Hard error: Proposal laundering:** The proposed-yet-`PROVED` verdict triggers the hard error; O does not commit either other hard-error category.

## Ambiguity

No genuine rubric or Rust-authority ambiguity changes a score. J presents a scoring boundary: its exhaustive configuration discussion gives a reader facts from which the missing `UNPROVED` conclusion could be derived. But the frozen instructions resolve that boundary: equivalent reasoning must be explicit, and a material premise may not be inferred from silence. Conversely, omission alone is not the hard error for using UB as a defined behavioral counterexample; that hard error requires affirmative misuse, which J does not make.
