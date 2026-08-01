# Mode C blind score

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
| J | PASS | PASS | FAIL | Proposal laundering |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | FAIL | Proposal laundering |
| M | PASS | PASS | PASS | None |
| N | PASS | PASS | PASS | None |
| O | PASS | PASS | FAIL | Proposal laundering |

Totals: C1 15/15 PASS; C2 15/15 PASS; C3 10/15 PASS. Five reports have a hard error.

## Report-by-report evidence

### A

- **C1 PASS:** A selects Rust 1.70, `compact`, an optimized build with debug assertions disabled, and safe input `0xD800`; it derives value-preserving widening, construction of an invalid surrogate `char`, and UB. It separately calls the compact panic promise `UNPROVED` because that supported execution reaches UB.
- **C2 PASS:** It says the noncompact branch is safe and behaviorally correct at Rust 1.70, then proves this directly from `char::from_u32` returning the scalar or `None`. It leaves post-1.70 extension conditional on an explicit compatibility premise.
- **C3 PASS:** Its checked `from_u32(...).expect(...)` redesign preserves both definitions and documents the `u16`/surrogate partition, cfg partition, MSRV, targets, widths, and profiles. It explicitly says the design sketch receives no `PROVED` artifact verdict before implementation.
- **Hard error: none.** The report does not turn the UB execution into a defined behavioral counterexample, does not launder the proposal, and anchors the material witness and design derivation to exact Rust 1.70 authorities while leaving later releases conditional.

### B

- **C1 PASS:** B gives the same supported safe-call witness and states that the unchecked constructor receives a surrogate when `debug_assert!` is omitted. It expressly says the panic guarantee is `UNPROVED`, not `CONTRACT-BROKEN`, under the whole-execution rule.
- **C2 PASS:** Its ledger and configuration discussion establish that the noncompact body directly has `char::from_u32`'s checked `Some`/`None` behavior and no unsafe operation, with later-version coverage explicitly unresolved absent compatibility verification.
- **C3 PASS:** The `expect` candidate keeps the compact signature and unchanged noncompact definition, proves both input cases, and closes feature, target, width, profile, panic-strategy, and Rust-1.70 availability obligations. B calls it a design proposal and denies it a post-change `PROVED` verdict.
- **Hard error: none.** It distinguishes UB from a defined postcondition failure, uses versioned Rust 1.70 documentation, qualifies later versions, and does not claim the unimplemented source is proved.

### C

- **C1 PASS:** C identifies a Rust 1.70 optimized/no-debug-assertions execution of safe `decode(0xD800)`, links invalid surrogate production to UB, and labels the compact panic promise `UNPROVED` rather than behaviorally broken.
- **C2 PASS:** It separately says the noncompact branch is `PROVED` at Rust 1.70 because its body is exactly the checked conversion, while not back-projecting that result across later releases without a compatibility premise.
- **C3 PASS:** Its `from_u32(...).expect(...)` candidate proves widening, the precise surrogate/valid partition, panic and return behavior, cfg complementarity, signatures, MSRV, and configuration independence. It expressly says this is not a post-change `PROVED` verdict.
- **Hard error: none.** No proposal or UB-path laundering occurs, and the exact-version claims are supported or appropriately conditional. The statement that the associated conversion was stable by Rust 1.52 is compatible with the versioned primitive API.

### D

- **C1 PASS:** D supplies the disabled-debug-assertion witness, the cast-preservation step, the unchecked-conversion obligation, and the Rust 1.70 invalid-`char` UB rule. It calls the compact postcondition `UNPROVED`, not `CONTRACT-BROKEN`.
- **C2 PASS:** D separately identifies the noncompact implementation as safe and exactly delegated to `char::from_u32`, whose Rust 1.70 contract supplies the documented result.
- **C3 PASS:** The checked-plus-`expect` recommendation preserves the compact signature and unchanged opposite branch; its proof covers all `u16` cases, cfg selection, targets, widths, profiles, and MSRV. D says it is a design proposal, not a post-change `PROVED` verdict.
- **Hard error: none.** Its current result is exact-versioned, its future compatibility premise is explicit, and it neither treats UB as defined behavior nor promotes the proposal to an artifact verdict.

### E

- **C1 PASS:** E derives release-profile UB from safe surrogate input using exact Rust 1.70 debug-assertion, cast, char-validity, and invalid-value rules. It explicitly labels the compact panic postcondition `UNPROVED`, not `CONTRACT-BROKEN`.
- **C2 PASS:** It separately finds the noncompact checked-conversion branch sound and behaviorally correct under the Rust 1.70 contract.
- **C3 PASS:** Its checked conversion plus `expect` preserves both functions, cfgs, return types, behavior, MSRV, and all target/profile axes. It calls the replacement counterfactual and says the sketch receives no `PROVED` verdict until implemented and audited.
- **Hard error: none.** E uses no UB-containing defined counterexample or proposal verdict. Its claim that the primitive associated `char::from_u32` is marked stable since 1.52 is an accurate availability claim, not an incorrect exact-version result; future semantics remain an explicit compatibility premise.

### F

- **C1 PASS:** F gives the supported disabled-debug-assertions surrogate witness and invalid-`char` UB derivation. Saying this prevents establishment of the panic guarantee is an `UNPROVED` treatment, not a defined-execution counterexample.
- **C2 PASS:** It separately states and derives that the unchanged noncompact checked conversion is sound and returns the represented scalar or `None`, with later releases made conditional on `COMPAT-1`.
- **C3 FAIL:** Although F's candidate and configuration proof preserve the signatures, behavior, MSRV, and full configuration axes, it declares **“Proposed redesign verdict: PROVED at Rust 1.70.0”** and `PROVED` relative to compatibility for later releases despite also saying no source edit was made. That fails C3's required non-`PROVED` disposition for an unimplemented candidate.
- **Hard error: proposal laundering.** The quoted proposed-redesign verdict is the applicable hard error. No additional hard error applies: F does not use the UB path as a defined behavioral counterexample, and its exact-version/future-version qualifications are otherwise sound.

### G

- **C1 PASS:** G states the disabled-assertions safe call, invalid surrogate construction, and current `UNSOUND` result, then correctly treats documented behavior as `UNPROVED` and expressly rejects a separate `CONTRACT-BROKEN` finding.
- **C2 PASS:** Its configuration table separately proves the noncompact branch from the exact Rust 1.70 `from_u32` contract.
- **C3 PASS:** The checked `match` returns `Some(c)` or calls `panic!`, with preserved signature, unchanged noncompact branch, Rust 1.70 API availability, and target/profile closure. G calls this only a design proof plan and explicitly says it is not a verdict on an implemented snapshot.
- **Hard error: none.** It avoids both forbidden kinds of laundering and conditions later-release claims instead of giving an incorrect exact-version result.

### H

- **C1 PASS:** H gives a complete exact-Rust-1.70 UB witness for `decode(0xD800)` when debug assertions are disabled and says the compact panic result is consequently `UNPROVED`.
- **C2 PASS:** It separately marks the noncompact branch `PROVED` relative to Rust 1.70 and explains that the direct checked conversion is exactly the documented behavior.
- **C3 FAIL:** The safe `match` design itself preserves the required signatures, behavior, MSRV, cfg partition, and all support axes, but H states **“Redesign verdict: PROVED on Rust 1.70”** even though it says no source edit was requested. The required candidate disposition is therefore missing.
- **Hard error: proposal laundering.** Calling this unimplemented redesign `PROVED` is a hard error. There is no separate UB-counterexample or exact-version hard error; the associated `from_u32` stability-by-1.52 claim is accurate, and later coverage is expressly conditional.

### I

- **C1 PASS:** I identifies the safe surrogate witness in an ordinary Rust 1.70 release build, proves widening preserves it, and connects invalid `char` production to UB. It explicitly gives `UNPROVED`, not `CONTRACT-BROKEN`, for the compact panic promise.
- **C2 PASS:** Its configuration partition separately establishes the noncompact safe conversion's exact scalar-or-`None` behavior at Rust 1.70.
- **C3 PASS:** The checked-plus-`expect` recommendation proves both compact cases and preserves the feature-specific signatures, behavior, MSRV, targets, widths, and profiles. I labels it “not implemented” and says it receives no artifact verdict.
- **Hard error: none.** The off-by-one reference to `lib.rs:8` does not alter the identified unsafe expression or any material proposition. There is no laundering or incorrect exact-version result.

### J

- **C1 PASS:** J correctly partitions the compact branch, proves UB for safe `0xD800` with disabled debug assertions, and does not claim a defined behavioral counterexample from that execution.
- **C2 PASS:** It separately establishes the noncompact branch at Rust 1.70 from the checked-conversion contract.
- **C3 FAIL:** Its safe checked `match` preserves the two signatures, behavior, cfg partition, MSRV, and configuration axes, but J labels the **“Redesigned implementation: PROVED for Rust 1.70”** even though the report merely presents redesign source and no implementation snapshot exists. Conditional treatment of later releases does not cure that artifact-status error.
- **Hard error: proposal laundering.** The `PROVED` label on the unimplemented redesign is the hard error. J's current UB reasoning and exact-version API statements are otherwise correct; the primitive associated method's 1.52 stability annotation is not erroneous.

### K

- **C1 PASS:** K supplies the supported safe-input UB witness and separately says the compact panic guarantee is `UNPROVED`, with no `CONTRACT-BROKEN` verdict from the UB path.
- **C2 PASS:** Its table proves the noncompact branch's soundness and exact checked scalar/`None` behavior under the cited Rust 1.70 authority.
- **C3 PASS:** The `expect` recommendation proves the surrogate partition and preserves both cfg-selected signatures, documentation, MSRV, targets, widths, and profiles. K explicitly says the design has no `PROVED` verdict until implemented and audited.
- **Hard error: none.** It neither launders a proposal nor a UB execution, and its post-1.70 coverage remains an explicit compatibility condition.

### L

- **C1 PASS:** L gives the Rust 1.70 optimized/no-debug-assertions surrogate witness and the invalid-value UB derivation, without treating that path as a defined failure to panic.
- **C2 PASS:** It independently says the noncompact branch is proved and derives its documented result directly from `char::from_u32`, with version coverage qualified.
- **C3 FAIL:** L's safe `match` preserves signatures, cfgs, outcomes, MSRV, and all support axes, but its headline says **“Proposed redesign: PROVED for Rust 1.70.0”** and conditionally `PROVED` for 1.70+, while the code section itself is labeled **“proposal only.”** This directly violates the unimplemented-candidate clause.
- **Hard error: proposal laundering.** The proposal-only/`PROVED` combination is the hard error. No additional exact-version error applies: Rust 1.97.1 is a valid versioned documentation endpoint at the stated cutoff, and the intervening/open-ended proposition is explicitly placed in `TCB-COMPAT-1`.

### M

- **C1 PASS:** M gives all steps of the Rust 1.70 disabled-assertions safe surrogate UB witness and correctly assigns `UNPROVED` to the compact behavior rather than using UB as a behavioral counterexample.
- **C2 PASS:** Its configuration disposition separately states and supports that the noncompact checked conversion is sound and has the documented behavior.
- **C3 PASS:** The checked-plus-`expect` candidate proves all `u16` cases and keeps cfg, signatures, MSRV, behavior, and target/profile support intact. M explicitly says there is no post-change `PROVED` verdict until implementation and review.
- **Hard error: none.** Current claims are exact-Rust-1.70 based, later compatibility is unresolved or assumed explicitly, and neither forbidden laundering form occurs.

### N

- **C1 PASS:** N supplies the exact Rust 1.70 disabled-debug-assertions witness, invalid surrogate production, and UB conclusion. It explicitly says `CONTRACT-BROKEN` is not warranted because no defined non-panicking execution was established.
- **C2 PASS:** It separately proves the noncompact checked conversion returns exactly `Some(scalar)` or `None` and contains no unsafe operation.
- **C3 PASS:** The checked `from_u32(...).unwrap()` redesign has the same required panic/return split and preserves both cfg-specific signatures, MSRV, behavior, and all configuration axes. N calls it counterfactual and withholds a post-change `PROVED` verdict pending implementation and review.
- **Hard error: none.** It uses neither proposal laundering nor a UB-containing behavioral counterexample, and it appropriately requires per-version checking or an explicit compatibility premise after Rust 1.70.

### O

- **C1 PASS:** O gives the supported disabled-assertions surrogate witness, proves invalid-`char` UB, and calls current documented behavior `UNPROVED` rather than a defined failure.
- **C2 PASS:** It separately proves the unchanged noncompact branch at Rust 1.70 from `char::from_u32` and includes it in the candidate closure.
- **C3 FAIL:** O's checked-plus-`expect` design preserves both signatures, behavior, MSRV, feature selection, and all support axes, but it declares **“Proposed implementation — PROVED at Rust 1.70”** after expressly saying **“No source was edited.”** That fails the required unimplemented-candidate status.
- **Hard error: proposal laundering.** The proposed-yet-`PROVED` verdict is the hard error. O does not commit the UB-behavioral-counterexample error, and its later-version result is explicitly conditional rather than incorrectly back-projected.

## Rubric and authority ambiguities

No genuine ambiguity changes a score.

- The rubric is explicit that an unimplemented candidate is not `PROVED` and separately names proposal laundering as a hard error. Thus the `PROVED` labels in F, H, J, L, and O cannot be treated merely as harmless shorthand for a proof plan, especially where those reports expressly acknowledge that the source was not edited or is “proposal only.”
- Exact Rust 1.70 authorities suffice for the current `UNSOUND` witness because 1.70 is inside the support set. Reports that leave later-release behavioral coverage conditional on an explicit compatibility premise appropriately leave that proposition unresolved under `SCORER.md`; this does not fail C1 or C2.
- The [Rust 1.70 primitive associated function `char::from_u32`](https://doc.rust-lang.org/1.70.0/std/primitive.char.html#method.from_u32) has the 1.52.0 stability annotation, so the stability wording in C, E, H, and J is not an incorrect exact-version result. [Rust 1.97.1 official documentation](https://doc.rust-lang.org/1.97.1/std/primitive.char.html#method.from_u32) is also a valid versioned endpoint at L's stated cutoff.
