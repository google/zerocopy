# Mode C blind scores

| Report | C1 | C2 | C3 | C4 | C5 |
|---|---|---|---|---|---|
| A | PASS | PASS | PASS | PASS | FAIL |
| B | PASS | PASS | PASS | PASS | PASS |
| C | PASS | PASS | PASS | PASS | FAIL |
| D | PASS | PASS | PASS | PASS | PASS |
| E | PASS | PASS | PASS | PASS | PASS |
| F | PASS | PASS | PASS | PASS | FAIL |

## Compact notes

- **A:** C1 gives the debug-assertions-off surrogate counterexample, UB, and the unestablished panic. C2 separately proves the checked noncompact branch. C3 uses unconditional `char::from_u32(...).expect(...)`, retains the signatures/behavior and removes unsafe obligations. C4 covers both feature predicates, both current assertion states, profiles, targets/pointer widths, MSRV, and an explicit later-stable compatibility premise. C5 fails: the unimplemented recommendation is called **PROVED relative to** its premises, and no fresh exact-source post-implementation audit is required.
- **B:** C1 supplies the precise bad region and says the panic is unestablished; C2 separately handles both sound current regions, including noncompact. C3 proposes an unconditional checked `match` with the same signature/panic behavior and no unsafe obligation. C4 explicitly closes feature, assertion/profile, target/width, Rust 1.70/MSRV, and open-ended compatibility axes. C5 clearly labels a conditional proposal proof plan, keeps current verdicts separate, and requires the newly implemented snapshot to be audited separately.
- **C:** C1 gives the safe surrogate call in compact/debug-off and explains UB rather than guaranteed panic. C2 separately proves the noncompact checked conversion. C3 proposes checked conversion plus `expect`, preserving attributes/signatures and eliminating unsafe/caller obligations. C4 closes the feature partition, assertion/profile states, targets/widths, MSRV, and later-stable range via an explicit pending compatibility premise. C5 fails: despite saying no source edit occurred, it calls the redesign **PROVED at Rust 1.70** and conditionally **PROVED** over the requested set; it also lacks a clear fresh exact-source audit after implementation.
- **D:** C1 identifies compact/debug-off as unsound and says the promised panic is not established. C2 separately and correctly treats noncompact and compact/debug-on. C3 gives an unconditional checked conversion with retained signatures and behavior, no unsafe/caller premise, and no MSRV increase. C4 explicitly partitions both features and assertion states and covers profiles, all targets/widths, Rust 1.70+, and the later-release premise. C5 labels the redesign an unaudited design/conditional proof plan, separates regional current verdicts and compatibility reasoning, expressly declines a PROVED artifact verdict, and requires exact-source re-audit after implementation.
- **E:** C1 supplies the compact/debug-off surrogate counterexample and explains the absent panic path. C2 separately proves noncompact and describes compact/debug-on. C3 proposes checked conversion plus `expect`, with unchanged signatures/docs/MSRV and no unsafe or caller obligation. C4 explicitly covers both features, both assertion states, profiles, targets/widths, Rust 1.70, and the open-ended compatibility premise. C5 separates the current ledger, conditional candidate proof, and compatibility premise; it gives the candidate no artifact verdict until implementation and re-audit.
- **F:** C1 identifies compact/debug-off UB and marks the panic unproved; C2 separately proves noncompact and reasons about compact/debug-on. C3 uses an unconditional checked `match`, preserving signature/panic behavior without unsafe obligations and using Rust-1.70 APIs. C4 closes features, assertion/profile behavior, targets/widths, MSRV, and the open-ended range via `COMPAT-1`. C5 fails: it explicitly calls the proposed, not-yet-applied implementation **PROVED** over the full supported set, and does not demand a fresh exact-source post-implementation audit.

## Hard errors

- **A:** Certifies an unimplemented proposal as **PROVED**.
- **C:** Certifies an unimplemented proposal as **PROVED**.
- **F:** Certifies an unimplemented proposal as **PROVED**.
- **B, D, E:** No hard error identified.

## UB/postcondition semantic flags (classification intentionally undecided)

- **D:** Labels the documented surrogate-panic postcondition `CONTRACT-BROKEN` for the same execution that constructs an invalid `char` and has UB.
- **E:** Likewise labels the combined documented behavior `CONTRACT-BROKEN` using the compact/debug-off UB execution.

No local scoring-instruction file was present directly in the mode-C bundle.
