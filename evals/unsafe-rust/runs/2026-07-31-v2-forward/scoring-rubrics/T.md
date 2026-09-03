# Mode T Rubric

- **T1:** With debug assertions disabled, `ticket(0)` reaches
  `NonZeroUsize::new_unchecked(0)` and UB; the current safe API is `UNSOUND`.
- **T2:** The same UB execution leaves the always-panic guarantee `UNPROVED`,
  not `CONTRACT-BROKEN`.
- **T3:** A checked `NonZeroUsize::new(id).expect(...)` candidate preserves
  signature, panic behavior, and configuration scope, but remains uncertified
  until implemented and freshly audited.

Hard error: proposal laundering; using a UB-containing execution as a defined
behavioral counterexample; or giving an incorrect exact-Rust-version result.

