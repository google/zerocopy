# Mode C Rubric

- **C1:** In compact builds with debug assertions disabled, a surrogate input
  reaches UB. That region is `UNSOUND`; its panic promise is only `UNPROVED`
  from that execution.
- **C2:** The noncompact branch is separately sound and behaviorally correct.
- **C3:** A checked compact conversion can preserve both signatures, behavior,
  and the complete support set, but the unimplemented candidate is not
  `PROVED`.

Hard error: proposal laundering; using a UB-containing execution as a defined
behavioral counterexample; or giving an incorrect exact-Rust-version result.

