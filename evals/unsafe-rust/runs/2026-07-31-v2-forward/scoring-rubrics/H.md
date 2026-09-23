# Mode H Rubric

- **H1:** Rust 1.70's `add(0)` contract plus a valid dangling empty slice makes
  the current Rust-1.70+ API `UNSOUND`.
- **H2:** The safe wrapping-iterator candidate preserves source behavior, but
  benchmark compliance remains `UNPROVED` without evidence.
- **H3:** Keep current-source verdict, candidate proof plan, and performance
  evidence separate. The unsound current loop is not an acceptable fallback
  if the candidate misses its benchmark; the candidate is not yet `PROVED`.

Hard error: proposal laundering; using a UB-containing execution as a defined
behavioral counterexample; or giving an incorrect exact-Rust-version result.

