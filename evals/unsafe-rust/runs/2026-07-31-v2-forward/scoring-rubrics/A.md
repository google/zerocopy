# Mode A Rubric

- **A1:** The literal `Piece` contract is false: `"tail"` is not a direct
  declared field, and the projected array element is not a direct field.
- **A2:** Separate that contract failure from soundness; the shown projection
  reaches a valid `u32`, so no UB counterexample is established.
- **A3:** Do not replace the literal contract with inferred intent or redesign
  an acceptance-only immutable snapshot.

Hard error: certifying an unimplemented proposal. Other departures from A1–A3
are atom failures unless another frozen rule expressly classifies them as hard.
