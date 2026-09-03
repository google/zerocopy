# Mode W Frozen Blind-Scoring Rubric

> **Evaluator-only material. Never expose this file to a report agent.**

## W — Whole-execution UB and independent behavioral refutation

Target: supplied W snapshot.

Let `C_W` be Rust 1.80.0 times every target on which this exact source and the
used Rust 1.80.0 standard-library item exist times every ordinary profile, and
let `I = {0, ..., 255}`. The claims are:

- `Required(W-sound) = C_W times I`;
- `Required(W-panic) = C_W times {0}`; and
- `Required(W-return) = C_W times I`; its theorem is: for every UB-free defined
  execution in this domain, if that execution returns normally, its result
  equals its input.

### Expected results and atoms

- **W1 — Soundness witness:** `classify(0)` is a valid safe call, takes the
  zero arm, evaluates the local statements, and reaches
  `unreachable_unchecked`. Its unreachable-site proposition is false; the
  applicable 1.80.0 std contract entails UB. Report `W-sound` **UNSOUND**.
- **W2 — Whole-execution classification:** The input-zero execution as a whole
  contains UB. Neither its apparent prefix computation nor the source-level
  fact that no panic operation appears before the unsafe call remains a
  guaranteed observation from a defined execution. It therefore cannot prove
  a UB-free failure of the panic postcondition. With no independent UB-free
  input-zero execution or equivalent proof, report `W-panic` **UNPROVED**, not
  `CONTRACT-BROKEN` and not `PROVED`. Its claim-level `Covered` set is empty on
  the submitted evidence.
- **W3 — Independent defined witness:** `classify(1)` takes the `1 => 2` arm,
  executes no unsafe operation, returns normally, and returns `2` rather than
  the promised input value `1`. That complete execution is UB-free and proves
  `W-return` **CONTRACT-BROKEN**.

Scoring guidance, not a separate atom: keep the three executions/theorems
independent. The input-zero UB witness cannot establish failure of the panic
promise, while the independent, defined input-one failure remains usable and
does not alter the soundness witness.

### W hard errors

Any of these is a hard error:

- calling the safe API sound, reporting only `UNPROVED` after explicitly
  establishing every input-zero UB-certificate link, or issuing `UNSOUND`
  without those links;
- using the UB-containing input-zero execution, an apparent observation before
  its UB, or the absence of an earlier panic to issue `CONTRACT-BROKEN`;
- claiming source observations remain guaranteed merely because they occur
  before the unsafe call;
- falsely treating the independent input-one refutation as UB-containing, or
  claiming complete behavioral coverage while omitting it.

### W checked authorities

- `https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety`
  — reaching the function is undefined behavior.
- `https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html`
  — controlling Rust 1.80.0 Reference section for what constitutes undefined
  behavior. Verify that the final evaluator instructions do not attribute to
  this page prose it does not contain; whole-execution non-observability is the
  logical consequence of classifying the execution as undefined, not a claimed
  quotation from a “time travel” subsection.
