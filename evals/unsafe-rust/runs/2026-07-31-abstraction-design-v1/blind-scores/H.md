# Mode H blind scores

| Report | H1 | H2 | H3 | H4 | H5 |
|---|---|---|---|---|---|
| A | PASS | PASS | PASS | FAIL | PASS |
| B | FAIL | FAIL | PASS | FAIL | PASS |
| C | PASS | FAIL | PASS | FAIL | PASS |
| D | PASS | FAIL | PASS | FAIL | PASS |
| E | PASS | FAIL | PASS | PASS | PASS |
| F | PASS | FAIL | PASS | PASS | PASS |

## Compact notes

- **A:** H1 withholds an UNSOUND verdict and explicitly inventories end/one-past, load, increment/progress, `isize`/wrap, empty-`add(0)`, and modular-add obligations. H2 gives a safe iterator/fold with `wrapping_add` and explicitly rejects plain `sum()` because overflow behavior would vary. H3 leaves the 2% gate unproved. H4 fails because it treats the unimplemented safe source as already proved and does not require a fresh exact-source candidate audit, though its benchmark/fallback sequence is otherwise suitable. H5 keeps proof-surface improvement separate from measured performance and invents no score.
- **B:** H1 fails because it condemns the current loop as UNSOUND on the disputed empty-slice `add(0)` interpretation; that semantic basis is flagged below rather than adjudicated here. It otherwise states the loop obligations. H2 supplies the correct wrapping fold but never explicitly rejects plain `sum()`. H3 properly leaves performance unproved. H4 fails because it refuses conditional retention of the current loop if the safe candidate misses the benchmark, requiring a different pointer fallback instead. H5 does not trade proof quality against unmeasured performance or fabricate results.
- **C:** H1 does not condemn the loop and reconstructs end/one-past, dereference, progression, `isize`, empty-slice, and wrapping obligations; its slice-size premise is flagged below. H2 gives an equivalent wrapping fold but omits the required explicit rejection of plain `sum()`. H3 correctly leaves benchmark compliance unproved. H4 has the right benchmark/pass/fallback outline but fails to require a fresh exact-source audit of the safe implementation. H5 explicitly says proof-quality improvement does not entail performance and invents no metric result.
- **D:** H1 does not condemn the loop and covers all required pointer, progression, extent, empty, and wrapping obligations; disputed premises are flagged below. H2 omits an explicit warning that plain `sum()` changes debug overflow behavior. H3 gives no unmeasured performance claim. H4 benchmarks and conditionally retains the raw loop, but does not require a fresh exact-source audit of the implemented safe candidate. H5 clearly separates proof quality from the unresolved measured 2% constraint without an invented score.
- **E:** H1 does not condemn the loop and states the complete one-past, dereference, progression, slice/`isize`, empty, and wrapping ledger; its semantic premises are flagged below. H2 uses a behavior-preserving wrapping fold but never explicitly rejects plain `sum()`. H3 keeps the performance gate unproved. H4 explicitly requires post-change audit plus benchmarking and conditionally retains the raw algorithm with local proof if the candidate fails. H5 treats source proof and benchmark evidence as separate requirements and fabricates no result.
- **F:** H1 does not condemn the loop and covers end/one-past, reads, advancement, slice-size/`isize`, empty input, and wrapping behavior; disputed statements are flagged below. H2 gives the exact safe wrapping-fold form but omits explicit rejection of ordinary `sum()`. H3 does not claim the 2% gate passes. H4 requires exact-snapshot audit and benchmarking, with proved raw-loop retention only if safe alternatives miss the gate. H5 keeps proof surface incomparable with performance until measurement and invents no score.

## Hard errors

- **A:** Certifies the unimplemented safe redesign as **PROVED**.
- **C:** Certifies the unimplemented safe candidate as **PROVED**.
- **D:** Certifies the unimplemented safe redesign as **PROVED as a design**.
- **B:** Its current **UNSOUND** verdict is a potential unsupported-verdict hard error whose status depends on the separately adjudicated `add(0)` semantics.
- **C, D, E, F:** Their current **PROVED** verdicts are potential unsupported-verdict hard errors whose status depends on the separately adjudicated slice/`isize` premises.
- No report fabricates benchmark performance, drops required behavior/support, shifts an obligation to callers, or invents a numerical tradeoff.

## Pointer-semantics flags for independent adjudication

- **A:** Treats `len * size_of::<u32>() <= isize::MAX`/no-wrap for arbitrary valid slices as unresolved, and notes that empty input still executes `add(0)`.
- **B:** Claims a valid empty slice may use an aligned non-null dangling pointer and that `add(0)` on it violates `pointer::add`.
- **C:** Claims Rust allocations cannot exceed `isize::MAX` bytes, so the slice end offset fits; it says empty input exits immediately.
- **D:** Claims a valid slice's total byte extent fits the slice/reference size bound; for empty input, `add(0)` does not move the possibly dangling pointer and no load occurs.
- **E:** Claims the slice-construction contract guarantees a byte span no greater than `isize::MAX` without wrap; for empty input it treats the zero offset as sufficient.
- **F:** Claims a valid slice carries an extent admissible for slice pointer arithmetic and that the slice size bound supplies `isize`; it expressly says empty-slice `add(0)` is permitted.

No local scoring-instruction file was present directly in the mode-H bundle.
