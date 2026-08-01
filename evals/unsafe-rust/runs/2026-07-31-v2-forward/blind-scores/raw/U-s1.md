# Mode U blind score

## Atom table

| Report | U1 | U2 | U3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | None |
| D | PASS | **FAIL** | PASS | **Yes — uses the input-zero UB execution as a behavioral refutation** |
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

The reports' controlling authority is consistent with the exact-version official text. Rust/core 1.80.0 says that reaching [`unreachable_unchecked`](https://doc.rust-lang.org/1.80.0/core/hint/fn.unreachable_unchecked.html#safety) is UB. The Rust 1.80.0 Reference specifies [first-matching-arm selection](https://doc.rust-lang.org/1.80.0/reference/expressions/match-expr.html), [literal-pattern equality](https://doc.rust-lang.org/1.80.0/reference/patterns.html#literal-patterns), and [return of an evaluated function-tail expression](https://doc.rust-lang.org/1.80.0/reference/items/functions.html#function-body). Its [undefined-behavior chapter](https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html) also confirms that safe code triggering UB makes unsafe code unsound. No later-version premise is needed.

## Report-by-report evidence

### A

- **U1 PASS:** It derives selection of the `0` arm from exact 1.80.0 match/literal rules, quotes the exact-version `unreachable_unchecked` contract, and concludes that the unrestricted safe call `classify(0)` is UB and the API is **UNSOUND**.
- **U2 PASS:** It says the zero-input panic promise is “not established” and that “UB cannot supply a guaranteed panic outcome”; it does not use zero as a defined behavioral counterexample.
- **U3 PASS:** It separately derives that `classify(1)` normally returns `2`, notes `2 != 1`, and calls this a defined counterexample independent of the UB finding.
- **Hard error: none:** The API is not called sound, no zero-run observation is guaranteed, and the input-one refutation is explicit and independent.

### B

- **U1 PASS:** S-1 traces valid safe input `0` through the literal/match rules to `unreachable_unchecked`, then uses its 1.80.0 contract to conclude **UNSOUND**.
- **U2 PASS:** B-1 says UB supplies no Rust behavioral guarantee and the panic promise is “not established”; it does not assign `CONTRACT-BROKEN` on that basis.
- **U3 PASS:** B-2 uses the separate `1 => 2` execution, expressly calls it defined, and establishes `2 != 1` and **CONTRACT-BROKEN**.
- **Hard error: none:** Its zero-path treatment is non-observational and its one-path refutation is separate.

### C

- **U1 PASS:** S1 uses exact 1.80.0 numeric, pattern, match, and `unreachable_unchecked` authority to show the admitted safe call `classify(0u8)` reaches UB and makes the API **UNSOUND**.
- **U2 PASS:** D1 expressly labels the panic clause **UNPROVED** and says the UB execution establishes neither a defined panic nor a UB-free behavioral counterexample.
- **U3 PASS:** D2 expressly identifies `classify(1u8)` as a separate UB-free execution returning `2`, hence a counterexample to the normal-return postcondition.
- **Hard error: none:** It states the whole-execution rule correctly and keeps the two witnesses independent.

### D

- **U1 PASS:** It correctly traces safe input `0` to the unsafe call under exact 1.80.0 match/pattern and library authority and concludes **UNSOUND**.
- **U2 FAIL:** It says “Both documented clauses fail,” describes zero as reaching UB “rather than providing the promised panic,” and later says the panic clause is “not upheld.” That treats the UB-containing execution as a behavioral refutation instead of leaving the zero-input guarantee **UNPROVED**.
- **U3 PASS:** Independently, it identifies the UB-free `classify(1)` execution, normal result `2`, and `2 != 1` refutation.
- **Hard error: yes:** The quoted zero-case reasoning is exactly “using an observation from the input-zero execution as a behavioral refutation.” It does not additionally call the API sound or miss/conflate the independent input-one refutation.

### E

- **U1 PASS:** O-SOUND derives that valid safe input `0` selects the unsafe arm and reaches a function whose exact 1.80.0 contract makes reachability UB; verdict **UNSOUND**.
- **U2 PASS:** O-PANIC labels the guarantee **UNPROVED**, rejects the UB execution as a `CONTRACT-BROKEN` witness, and says no separate UB-free zero witness exists.
- **U3 PASS:** O-IDENTITY uses an “independent safe call” at input `1`, calls the context UB-free, and derives normal result `2 != 1`.
- **Hard error: none:** All three dispositions are separated exactly as the rubric requires.

### F

- **U1 PASS:** F1 states that safe input `0u8` selects the `0` arm and reaches `unreachable_unchecked`; its exact 1.80.0 contract and exact-version unsoundness authority support the **UNSOUND** verdict.
- **U2 PASS:** Although the ledger says “not upheld / subsumed by S1,” the operative proposition is that UB acts “rather than establishing a defined panic” and prevents “any source-level guarantee”; it does not label B1 `CONTRACT-BROKEN` or claim an observed non-panic.
- **U3 PASS:** F2 expressly calls `classify(1)` independent and defined, with the unsafe arm unexecuted, and derives normal result `2` rather than `1`.
- **Hard error: none:** In context, “not upheld” means no guarantee is established, while the behavioral refutation is expressly based on input one.

### G

- **U1 PASS:** S1/U1 and AX-1/AX-2 trace the admitted zero input to reached UB and the **UNSOUND** verdict.
- **U2 PASS:** B1 says the selected zero arm supplies no defined outcome and the panic guarantee is “not proved.”
- **U3 PASS:** B2 uses exact match and function-body authority to derive that the separate input-one path normally returns `2 != 1`, without executing unsafe code.
- **Hard error: none:** It makes no post-UB observation and explicitly separates the one-input counterexample.

### H

- **U1 PASS:** F1 uses exact Rust/core 1.80.0 pattern, match, and callee-safety text to show that valid safe input zero reaches UB and makes the API **UNSOUND**.
- **U2 PASS:** It says the zero panic clause “is not established,” supplies no defined panic behavior, and has no normal-return case under defined semantics.
- **U3 PASS:** F2 uses exact function-tail authority and the separate, unsafe-arm-free input-one path to derive normal result `2 != 1`.
- **Hard error: none:** It expressly says the independent input-one case, not zero, is why the behavior verdict is `CONTRACT-BROKEN`.

### I

- **U1 PASS:** Its exhaustive derivation uses exact-version `unreachable_unchecked`, match, and literal-pattern premises to show safe input zero reaches UB; verdict **UNSOUND**.
- **U2 PASS:** It says the zero panic promise is “not established” and that the path reaches UB “rather than a defined panic,” without using that as the contract-breaking witness.
- **U3 PASS:** It separately derives that input one does not execute the unsafe arm and normally returns `2 != input`, calling this a defined counterexample.
- **Hard error: none:** Soundness, unresolved zero behavior, and the defined one-input defect remain distinct.

### J

- **U1 PASS:** It verifies that zero is a valid `u8`, traces exact-version literal/match selection to the unsafe call, quotes the 1.80.0 UB contract, and concludes **UNSOUND**.
- **U2 PASS:** It says zero “does not establish” the promised defined panic and that after UB no behavior is guaranteed; it records “No guaranteed panic,” not a UB-free refutation.
- **U3 PASS:** Its table independently records input one returning `2`, no unsafe operation on that path, and `2 != 1` as **CONTRACT-BROKEN**.
- **Hard error: none:** There is no guaranteed post-UB observation and no conflation of witnesses.

### K

- **U1 PASS:** Exact 1.80.0 match/pattern and library axioms establish that valid safe zero selects the unsafe arm and produces UB; verdict **UNSOUND**.
- **U2 PASS:** It expressly labels the zero panic promise **UNPROVED** and says the UB execution can establish neither a panic observation nor the UB-free witness needed for `CONTRACT-BROKEN`.
- **U3 PASS:** Exact function-return authority supports its expressly independent UB-free `classify(1)` witness returning `2 != 1`.
- **Hard error: none:** Its treatment directly states and respects every prohibited conflation.

### L

- **U1 PASS:** S1 and the exact 1.80.0 callee contract establish that safe input zero reaches `unreachable_unchecked`, hence UB and **UNSOUND**.
- **U2 PASS:** The B1 result is “UNSOUND; no panic guarantee is established,” and the prose says backend behavior after UB cannot establish a source-level guarantee. This leaves B1 unresolved rather than deriving a defined non-panic.
- **U3 PASS:** B2 separately identifies `1 => 2` as a normally returning path that executes no unsafe operation and establishes `2 != 1`.
- **Hard error: none:** “B1 is also not guaranteed” is clarified as lack of establishment; `CONTRACT-BROKEN` is independently based on input one.

### M

- **U1 PASS:** Exact 1.80.0 literal, match, and `unreachable_unchecked` premises show the admitted safe input zero reaches UB; S1/U1 are correctly refuted.
- **U2 PASS:** The headline calls the panic promise “not established as defined Rust behavior.” The ledger’s “Not satisfied as a defined source behavior” is read consistently with that explicit no-proof disposition, not as a UB-free behavioral refutation.
- **U3 PASS:** It separately derives that input one selects `1 => 2`, returns normally, does not rely on the UB path, and conclusively refutes B2.
- **Hard error: none:** B1 is not labeled refuted or `CONTRACT-BROKEN`; the aggregate contract verdict is explicitly supported by input one.

### N

- **U1 PASS:** S1 uses exact 1.80.0 match/literal and callee-safety authority to show the valid safe call at zero reaches UB and makes the API **UNSOUND**.
- **U2 PASS:** B1 is expressly **UNPROVED**; it says the UB whole execution proves neither panic nor a UB-free `CONTRACT-BROKEN` witness.
- **U3 PASS:** B2 expressly uses the separate UB-free input-one execution returning normally with `2 != 1`.
- **Hard error: none:** The report precisely separates all three rubric propositions.

### O

- **U1 PASS:** S1 uses exact 1.80.0 `u8`, pattern, match, and `unreachable_unchecked` authority to show the unrestricted safe zero call reaches UB; verdict **UNSOUND**.
- **U2 PASS:** B2 labels the zero panic guarantee **UNPROVED** and says no independent UB-free derivation establishes either fulfillment or refutation.
- **U3 PASS:** B1 uses exact match/function-return authority to establish a separate UB-free input-one execution normally returning `2 != 1`.
- **Hard error: none:** Its atom numbering differs from the rubric labels, but the propositions are unambiguously correct and independent.

## Genuine rubric/authority ambiguities

1. **“Not upheld/not satisfied” wording in F, L, and M.** In isolation, those phrases could denote a behavioral refutation. In context, however, F says UB does not establish a defined panic, L says no panic guarantee is established, and M's headline says the promise is not established; all three anchor `CONTRACT-BROKEN` solely in the independent input-one execution. I therefore score U2 as PASS and do not assign a hard error. D is materially different because it expressly says both documented clauses “fail.”
2. **Authority granularity for routine source evaluation.** Some reports cite separate exact-version rules for match selection and function-tail return, while others state those elementary steps directly from the exact source and cite only the materially unsafe callee contract (most notably F and L). The scorer does not define whether every routine syntax step needs its own authority link. I treated explicit source tracing of `0 => ...` and `1 => 2` as establishing those elementary steps; I did not infer an omitted control-flow premise. All reports verify the decisive, version-sensitive `unreachable_unchecked` contract against Rust/core 1.80.0. No cited authority conflicts with the exact 1.80.0 official text.
