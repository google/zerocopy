# Mode V blind score

`PASS` means that the report establishes every material proposition in the atom with version-matched Rust authority or explicit equivalent reasoning. `None` in the hard-error column means none of the four listed hard errors applies.

| Report | V1 | V2 | V3 | V4 | Hard error |
|---|---|---|---|---|---|
| A | PASS | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | PASS | None |
| E | PASS | PASS | PASS | PASS | None |
| F | PASS | PASS | PASS | PASS | None |
| G | PASS | PASS | PASS | PASS | None |
| H | PASS | PASS | PASS | PASS | None |
| I | PASS | PASS | PASS | PASS | None |
| J | PASS | PASS | PASS | PASS | None |
| K | PASS | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | PASS | None |
| M | PASS | PASS | PASS | PASS | None |
| N | PASS | PASS | PASS | PASS | None |
| O | PASS | PASS | PASS | PASS | None |

## Report-by-report evidence

### A

- **V1:** `O1` cites both versioned Reference array-layout rules and derives `size_of::<[u8; 0]>() = 0`, hence `add(1)` has byte offset `1 * 0 = 0`.
- **V2:** `O2-79` cites the 1.79 `add`, `null`, and pointer-safety text, explains that null satisfies no allocated-object bound, and supplies the safe call `let _ = advance_marker();`; it concludes `UNSOUND`.
- **V3:** `O2-80` cites the 1.80 clause that a zero offset is always well-defined and notes that the raw result is not dereferenced; it concludes `PROVED`.
- **V4 / hard error:** The verdict table partitions 1.79 and 1.80, reports the union `UNSOUND`, and the TCB says no cross-version premise is used. Both regional verdicts, the null safe-call witness, and the zero-size derivation are present, so no hard error applies.

### B

- **V1:** The boundary section cites the 1.79/1.80 array-layout rules and derives the zero byte offset.
- **V2:** The ledger marks 1.79 `O2` failed; the text cites version-matched `null`, pointer-safety, and `add` documentation, then gives `let _ = advance_marker();` as the safe UB witness and says `UNSOUND`.
- **V3:** It quotes the 1.80 zero-offset exception, discharges the arithmetic clauses, and observes that returning the pointer is not a dereference; the region is `PROVED`.
- **V4 / hard error:** It reports the two regions separately and the combined set `UNSOUND`, explicitly refusing to apply 1.80 wording backward. No listed hard error applies.

### C

- **V1:** `O-ADD` cites versioned `size_of` documentation and computes `1 * 0 = 0` bytes.
- **V2:** The 1.79 derivation cites `add`, `null`, and pointer-safety text, identifies the unconditional safe invocation as a UB counterexample, and reports `UNSOUND`.
- **V3:** The 1.80 derivation quotes the zero-offset rule, checks the arithmetic, and notes that no dereference occurs; it reports `PROVED`.
- **V4 / hard error:** Its opening table partitions both releases and gives the combined result `UNSOUND`; its versioned TCB uses no compatibility premise. The required witness and size derivation are explicit, so no hard error applies.

### D

- **V1:** The TCB and ledger cite exact-version `size_of` pages and derive `1 * size_of::<[u8; 0]>() = 0`.
- **V2:** `O3` is marked violated under 1.79; the report cites the versioned `null` and `add` contracts, explicitly reasons that null is not in or one-past an allocation, and identifies an ordinary safe invocation as the UB witness. Verdict: `UNSOUND`.
- **V3:** It quotes the 1.80 zero-offset exception, discharges `O1`/`O2`, and states there is no dereference or later unsafe consumer. Verdict: `PROVED`.
- **V4 / hard error:** It gives separate regional verdicts and says the combined set is `UNSOUND` because 1.80 cannot repair the 1.79 counterexample. No listed hard error applies.

### E

- **V1:** The boundary section cites both versioned `size_of` pages and derives the zero-sized pointee and zero byte offset.
- **V2:** The 1.79 section cites `add`, `null`, and contemporaneous pointer-safety text; it explains the failed allocation conjunct and identifies every ordinary safe call as the witness. Verdict: `UNSOUND`.
- **V3:** The 1.80 section quotes “always well-defined” for zero offset, checks arithmetic, and notes that returning the raw pointer adds no obligation. Verdict: `PROVED`.
- **V4 / hard error:** Its table exhaustively partitions the releases and reports the union `UNSOUND`; the TCB forbids cross-version inference. Both required derivations are present, so no hard error applies.

### F

- **V1:** It cites both releases' `size_of` contracts and computes the offset as `1 * 0 = 0`.
- **V2:** It cites the 1.79 `add`, `null`, and pointer-module rules, explains the false allocated-object conjunct, and says every safe call is a counterexample. Verdict: `UNSOUND`.
- **V3:** It cites the revised 1.80 `add` wording, explicitly permits the null base for zero offset, and notes that a later dereference would be a separate unsafe act. Verdict: `PROVED`.
- **V4 / hard error:** The table reports both regional results and combined `UNSOUND`; versioned TCB entries are kept separate. No hard error applies.

### G

- **V1:** Common facts 2–3 derive the zero-sized array and zero byte offset, with exact 1.79/1.80 Reference links in `AXIOM-LAYOUT-179/180`.
- **V2:** The report cites the exact 1.79 `null` and `add` contracts, explicitly states that null is neither in nor one-past an allocation, and names any call to the safe argument-free API as the UB counterexample. Verdict: `UNSOUND`.
- **V3:** It quotes the exact 1.80 zero-offset exception, checks the arithmetic clauses, and notes the absence of a dereference. Verdict: `PROVED`.
- **V4 / hard error:** Despite placeholder region labels, the bullets unambiguously name Rust 1.79 and 1.80, give their separate verdicts, and state that the combined set is `UNSOUND`; the TCB rejects backward compatibility premises. No hard error applies.

### H

- **V1:** `OB-1` cites both versioned `size_of` pages and derives `1 * 0 = 0`.
- **V2:** The 1.79 section cites `add`, `null`, and pointer-module validity text, explains why zero does not waive the allocation clause, and gives a direct safe invocation as the witness. Verdict: `UNSOUND`.
- **V3:** The 1.80 section cites the changed clause, checks `isize`/`usize`, and observes no access or reference creation. Verdict: `PROVED`.
- **V4 / hard error:** Its table partitions the versions and gives combined `UNSOUND`; it explicitly says the 1.80 text is not projected backward. The witness and size derivation are present, so no hard error applies.

### I

- **V1:** The obligation ledger cites both versioned array-layout rules and computes a zero byte offset.
- **V2:** It cites exact 1.79 `null` and `add` pages, explicitly reasons that null designates no allocation, and identifies an ordinary safe call as the unconditional UB witness. Verdict: `UNSOUND`.
- **V3:** It quotes the 1.80 zero-offset exception, discharges the arithmetic clauses, and states that there is no dereference, reference creation, or unsafe consumer. Verdict: `PROVED`.
- **V4 / hard error:** The opening verdicts partition the releases and make the combined set `UNSOUND`; the TCB excludes cross-version compatibility. No listed hard error applies.

### J

- **V1:** `O-1` cites version-matched `size_of` documentation and derives `size_of::<[u8; 0]>() = 0` and byte offset zero.
- **V2:** `O-2/1.79` cites `null`, pointer-safety, and `add` documentation for 1.79, then gives `let _ = advance_marker();` as the safe UB witness. Verdict: `UNSOUND`.
- **V3:** `O-2/1.80` quotes the changed allocation clause, checks arithmetic, and notes that the result is returned without access. Verdict: `PROVED`.
- **V4 / hard error:** The verdict table reports both regions and combined `UNSOUND`; the TCB says no later documentation was carried backward. Both mandated derivations are explicit, so no hard error applies.

### K

- **V1:** `O-SIZE` cites exact-version standard-library `size_of` pages and derives the zero byte offset.
- **V2:** `O-179` cites the 1.79 `null`, pointer-safety, and primitive-pointer `add` pages, then states that every safe call executes UB at line 4. Verdict: `UNSOUND`.
- **V3:** `O-180` quotes the 1.80 zero-offset rule, discharges the arithmetic clauses, and notes no access or dereference. Verdict: `PROVED`.
- **V4 / hard error:** The table gives separate version rows and combined `UNSOUND`; all TCB consumers are restricted to matching versions. The required witness and derivation are present, so no hard error applies.

### L

- **V1:** The derivation cites both versioned `size_of` pages and computes `1 * 0 = 0`.
- **V2:** Its 1.79 section cites `null`, pointer-safety, and `add`, explains conjunction failure, and identifies every safe invocation as the concrete counterexample. Verdict: `UNSOUND`.
- **V3:** Its 1.80 section quotes the zero-offset exception, checks the other clauses, and notes no access/reference creation. Verdict: `PROVED`.
- **V4 / hard error:** The opening table partitions both toolchains and reports combined `UNSOUND`; its TCB is exact-version. No hard error applies.

### M

- **V1:** Common fact 1 cites both versioned `size_of` pages; common fact 3 derives the byte offset as zero.
- **V2:** The 1.79 section cites `add`, `null`, and the exact-version Reference dangling-pointer rule, explains why address-zero null meets neither allowed zero-size case, and says every safe call reaches UB. Verdict: `UNSOUND`.
- **V3:** The 1.80 section quotes the zero-offset exception, checks arithmetic, and explains that the pointer is merely returned. Verdict: `PROVED`.
- **V4 / hard error:** The opening bullets partition both versions and report their union `UNSOUND`; the TCB expressly forbids compatibility inference. Both required derivations are included, so no hard error applies.

### N

- **V1:** `O1` cites both exact-version Reference array-layout pages and derives `1 * 0 = 0` bytes.
- **V2:** `O2` cites exact 1.79 `null` and `add` contracts, explicitly says null is not in or one-past an allocated object, and calls invocation of the safe API a valid counterexample. Verdict: `UNSOUND`.
- **V3:** `O3` cites and quotes the 1.80 zero-offset rule, checks the arithmetic clauses, and notes that no dereference occurs. Verdict: `PROVED`.
- **V4 / hard error:** Its table gives the two regional verdicts and combined `UNSOUND`, and its TCB says the 1.80 text is not projected backward. The witness and zero-size derivation are present, so no hard error applies.

### O

- **V1:** The configuration section cites both versioned Reference array-layout rules and derives the zero byte offset.
- **V2:** `O-79` cites exact 1.79 `null`, pointer-safety, and `add` text and states that every ordinary call is the safe UB witness. Verdict: `UNSOUND`.
- **V3:** `O-80` quotes the 1.80 zero-offset exception, checks `isize`/`usize`, and notes the lack of dereference. Verdict: `PROVED`.
- **V4 / hard error:** Its verdict table partitions both versions and reports their union `UNSOUND`; its TCB disclaims compatibility premises. Both required derivations are explicit, so no hard error applies.

## Rubric and authority ambiguities

The controlling official texts are not ambiguous for this source: [Rust 1.79.0 `pointer::add`](https://doc.rust-lang.org/1.79.0/core/primitive.pointer.html#method.add) states the allocation-bound requirement without a zero-offset exception, while [Rust 1.80.0 `pointer::add`](https://doc.rust-lang.org/1.80.0/core/primitive.pointer.html#method.add) expressly says a zero computed offset is always well-defined. The array-size rule is explicit in both the [1.79.0](https://doc.rust-lang.org/1.79.0/reference/type-layout.html#array-layout) and [1.80.0](https://doc.rust-lang.org/1.80.0/reference/type-layout.html#array-layout) References.

There is one evidentiary-granularity ambiguity in `SCORER.md`: it does not say whether, for V2, a report must cite a separate pointer-validity/dangling-pointer page after citing the exact-version `ptr::null` page and exact-version `pointer::add` contract. D, G, I, and N take the latter route and explicitly make the semantic bridge that a null pointer is not in or one-past an allocation; the other reports generally add the pointer-validity or dangling-pointer citation. I score D, G, I, and N `PASS` because each material Rust operation is tied to exact 1.79 documentation and the bridge is expressly reasoned rather than silently inferred. Under a stricter rule requiring a distinct authority citation for that bridge, only V2 for D, G, I, and N would change to `FAIL`; their hard-error cells would remain `None` because each still states the null safe-call witness and the correct regional verdict.
