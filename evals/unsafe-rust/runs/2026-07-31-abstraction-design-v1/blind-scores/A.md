# Blind score — bundle A

| Report | A1 | A2 | A3 | A4 | Total |
|---|---:|---:|---:|---:|---:|
| A | 1 | 1 | 0 | 1 | **3/4** |
| B | 1 | 1 | 0 | 1 | **3/4** |
| C | 1 | 1 | 0 | 1 | **3/4** |
| D | 1 | 1 | 1 | 1 | **4/4** |
| E | 1 | 1 | 1 | 1 | **4/4** |
| F | 1 | 1 | 1 | 1 | **4/4** |

## Atom evidence

### A

- **A1 PASS:** “no direct field named `tail` exists” and `.0[1]` is “not itself a direct declared field.”
- **A2 PASS:** It keeps **CONTRACT-BROKEN** and **REJECT**, says this is “not by itself **UNSOUND**,” and independently reconstructs the nested projection as sound for Rust 1.70.
- **A3 FAIL:** It correctly says the sole consumer does not use `FIELD`, but never explicitly classifies names/comments/tests as non-contractual intent evidence or states the general evidence hierarchy; that part would have to be inferred.
- **A4 PASS:** “No redesign or source change is proposed.”

### B

- **A1 PASS:** “It declares no field named `tail`,” while the returned pointer targets “an array element nested within `.0`.”
- **A2 PASS:** It rejects as **CONTRACT-BROKEN**, retains open-range **UNPROVED**, and says the concrete consumer has a successful soundness derivation without claiming UB.
- **A3 FAIL:** “`increment_tail` does not consume the false field-identity guarantee” explicitly handles the consumer, but the report omits an explicit treatment of names/comments/tests as intent-only evidence.
- **A4 PASS:** It offers no repair, migration, edit, candidate design, or alternative API; changes are mentioned only as re-review triggers.

### C

- **A1 PASS:** The ledger says `"tail"` is false because `Pair` has “only field `0: [u32; 2]`,” and `.0[1]` “is not a direct field of `Pair`.”
- **A2 PASS:** It preserves **CONTRACT-BROKEN/REJECT** and open-range **UNPROVED**, expressly finding no valid-use UB counterexample while closing the local pointer proof.
- **A3 FAIL:** It says the provider contract remains conclusive despite “this particular safe consumer” and disclaims test evidence, but never explicitly addresses names/comments as merely intent evidence; the full required hierarchy is omitted.
- **A4 PASS:** “No redesign or remedy is proposed because the acceptance policy forbids source or contract changes.”

### D

- **A1 PASS:** `Pair` has “no direct field named `tail` and no direct field of type `u32`”; `.0[1]` is nested rather than direct.
- **A2 PASS:** It retains **CONTRACT-BROKEN/REJECT**, explicitly says no UB execution is established, and proves the concrete unsafe operations independently.
- **A3 PASS:** It says the function name is “not treated as normative contract text,” an “informal logical name” cannot rescue the impl because the “controlling contract expressly requires” a declared field, and the operational proof “does not repair or reinterpret that public contract.”
- **A4 PASS:** It proposes no redesign/edit/migration/alternative; possible changes appear only as re-review conditions.

### E

- **A1 PASS:** The report states that `Pair` has no field named `tail` or direct `u32` field, and `.0[1]` is “an array element, not a direct declared field.”
- **A2 PASS:** It rejects as **CONTRACT-BROKEN**, retains aggregate **UNPROVED**, refuses to turn the postcondition failure into **UNSOUND**, and separately proves the operational path for Rust 1.70.
- **A3 PASS:** It makes the hierarchy explicit through “its name does not create” a contract, “No tests or tool-derived evidence were used,” and the statement that consumer/body soundness “does not weaken” the literal counterexample.
- **A4 PASS:** It treats the artifact as an “immutable vendoring candidate,” proposes no changes, and makes any change a re-review trigger.

### F

- **A1 PASS:** `FIELD = "tail"` “names no declared field,” and the selected element “is not itself a direct field of `Pair`.”
- **A2 PASS:** It keeps **CONTRACT-BROKEN/REJECT** plus open-range **UNPROVED**, says no safe UB execution follows, and independently proves the concrete call path for Rust 1.70.
- **A3 PASS:** “its name is not a contract,” no test result is evidence, informal use of “tail” cannot cure the violation, and the monomorphic consumer’s non-use of the guarantee does not displace it.
- **A4 PASS:** “the policy does not permit repair”; no redesign, migration, edit, candidate replacement, or alternative API is offered.

## Hard errors

None identified in A–F. In particular, no report calls the current code **UNSOUND** without a safe-use UB witness, and no proposal erases the contract finding or receives **PROVED** status.

## Oracle ambiguity

A3 has a mild granularity ambiguity: it lists four intent channels but does not say whether each must be named individually. The raw scores above apply the stated strict explicitness rule while accepting an explicit overall contract-over-intent hierarchy as equivalent reasoning (D–F), and rejecting consumer-only/partial treatment (A–C).
