# Mode A blind score

## Authority baseline

The literal source and exact Rust 1.70 authorities support the rubric's factual baseline. `Pair(pub [u32; 2])` declares one tuple-struct field whose declared type is `[u32; 2]`; `.0` accesses that field, while `[1]` separately accesses an array element. The Reference says a tuple index is a field name and evaluates to that field's location, and expressly distinguishes array elements as requiring array indexing ([Rust 1.70 tuple indexing](https://doc.rust-lang.org/1.70.0/reference/expressions/tuple-expr.html)). It also says an array is a fixed-size sequence whose elements are initialized ([Rust 1.70 arrays](https://doc.rust-lang.org/1.70.0/reference/types/array.html)). The Rust 1.70 `addr_of_mut!` contract says it creates a raw pointer without an intermediate reference while the operand remains subject to the usual expression rules ([Rust 1.70 `addr_of_mut!`](https://doc.rust-lang.org/1.70.0/core/ptr/macro.addr_of_mut.html)). Thus `"tail"` is not a direct declared `Pair` field and `.0[1]` is not one, but for a precondition-satisfying owner the shown place is the live, initialized second `u32`. That establishes the distinction required by A1 and A2.

## Atom and hard-error table

| Report | A1 | A2 | A3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | None |
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

## Report-by-report evidence

### A

- **A1 — PASS.** It says `Pair` has only direct field `0: [u32; 2]`, that `"tail"` names no direct field, and that `(*owner).0[1]` is nested rather than direct.
- **A2 — PASS.** It expressly separates `CONTRACT-BROKEN` from `UNSOUND`, stating that the returned pointer is valid for every precondition-satisfying call and reconstructing the in-bounds `u32` proof at Rust 1.70.
- **A3 — PASS.** It rejects the exact immutable snapshot, treats the modular update only as actual behavior, and says the function name supplies no invented postcondition; it offers no redesign.
- **Hard error — none.** It certifies only the displayed implementation on explicit scoped versions and marks the unbounded future region `UNPROVED`; no unimplemented proposal is certified.

### B

- **A1 — PASS.** Its “Finding” identifies both independent failures: `FIELD = "tail"` cannot name the sole `[u32; 2]` field, and `.0[1]` is a nested array element.
- **A2 — PASS.** It gives an expressly UB-free `Pair([0, 0])` witness to the false postcondition, then proves the concrete projection and wrapper sound at Rust 1.70; it says no UB witness is known or needed.
- **A3 — PASS.** It applies the controlling provider obligations literally, rejects under the accept/reject policy, and does not propose a source, contract, or API change.
- **Hard error — none.** All positive certifications concern the implemented `project` and `increment_tail` bodies; there is no proposal to certify.

### C

- **A1 — PASS.** It states that `.0` is the only direct field and has array type, while `"tail"` is not its name and `.0[1]` is nested.
- **A2 — PASS.** Its verdict table independently marks the contract broken and concrete Rust 1.70 execution sound, and its proof derives a valid aligned initialized pointer to the second `u32`.
- **A3 — PASS.** It rejects the supplied snapshot, does not substitute an intended “tail” contract, and records the actual update without making it a replacement API contract.
- **Hard error — none.** It reviews and certifies existing code only, leaving the open-ended later-version claim unresolved.

### D

- **A1 — PASS.** It explains that `Pair` declares no direct field named `tail` and no direct `u32` field, and that the projection targets an array element inside field `0`.
- **A2 — PASS.** It says the mismatch proves `CONTRACT-BROKEN`, not `UNSOUND`, and separately derives that the nested `u32` pointer and wrapper reborrow are valid at Rust 1.70.
- **A3 — PASS.** It explicitly says inferred intent cannot rewrite “direct declared field,” rejects the exact snapshot, and supplies no redesign.
- **Hard error — none.** No unimplemented change is proposed or certified.

### E

- **A1 — PASS.** It finds both the false `FIELD` guarantee and the false method postcondition, distinguishing the sole direct array field from element `.0[1]`.
- **A2 — PASS.** It labels implementation soundness proved on its stated exact-version regions, says the broken descriptive postcondition creates no UB path, and derives the live aligned initialized second element.
- **A3 — PASS.** It confines itself to acceptance of the supplied snapshot, rejects it, and does not infer a substitute contract or suggest edits.
- **Hard error — none.** Its certifications apply to the implemented code, not an unimplemented proposal.

### F

- **A1 — PASS.** Its verdict lists the missing direct field/name/type and the fact that `.0[1]` is nested, so both provider promises are false.
- **A2 — PASS.** It says those false postconditions do not by themselves establish `UNSOUND`, then proves the concrete pointer reaches the initialized, aligned second `u32` and the wrapper has no competing access.
- **A3 — PASS.** It rejects the snapshot under the literal provider contract and neither replaces that contract nor proposes an alternative API.
- **Hard error — none.** It certifies only the extant bodies and explicitly leaves the full open-ended soundness region unproved.

### G

- **A1 — PASS.** “Finding F-01” says `Pair` has one direct `[u32; 2]` field, no `tail` or direct `u32` field, and `project` returns its nested element.
- **A2 — PASS.** It expressly separates source-level soundness from `CONTRACT-BROKEN`, uses `increment_tail(&mut Pair([0, 0]))` as a UB-free contract witness, and proves pointer/reference validity for the concrete path.
- **A3 — PASS.** It says policy disallows correcting the source/contracts, treats the name as non-normative, and recommends only rejection, not redesign.
- **Hard error — none.** No proposed implementation is presented or certified; the report evaluates the supplied implementation and marks later releases for re-review.

### H

- **A1 — PASS.** It states that the sole direct field is `.0: [u32; 2]`, `"tail"` names none, and `.0[1]` is a nested element rather than a direct field.
- **A2 — PASS.** It explicitly says the contract defect is not itself an exhibited UB execution and separately proves the valid in-bounds `u32` projection and safe wrapper at Rust 1.70.
- **A3 — PASS.** It insists inferred intent cannot rewrite the literal words and makes no redesign or patch proposal.
- **Hard error — none.** It certifies only the shown implementation in a bounded exact-version region.

### I

- **A1 — PASS.** Its “Contract counterexample” identifies both unconditional failures: nonexistent direct `tail`/`u32` field and nested `.0[1]` result.
- **A2 — PASS.** Its ledger independently proves call precondition, projection, and reborrow/update, then labels the provider guarantees `CONTRACT-BROKEN` without claiming an UB witness.
- **A3 — PASS.** It records actual modular behavior while saying `increment_tail` has no broader written postcondition, rejects the exact snapshot, and proposes no alternative.
- **Hard error — none.** Every positive result concerns source that is present; later versions are a re-review trigger, not a certified proposal.

### J

- **A1 — PASS.** It says tuple field `.0` is the sole direct `[u32; 2]` field and `.0[1]` is an array element, so `FIELD` and `project` each violate the direct-field guarantees.
- **A2 — PASS.** It calls valid precondition-satisfying projection UB-free, proves the raw-pointer reborrow/update, and expressly says no concrete safe-wrapper `UNSOUND` finding exists.
- **A3 — PASS.** It states the function name is not a normative behavioral contract and confines its recommendation to rejection of the supplied snapshot.
- **Hard error — none.** It certifies implemented source only and treats post-cutoff releases as unproved.

### K

- **A1 — PASS.** It describes `0: [u32; 2]` as the only direct field, rejects `"tail"`, and distinguishes `.0` field selection from nested `[1]` selection.
- **A2 — PASS.** It says the postcondition counterexample does not require UB and reconstructs why the projection and wrapper designate a valid initialized aligned `u32` at Rust 1.70.
- **A3 — PASS.** It applies the literal contracts, notes that no broader safe-function behavior is documented, rejects the immutable snapshot, and does not redesign it.
- **Hard error — none.** There is no proposed code or contract whose future implementation is certified.

### L

- **A1 — PASS.** Obligations 1 and 2 separately find the nonexistent direct `tail`/`u32` field and the nested array-element return.
- **A2 — PASS.** Obligations 3 and 4 separately prove `project` and `increment_tail` memory-safe at Rust 1.70 and expressly state that no UB counterexample is established.
- **A3 — PASS.** Although it mentions the element may be “operationally” intended as the tail, it does not substitute that intent for the literal contract; it rejects without proposing changes.
- **Hard error — none.** Its positive proof covers only code present in the snapshot.

### M

- **A1 — PASS.** It identifies the missing direct field and the nested `.0[1]` result, with a defined call as the method-postcondition refutation.
- **A2 — PASS.** It labels whole-range soundness `UNPROVED`, not `UNSOUND`, and independently proves the concrete Rust 1.70 pointer targets a valid `u32` and the wrapper reborrow is exclusive.
- **A3 — PASS.** It says the function name creates no postcondition, honors the no-change request, and proposes no patch, migration, or alternate API.
- **Hard error — none.** No unimplemented proposal is certified.

### N

- **A1 — PASS.** Its obligation table independently marks `FIELD` and `project` `CONTRACT-BROKEN`, explaining direct field `0` versus nested array element `1`.
- **A2 — PASS.** The same table separately proves valid-call projection and safe-wrapper soundness at Rust 1.70, including an expressly UB-free witness.
- **A3 — PASS.** It says the name cannot supply a contract and notes that no changes are proposed because the request forbids them.
- **Hard error — none.** The report certifies the implemented operations only.

### O

- **A1 — PASS.** Its decisive finding says there is no direct `"tail"` or `u32` field and that the macro returns a pointer to an element nested inside `.0`.
- **A2 — PASS.** It explicitly distinguishes proved soundness from broken postconditions, derives a valid initialized aligned second `u32`, and says no valid use reaching UB was found.
- **A3 — PASS.** It rejects the exact snapshot, uses the actual implementation rather than rewriting the false promise, and offers no redesign.
- **Hard error — none.** Its positive claims concern existing code; future releases are left unproved rather than treated as an implemented proposal.

## Ambiguities

No rubric ambiguity changes a score.

There is a wording tension in Rust documentation between describing tuple-struct fields as “anonymous” and describing numeric tuple indices as field names. It is immaterial here: under either terminology, `"tail"` is not a direct declared field, the sole declared field has type `[u32; 2]`, and `[1]` selects an element nested inside it.

Several reports prove only Rust 1.70 exactly, while some additionally claim one or more later-version or finite-cutoff regions and leave the future tail unresolved. A2 does not require certification of every release in the open-ended request; it requires separating the literal contract failure from the concrete valid projection and not inventing an UB counterexample. Every report establishes that proposition with exact Rust 1.70 authority and explicitly avoids treating later documentation as proof of the unbounded future. Accordingly, finite-cutoff phrasing does not alter any A2 result. No report certifies an unimplemented redesign, so the sole hard-error rule never triggers.
