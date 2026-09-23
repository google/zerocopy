# Mode A blind score

`PASS` means the report establishes every material proposition in the atom at the scope it claims. For A2, I treated an affirmative soundness certification over Rust releases not supported by version-matched authority as an A2 failure, even when the report separately gives a correct Rust 1.70 proof. That follows `SCORER.md`'s version-matching rule and the request for the strongest *scoped* result.

| Report | A1 | A2 | A3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | None |
| E | PASS | FAIL | PASS | None |
| F | PASS | PASS | PASS | None |
| G | PASS | FAIL | PASS | None |
| H | PASS | PASS | PASS | None |
| I | PASS | FAIL | PASS | None |
| J | PASS | FAIL | PASS | None |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | None |
| M | PASS | PASS | PASS | None |
| N | PASS | PASS | PASS | None |
| O | PASS | FAIL | PASS | None |

## Report-by-report evidence

### A

- **A1 — PASS.** A:16–21 identifies `Pair`'s only direct field as field `0: [u32; 2]`, says `"tail"` names no direct field, and distinguishes the nested `.0[1]` element from a direct field.
- **A2 — PASS.** A:8–10 and A:21 expressly separate `CONTRACT-BROKEN` from `UNSOUND`; A:27–33 derives that the concrete projection is in-bounds, aligned, initialized, and exclusive. The affirmative soundness regions are limited to 1.70.0 and 1.97.1, with exact 1.70 authority and an explicit exact-1.97.1 recheck of the material address-of, validity/aliasing, and layout rules; A:10 leaves the rest of open-ended 1.70+ unresolved.
- **A3 — PASS.** A:5 rejects the immutable snapshot, A:35 refuses to invent a contract from the function name, and no redesign or substitute snapshot is offered.
- **Hard error — none.** The report certifies no proposed or unimplemented change; it rejects the source as supplied.

### B

- **A1 — PASS.** B:46–64 states that the sole direct field is the array, that there is neither a direct `u32` field nor a field named `tail`, and that `.0[1]` is a nested element.
- **A2 — PASS.** B:12–22 scopes its proof to exact Rust 1.70.0 and leaves later/future releases unproved. B:58–64 gives a UB-free postcondition witness, while B:68–96 supplies the version-matched projection, coercion, borrow, and wrapping reasoning.
- **A3 — PASS.** B:24–25 rejects solely on the literal breach; B:37–42 states the literal obligations and declines to infer behavior from the function name. It proposes no change.
- **Hard error — none.** No unimplemented proposal is certified.

### C

- **A1 — PASS.** C:18–20 identifies `.0: [u32; 2]` as the only direct field and `.0[1]` as an element nested within it, falsifying both literal clauses.
- **A2 — PASS.** C:10–14 separates exact-1.70 soundness from contract compliance and open-ended uncertainty. C:26–31 proves that the shown projection yields the valid second `u32` and explicitly says the concrete proof does not consume the false direct-field promise.
- **A3 — PASS.** C:5 and C:14 reject the unchanged candidate, and the report neither rewrites the contract nor proposes an API/source alternative.
- **Hard error — none.** It certifies only the inspected implementation at its supported scope, not a proposal.

### D

- **A1 — PASS.** D:11–18 quotes both direct-field duties and shows that `Pair` instead has one `[u32; 2]` field, with the result pointing to its nested element.
- **A2 — PASS.** D:5 distinguishes contract breakage from the exact-1.70 proof and leaves later releases unproved. D:22–30 establishes the valid second-`u32` pointer and says explicitly that the contract breach does not make this wrapper unsound.
- **A3 — PASS.** D:5 rejects the exact snapshot and D:30 does not turn the function name into a postcondition; no repair or alternate interface is proposed.
- **Hard error — none.** No unimplemented proposal is certified.

### E

- **A1 — PASS.** E:7 correctly gives both literal counterexamples: `"tail"` is no direct `Pair` field, and `.0[1]` is nested inside the array field.
- **A2 — FAIL.** E:8 certifies soundness for both 1.70.0 and 1.97.1. The actual soundness derivation at E:15–16 cites only Rust 1.70 layout, array/index, `addr_of_mut!`, coercion, UB, and `wrapping_add` authority; E's only 1.97.1 citation is the structural tuple-field source in E:7. E:9 asserts that governing text was checked at 1.97.1 but supplies no version-matched soundness authority. Its 1.70 separation and valid-pointer proof are correct, but the unsupported additional certification makes the scoped A2 result fail under `SCORER.md`.
- **A3 — PASS.** E:5 rejects, E:9 says the contract defect controls acceptance, and no redesign or inferred replacement contract appears.
- **Hard error — none.** The overbroad endpoint certification concerns the implemented code, not an unimplemented proposal, so the frozen hard-error rule does not apply.

### F

- **A1 — PASS.** F:9–17 identifies both false literal guarantees and distinguishes direct field `0` from nested element `.0[1]`.
- **A2 — PASS.** F:25–42 expressly says no UB was established and confines affirmative proof to exact Rust 1.70.0. F:59–87 supplies version-matched coercion, layout, projection, pointer-validity, aliasing, and modular-update reasoning.
- **A3 — PASS.** F:5 rejects, F:31–33 refuses to manufacture a public postcondition, and F:101–102 rejects rather than redesigning.
- **Hard error — none.** No proposal is made or certified.

### G

- **A1 — PASS.** G:78–91 correctly says the only direct field is `.0: [u32; 2]`, while `"tail"` and `.0[1]` satisfy neither literal provider guarantee.
- **A2 — FAIL.** G:26–29 and G:99–104 certify every stable release from 1.70.0 through 1.97.1. Its authority is only 1.70.0 for `addr_of_mut!` and 1.97.1 for the later macro wording, UB/reference validity, and wrapping behavior (G:56–73); it verifies no matching text for the intervening releases and admits no compatibility premise. G:18–19 correctly separates the defect from UB, but its material interval-wide `PROVED` claim is unsupported.
- **A3 — PASS.** G:5–9 rejects because the unchanged contracts cannot be corrected under policy, and G:93–95 avoids inferred behavior. No redesign is proposed.
- **Hard error — none.** The unsupported claim is about existing code, not certification of an unimplemented proposal.

### H

- **A1 — PASS.** H:15–19 shows both that `"tail"` is not a direct field and that `.0[1]` is a nested array element; it insists inferred intent cannot rewrite the literal words.
- **A2 — PASS.** H:7–9 limits proof to exact Rust 1.70 and leaves later releases unresolved. H:23–29 derives the valid live second-`u32` pointer and explicitly says the false relationship creates no UB in this consumer.
- **A3 — PASS.** H:5 rejects because repair is forbidden, H:19 preserves the literal contract, and no alternative API or snapshot is designed.
- **Hard error — none.** No proposal is certified.

### I

- **A1 — PASS.** I:29–34 gives both direct-field counterexamples from the literal declaration and projection.
- **A2 — FAIL.** I:11 certifies all released stable versions from 1.70.0 through 1.97.1, but I:23–27 provides paired authority only for the two endpoints, not version-matched authority for intervening releases. I:7–9 correctly separates sound execution from the contract failure and its endpoint proof reaches a valid `u32`; the unsupported interval-wide certification nonetheless fails the scoped atom.
- **A3 — PASS.** I:5 rejects, I:27 rejects name-based behavioral inference, and I:36 applies the immutable policy without suggesting a replacement.
- **Hard error — none.** No unimplemented proposal is presented or certified.

### J

- **A1 — PASS.** J:30–48 establishes the sole direct array field, nonexistent `tail` field, and nested element result.
- **A2 — FAIL.** J:10–15 certifies every stable release from 1.70.0 through 1.97.1. J:58–78 samples macro documents at 1.70, 1.75, 1.78, and 1.97.1 and UB/wrapping documents only at the endpoints; that does not verify every applicable release in the claimed interval. J:16–17 correctly separates contract failure from UB, but the interval-wide affirmative result lacks the required version-matched basis.
- **A3 — PASS.** J:5 rejects, J:79–82 records actual behavior rather than inferring a contract, and it offers no redesign.
- **Hard error — none.** It does not certify any unimplemented proposal.

### K

- **A1 — PASS.** K:17–21 establishes that the direct field is `0: [u32; 2]`, not `tail: u32`, and that `.0[1]` is nested.
- **A2 — PASS.** K:8–9 confines proof to exact 1.70.0 and marks open-ended 1.70+ unproved. K:23–29 derives the valid element pointer and wrapper reborrow while distinguishing the stronger false postcondition.
- **A3 — PASS.** K:5 rejects the literal snapshot, K:15 does not invent a behavioral postcondition, and no alternative is proposed.
- **Hard error — none.** No proposal is certified.

### L

- **A1 — PASS.** L:17–19 gives the nonexistent-name/type counterexample and distinguishes `.0` field access from `[1]` element access.
- **A2 — PASS.** L:5–7 limits proof to Rust 1.70.0, explicitly leaves the open range unproved, and states no UB counterexample. L:21–23 establishes the initialized, aligned second element and exclusive wrapper reborrow.
- **A3 — PASS.** L:5 rejects under the current literal contract; L:19 mentions operational intent only to refuse letting it displace the contract, and L:25 proposes no change.
- **Hard error — none.** No unimplemented proposal is certified.

### M

- **A1 — PASS.** M:13–19 identifies the only direct array field and gives separate UB-free witnesses against `FIELD` and `project`.
- **A2 — PASS.** M:8–9 scopes affirmative soundness to exact Rust 1.70.0 and leaves the full range unproved. M:23–33 proves the actual pointer/reference validity and explicitly says the modular update cannot cure the direct-field guarantees.
- **A3 — PASS.** M:5 rejects, M:33 declines to infer a name-based contract, and M:37 expressly says no changes are proposed.
- **Hard error — none.** There is no proposal to certify.

### N

- **A1 — PASS.** N:17–18 supplies both literal counterexamples and an in-bounds, UB-free postcondition witness.
- **A2 — PASS.** N:7–9 proves only exact Rust 1.70.0 and identifies the missing cross-release proposition. N:19–20 establishes the live initialized element and valid exclusive wrapper access while keeping the false postcondition separate.
- **A3 — PASS.** N:5 rejects the supplied artifact, N:20 refuses to infer a behavioral postcondition from the name, and no redesign appears.
- **Hard error — none.** No unimplemented proposal is certified.

### O

- **A1 — PASS.** O:70–90 establishes that the sole direct field is `.0: [u32; 2]`, while `"tail"` and nested `.0[1]` violate the two literal guarantees.
- **A2 — FAIL.** O:9–16 certifies all stable releases from 1.70.0 through 1.97.1. O:47–55 infers rules for 1.70–1.74 from a 1.70 document and for 1.75 onward from 1.75 and 1.97.1 documents; O:57–65 likewise cites reference-validity and wrapping authority only at the endpoints. That is not release-by-release, version-matched verification and no compatibility premise is admitted. O:20–21 and O:67–68 otherwise make the correct contract/soundness distinction.
- **A3 — PASS.** O:5–7 rejects because changing the snapshot is forbidden, uses the actual implementation rather than inferred intent (O:67–68), and proposes no alternative.
- **Hard error — none.** The interval overclaim concerns implemented source, not an unimplemented proposal.

## Genuine rubric/authority ambiguities

1. **Effect of surplus scope claims on A2.** Read narrowly, A2 asks only whether the report distinguishes contract failure from UB and recognizes the valid nested `u32`; every report does that. `SCORER.md`, however, says a material Rust premise passes only with applicable version-matched authority, and the acceptance request asks for the strongest scoped result. I therefore counted an unsupported affirmative release scope as part of A2 and failed E, G, I, J, and O. Under a rubric that ignores surplus soundness certifications once the minimal nested-pointer proposition is shown, those five A2 cells would instead pass.
2. **How much exact-version citation counts as verification.** A:33 expressly reports an exact-1.97.1 recheck and links the material unsafe address/projection, validity/aliasing, and layout documents, so I accepted its endpoint-only 1.97.1 result even though some ancillary 1.97.1 facts are not separately linked. E merely asserts an exact-1.97.1 soundness check while its soundness citations are all 1.70; I did not treat that assertion as verification. The packet does not define a mechanical minimum citation set, so this boundary is judgment-sensitive.
3. **Tuple-field naming does not affect the outcome.** Some reports call the direct tuple field `0`; others call tuple fields anonymous. The source still indisputably has no direct declared field named `tail` and no direct field of type `u32`, while `[1]` is an array-element projection. Thus this terminology variation creates no scoring ambiguity for A1.
