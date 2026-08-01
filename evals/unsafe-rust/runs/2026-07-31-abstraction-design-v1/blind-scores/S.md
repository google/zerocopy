# Mode S blind scores

| Report | S1 | S2 | S3 | S4 | S5 |
|---|---|---|---|---|---|
| A | PASS | PASS | PASS | FAIL | FAIL |
| B | PASS | PASS | PASS | FAIL | FAIL |
| C | PASS | PASS | PASS | PASS | FAIL |
| D | PASS | PASS | PASS | FAIL | PASS |
| E | PASS | PASS | PASS | FAIL | PASS |
| F | PASS | PASS | PASS | FAIL | PASS |

## Compact notes

- **A:** S1 gives a wholly safe external `Bytes` impl returning `(null, 1)` and derives UB in safe `last`. S2 explains that `#[doc(hidden)]` affects documentation, not visibility/implementability, and that prose cannot impose the missing safe-implementer invariant. S3 moves the seal, representation, implementations, and consumer into a genuinely private leaf, proves the controlled `Owned` producer, and rejects `pub(crate)` escape hatches. S4 fails because it never evaluates an `unsafe trait` alternative as viable but larger and dominated. S5 proves empty/final-byte behavior and identifies controlled producers/consumer, but fails to require a fresh audit of the exact implemented snapshot and instead certifies the sketch as PROVED.
- **B:** S1 supplies the safe forged raw-parts counterexample and traces the invalid load. S2 explicitly rejects doc hiding and comments as invariant enforcement. S3 gives a private leaf seal/representation boundary and requires each future built-in implementation there to prove its slice contract. S4 fails: it discusses making only `raw_parts` an unsafe method, not the viable-but-larger `unsafe trait` design required by the atom. S5 states `I-BYTES`, its owner/producers/consumer, and the exact empty/nonempty result, but does not demand a fresh post-implementation source audit and calls the redesign PROVED.
- **C:** S1 identifies the safe external null/length forgery and resulting pointer UB. S2 says doc hiding is not privacy and method prose cannot cure the safe boundary. S3 puts representation, genuine seal, implementations, and consumer in a private leaf and requires every future built-in to be proved there. S4 explicitly says an unsafe `Bytes` trait could express the obligation but exports an unnecessary larger proof burden when external implementations are not needed. S5 specifies the slice contract, controlled producer/consumer, and required result behavior, but fails the fresh exact-source post-change-audit requirement and improperly calls the unimplemented skeleton PROVED.
- **D:** S1 constructs the safe downstream bad impl and derives UB in `add`/dereference. S2 explicitly distinguishes `#[doc(hidden)]` from privacy or an unsafe obligation. S3 uses an unnameable private sealing trait, a leaf-private field, leaf-owned safe construction, and per-built-in controlled implementations; its `pub(crate)` constructor is checked leaf-owned construction, not invariant-bearing raw/sealing access. S4 fails because no unsafe-trait alternative or burden comparison is given. S5 preserves the exact empty/final-byte behavior, identifies the slice contract and controlled implementations/consumer, withholds a proposal verdict, and explicitly requires an exact post-implementation audit.
- **E:** S1 gives a safe external forged-parts witness and explains null-pointer UB in `last`. S2 says the hidden method remains public and that a safety comment cannot impose a hidden obligation on a safe implementer. S3 removes raw representation, makes sealing and representation leaf-private, and requires each controlled future impl to establish the local behavioral contract. S4 fails because it does not analyze making `Bytes` unsafe. S5 directly specifies empty/final-byte semantics, the leaf owner/producers/consumer, and a fresh audit of the implemented snapshot.
- **F:** S1 gives the safe bad implementation and traces its dangling raw access. S2 explicitly explains why doc hiding supplies neither privacy nor an implementer obligation. S3 provides a private leaf seal and representation, checked leaf-owned construction, the named `BYTES-VIEW` contract, and per-implementation proof. S4 fails because the unsafe-trait alternative and its larger burden are omitted. S5 proves the required behavior from the local view contract, identifies all controlled producers and the consumer, calls the sketch only a candidate, and requires exact-source post-implementation re-audit.

## Hard errors

- **A:** Certifies an unimplemented proposal as **PROVED**.
- **B:** Certifies an unimplemented proposal as **PROVED**.
- **C:** Certifies an unimplemented proposal as **PROVED**.
- **D, E, F:** No hard error identified.

No local scoring-instruction file was present directly in the mode-S bundle.
