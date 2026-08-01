# Mode I blind score

## Atom table

| Report | I1 | I2 | I3 | Hard error |
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

I1 requires both producers and constructor-specific treatment of `from_writable`'s contract. I2 requires the write-validity obligation, its failure for `from_static`, and rejection of both local comments. I3 requires a wholly safe witness and an authoritative Rust 1.80 UB derivation, or an explicitly equivalent derivation. The hard-error column was decided independently from the atom columns.

## Report-by-report evidence

### A

- **I1 — PASS:** “The current producer set is exhaustive” names unsafe `from_writable` and safe `from_static`; states W and S are separated, and the W result is expressly conditional on `from_writable`'s ongoing caller contract.
- **I2 — PASS:** The ledger says `from_static` establishes S, not W, and the `Some` arm is unsound. Finding F2 calls the `Some` comment false and the `None` comment incomplete because it omits alignment and the state-to-producer bridge.
- **I3 — PASS:** It gives the entirely safe `from_static(); overwrite(0)` witness and cites exact Rust 1.80 liveness, shared-reference immutability, nonzero mutation, `ptr::write`, and one-byte-`u8` rules before concluding UB and `UNSOUND`.
- **Hard error — None:** It does not universalize `from_writable` or rely on privacy alone; it includes the safe witness and completes the authoritative UB derivation.

### B

- **I1 — PASS:** The producer table separately lists `from_writable` as producing `None` under its continuing unsafe-caller obligations and `from_static` as safely producing `Some(&BYTE)`.
- **I2 — PASS:** It says `from_static` creates the state behind the unsound consumer, identifies write validity and alignment as `ptr::write` requirements, rejects the `Some` comment as false, and rejects the `None` comment as missing the producer/privacy bridge and alignment.
- **I3 — PASS:** The safe `from_static(); overwrite(9)` witness is followed by exact Rust 1.80 `ptr::write` and Reference liveness/immutable-byte reasoning, yielding UB and an `UNSOUND` verdict.
- **Hard error — None:** Both producers, the safe witness, and a direct authoritative derivation are present; privacy is used only with an exhaustive producer inventory.

### C

- **I1 — PASS:** The boundary inventory names the sole unsafe producer and sole safe producer, then O1 limits `from_writable`'s result to calls satisfying its documented unsafe-caller obligations.
- **I2 — PASS:** It states the needed write-validity invariant, says `from_static` does not establish it, calls the `Some` comment false, and calls the `None` comment incomplete for omitting producer partition, alignment, and conflict facts.
- **I3 — PASS:** It supplies `from_static(); overwrite(9)` and explicitly derives same-byte identity, full-call reference liveness, a one-byte overlapping mutation, UB, and safe-API `UNSOUND`, with exact Rust 1.80 sources.
- **Hard error — None:** It distinguishes both histories, does not use privacy as sole proof, and neither misses nor weakens the safe UB witness.

### D

- **I1 — PASS:** The surface inventory identifies exactly `from_writable` and `from_static`; the `None`-arm proof is explicitly only for a valid `from_writable` call satisfying the ongoing contract.
- **I2 — PASS:** It says the `Some` comment's `from_writable` premise is inapplicable and that `from_static` establishes the opposite needed fact; it separately calls the `None` comment proof-documentation deficient.
- **I3 — PASS:** It gives the entirely safe `from_static(); overwrite(0)` witness and derives UB from the exact Rust 1.80 immutable-static-byte rule plus `ptr::write`'s write-validity contract, concluding `UNSOUND`. This is an explicit equivalent treatment: immutable `static BYTE` alone closes the execution without needing the additional shared-reference-liveness route.
- **Hard error — None:** It audits both producers and supplies a concrete safe witness with a direct authoritative UB proof, rather than stopping at aliasing concern or proof debt.

### E

- **I1 — PASS:** The W/S inventory names both producers and confines the ongoing non-null/aligned/write-valid/non-conflict promise to state W created by valid `from_writable` use.
- **I2 — PASS:** The ledger says `from_static` establishes addressability and alignment but not write permission, marks the S write unsound, calls the S comment invalid, and calls the W comment deficient.
- **I3 — PASS:** It gives the safe `from_static(); overwrite(0)` execution and, using exact Rust 1.80 `ptr::write`, liveness/immutable-byte, and `u8`-size text, derives an overlapping write during `with_live`, UB, and `UNSOUND`.
- **Hard error — None:** The report neither closes all states through `from_writable` nor relies on privacy by itself, and it contains the required safe witness and complete derivation.

### F

- **I1 — PASS:** It explicitly partitions W (`None`, only `from_writable`) and S (`Some`, only `from_static`) and proves W only relative to the unsafe caller's ongoing contract.
- **I2 — PASS:** Its obligation table states `ptr::write` needs validity and alignment, proves the W branch conditionally, marks the S branch unsound, rejects the S comment as false, and rejects the W comment as missing the producer bridge and other conjuncts.
- **I3 — PASS:** `from_static(); overwrite(7)` is identified as wholly safe UB even when bits are unchanged; exact Rust 1.80 liveness, shared immutability, nonzero mutation, `ptr::write`, and `u8` layout close the result.
- **Hard error — None:** Both producer cases and the safe witness are explicit, and the finding goes beyond proof debt to authoritative UB.

### G

- **I1 — PASS:** The exhaustive invariant partition identifies W from `from_writable` and S from `from_static`; the W proof is expressly quantified only over calls satisfying the continuing unsafe contract.
- **I2 — PASS:** It states `ptr::write`'s validity/alignment requirements, marks S unsound, calls the `Some` comment false, and identifies the `None` comment's missing constructor-closure, alignment, and non-conflict reasoning.
- **I3 — PASS:** It supplies `from_static(); overwrite(0)` and derives same-byte identity, liveness throughout `with_live`, a one-byte mutation of shared-reference-protected storage, UB, and `UNSOUND` from exact Rust 1.80 authority.
- **Hard error — None:** Privacy is paired with complete producer inspection; the safe witness and direct UB proof are present.

### H

- **I1 — PASS:** Its table names both producers, and the text explicitly warns that the regional `from_writable` proof “cannot be reversed into an invariant of every `Buffer`” because `from_static` is a second producer.
- **I2 — PASS:** It states `ptr::write` needs write validity and alignment, establishes the `None` branch only conditionally, rejects the `Some` comment as false, and rejects the `None` comment for omitted alignment and dataflow.
- **I3 — PASS:** The safe `from_static(); overwrite(7)` witness is connected to same-byte pointer/reference identity, full-call liveness, immutable shared-reference bytes, a one-byte write, UB, and an overall `UNSOUND` verdict using exact Rust 1.80 pages.
- **Hard error — None:** It expressly avoids universal closure through `from_writable`, includes the safe witness, and proves rather than merely suspects UB.

### I

- **I1 — PASS:** The producer inventory names `from_writable` and `from_static`; the ledger proves the former only “for valid calls” under its ongoing obligations and treats fabricated states outside the safe-use theorem.
- **I2 — PASS:** It identifies validity/alignment/non-conflict at each write, says `from_static` creates the conflicting state, rejects the line-31 comment as false, and calls the line-38 comment deficient for missing producer/transition and alignment facts.
- **I3 — PASS:** Finding F-1 gives `from_static(); overwrite(0)` and exact Rust 1.80 liveness, immutable-byte, mutation, `ptr::write`, and `u8`-size premises, then concludes safe reachable UB and `UNSOUND`.
- **Hard error — None:** Both producers and both proof sites are treated; the witness and authoritative UB derivation are complete.

### J

- **I1 — PASS:** Its boundary table and W/S invariants enumerate both producers, with W carrying only the valid unsafe caller's continuing contract.
- **I2 — PASS:** It identifies write validity/alignment and non-conflict, says the S write cannot meet validity, rejects the S comment as inapplicable, and labels the W comment incomplete for missing the producer link and other obligations.
- **I3 — PASS:** F-1 supplies `from_static(); overwrite(0)` and stepwise derives full-call liveness, a positive-size same-byte write, immutable-byte mutation, failure of `ptr::write` validity, UB, and `UNSOUND` from exact Rust 1.80 documentation.
- **Hard error — None:** It uses privacy only as part of exhaustive representation closure and contains a concrete safe witness plus a completed UB proof.

### K

- **I1 — PASS:** The ledger names both constructors and distinguishes W from S; the W/`None` conclusion is explicitly relative to the valid unsafe-constructor contract.
- **I2 — PASS:** It says `from_static` does not establish W, marks the `Some` write unsound, rejects the line-31 implication, and rejects the line-36 comment for omitted alignment and producer derivation.
- **I3 — PASS:** It gives `from_static(); overwrite(0)` and exact Rust 1.80 same-location cast, liveness, shared immutability, nonzero mutation, `u8` size, and `ptr::write` support before concluding UB and `UNSOUND`.
- **Hard error — None:** The report enumerates both producers, supplies the safe witness, and closes UB directly rather than reporting vague proof debt.

### L

- **I1 — PASS:** It calls `from_writable` and `from_static` the complete producer set and limits the `None` proof to a valid `from_writable` call satisfying ongoing obligations.
- **I2 — PASS:** It states the exact `ptr::write` invariant, says the `Some` state never came from `from_writable`, calls its comment false, and calls the `None` comment incomplete for omitted alignment/conflict facts.
- **I3 — PASS:** It supplies the safe `from_static(); overwrite(9)` execution and exact Rust 1.80 pointer-identity, call-liveness, shared-byte immutability, one-byte mutation, and write-contract authority to establish UB and `UNSOUND`.
- **Hard error — None:** Both histories are independently analyzed; neither the safe witness nor the authoritative derivation is missing.

### M

- **I1 — PASS:** Its complete dataflow inventory names unsafe `from_writable` and safe `from_static`, and its W result remains conditional on the unsafe caller-maintained obligation rather than becoming universal.
- **I2 — PASS:** The ledger states the exact validity/alignment/non-conflict obligation, marks S unsound, rejects the `Some` comment because `from_writable` never occurred, and rejects the `None` comment for omitted closure and conjuncts.
- **I3 — PASS:** It gives `from_static(); overwrite(0)` and uses exact Rust 1.80 `core::ptr::write` and Reference liveness/immutable-byte/mutation rules to derive a same-byte live-reference conflict, UB, and safe-API `UNSOUND`.
- **Hard error — None:** Exhaustive producer reasoning accompanies privacy, and the safe witness receives a direct authoritative UB derivation.

### N

- **I1 — PASS:** Its two-state inventory names W from `from_writable` and S from `from_static`, with W's facts explicitly maintained by the valid unsafe caller throughout use.
- **I2 — PASS:** It applies `ptr::write` validity/alignment only to W, says the S obligation is false, calls the S comment materially false, and calls the W comment incomplete for alignment and the private-field/dataflow bridge.
- **I3 — PASS:** The safe `from_static(); overwrite(0)` witness is tied to same-location pointer conversion, `with_live` call liveness, shared-byte immutability, one-byte mutation, UB, and `UNSOUND` using exact Rust 1.80 sources.
- **Hard error — None:** It neither closes S through the unsafe contract nor stops at missing proof; the safe execution and authoritative UB result are explicit.

### O

- **I1 — PASS:** The boundary section enumerates both producers and the representation partition; the `None` result is expressly relative to `from_writable`'s caller contract.
- **I2 — PASS:** The ledger identifies `ptr::write` validity/alignment, marks the S write unsound, calls the `Some` comment materially false, and says the `None` comment omits alignment and the privacy/producer argument.
- **I3 — PASS:** It gives the entirely safe `from_static(); overwrite(7)` counterexample and derives pointer identity, full-call liveness, a one-byte mutation of shared-reference-protected storage, failed write validity, UB, and `UNSOUND` from exact Rust 1.80 documentation.
- **Hard error — None:** It audits both producers and both paths, does not treat privacy alone as proof, and includes the concrete safe witness and complete UB derivation.

## Rubric or authority ambiguity

No genuine ambiguity affects these scores. Report D uses the Rust 1.80 Reference rule that bytes owned by an immutable static are immutable (absent `UnsafeCell`) as its decisive UB route, while noting the live-reference aliasing concern. That is an explicit, version-matched equivalent to I3's shared-reference route, and `SCORER.md` expressly permits equivalent explicit reasoning. All other reports give the rubric's live-shared-reference route directly. No report depends materially on later documentation, implementation behavior, tests, project policy, Cargo metadata, or the rubric itself as a Rust axiom.
