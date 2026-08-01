# Mode P score

## Atom table

| Report | P1 | P2 | P3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | None |
| E | PASS | PASS | PASS | None |
| F | PASS | PASS | PASS | None |
| G | FAIL | PASS | PASS | None |
| H | PASS | PASS | PASS | None |
| I | PASS | PASS | PASS | None |
| J | PASS | PASS | PASS | None |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | None |
| M | PASS | PASS | PASS | None |
| N | PASS | PASS | PASS | None |
| O | PASS | PASS | PASS | None |

## Evidence and decisions

### A

- **P1 PASS:** It enumerates the complete constant and pointer obligations, proves `16`, array extent/initialization, zero field offset, 16-byte alignment, `as_ptr`, and the live receiver-borrow interval for `Page`. For generic `first`, it gives the exact conditional premises C1 (initialized/read-permitted bytes) and C2 (the interval survives through the load), concludes the proof under them, and says the published prose otherwise leaves the result `UNPROVED`, not `UNSOUND`.
- **P2 PASS:** It states that downstream implementations and unsafe consumers may rely on every clause and that local search cannot narrow that public boundary.
- **P3 PASS:** It limits 1.x work to proof documentation/private reasoning or a parallel API that preserves `Block`, and reserves sealing, weakening, removal, signature changes, and replacement for an authorized 2.0.
- **Hard error: none.** The redesign is expressly a preferred future design, and the report says implemented 2.0 source would need a fresh audit.

### B

- **P1 PASS:** It explicitly adopts the operational reading that the 16 bytes are initialized and readable through the receiver-borrow interval, then proves all of `Page`'s clauses and shows `first` consumes only initialized byte zero with `u8` alignment one.
- **P2 PASS:** It says unknown downstream consumers can use every guarantee and unknown implementations were admitted under the old obligations; neither side can be inferred away by repository search.
- **P3 PASS:** It identifies proof comments and a private one-byte lemma as compatible 1.x simplifications, while retaining the legacy API and placing capability splitting/removal in an authorized 2.0.
- **Hard error: none.** The 2.0 section is a design proposal and explicitly requires re-auditing adapters and implementations.

### C

- **P1 PASS:** It lists the five implementer obligations, proves each for `Page`, explicitly reads `readable` as initialized storage valid for shared reads for the stated interval, and derives the immediate one-byte load in `first`.
- **P2 PASS:** It expressly treats downstream implementations and consumers as an open quantified boundary and rejects repository search as authority to narrow it.
- **P3 PASS:** It separates local proof factoring/additive migration surfaces that retain `Block` from sealing, weakening, removal, new required items, and changing `first`, all of which it assigns to 2.0.
- **Hard error: none.** It says no edit is authorized and frames the reference-returning capability and adapter as a possible migration, not a proved implemented artifact.

### D

- **P1 PASS:** It gives a complete `Page` derivation for the constant, representation, alignment, contiguous initialized array, `as_ptr`, non-nullness, and borrow duration. It normalizes `readable` operationally to initialized bytes that can be read on normal return and proves `first`'s immediate aligned load.
- **P2 PASS:** It explains separately how weakening harms downstream consumers and changing duties harms downstream implementations, neither of which local search enumerates.
- **P3 PASS:** It allows only local proof simplification and a parallel API in 1.x, while explicitly requiring 2.0 for reduced extent/alignment, changed items or interval, and safe/reference-based replacement.
- **Hard error: none.** All redesign language is prospective and conditional on explicit major-version authorization.

### E

- **P1 PASS:** It proves `Page` against B1-B5. For `first`, it precisely identifies the two unresolved implications—initialized/read-permitted byte zero and an interval covering the post-return dereference—and supplies a complete conditional proof without manufacturing an unsoundness verdict.
- **P2 PASS:** It says known local use is non-exhaustive and that both downstream consumer guarantees and implementer compatibility constrain 1.x.
- **P3 PASS:** It preserves the old trait/function in 1.x while distinguishing proof comments and a parallel safe API from sealing, strengthening, weakening, changing bounds, and removal, which it places in 2.0.
- **Hard error: none.** It calls the replacement a proposed major-version design and requires audit of the implemented replacement.

### F

- **P1 PASS:** It explicitly conditions `first` on `readable` meaning live, initialized, provenance/access-permitted bytes without aliasing violations, identifies that as the smallest missing proposition otherwise, and proves the complete `Page` provider contract and one-byte consumer projection.
- **P2 PASS:** It states that unknown downstream consumers and implementations require the entire published theorem despite the repository-only usage result.
- **P3 PASS:** It confines 1.x to equivalent documentation, an internal lemma, or an additive API preserving the old one, and assigns weakening, strengthening, sealing, signature/layout changes, and removal to authorized 2.0 work.
- **Hard error: none.** Its redesign is described as a future endpoint and staged migration, not a current audited artifact.

### G

- **P1 FAIL:** The `Page` half is complete: it covers `ALIGN`, zero field offset, raised alignment, `as_ptr`, non-nullness, initialized extent, and lifetime. The generic `first` half, however, merely says that the contract's undefined `readable` term plus the UB rules “permits `*p`” and that every possible byte is valid. It never states that `readable` is being operationally interpreted to entail initialization and alias/data-race-safe read permission, nor conditions the proof on that implication. Its only ambiguity branch concerns whether “during the borrow” survives method return. The cited UB rules identify forbidden cases; they do not positively establish the missing premise for an arbitrary implementation.
- **P2 PASS:** It says the public contract must remain intact because downstream consumers and implementers cannot be bounded by the repository search.
- **P3 PASS:** It distinguishes local proof/comments and independent additive APIs from sealing, strengthening, reducing extent/alignment, changing bounds, and removal requiring 2.0.
- **Hard error: none.** The capability split is explicitly an authorized-2.0 proposal, and the report says the implemented snapshot would require a fresh audit.

### H

- **P1 PASS:** It proves every `Page` obligation, including initialized readable extent and the full receiver-borrow interval. For `first`, it explicitly treats the postcondition as ruling out dangling, unaligned, and uninitialized access, and separately warns that initialization/provenance/interference wording is a contract change if not already meant by `readable`; this is an acceptable operational/conditional treatment.
- **P2 PASS:** It expressly identifies both unknown consumer reliance and unknown implementer obligations and rejects local search as closure.
- **P3 PASS:** It permits narrow local proof use and additive APIs in 1.x, but reserves narrowed guarantees, stronger duties, removal, and the shown safe-trait replacement for a major release.
- **Hard error: none.** The code is labeled a preferred 2.0 design, said to require authorization, and any implemented candidate is to be audited anew.

### I

- **P1 PASS:** It explicitly defines `readable` as permission for initialized non-atomic loads without lifetime, aliasing, or race UB, proves all `Page` clauses, and derives `first`'s aligned byte-zero load. Later-version coverage is transparently conditional on a named non-Reference premise and left unproved if that premise is rejected.
- **P2 PASS:** It states that weakening breaks unknown consumers and strengthening breaks unknown implementations; local ecosystem search proves neither absent.
- **P3 PASS:** It separates comments/internal refactoring/parallel API work from sealing, extent/alignment changes, changed bounds, and removal requiring explicit breaking authority.
- **Hard error: none.** The migration API is prospective, and the report expressly requires a fresh audit of any implementation.

### J

- **P1 PASS:** It states the ordinary operational meaning of `readable`—live allocation, initialized consecutive bytes, and permitted reads for the receiver borrow—and says a weaker meaning leaves `first` unproved. It then fully proves `Page` and the immediate one-byte load.
- **P2 PASS:** It explicitly uses the open-world consumer/implementer argument and rejects local search as evidence for either narrowing or strengthening.
- **P3 PASS:** It permits proof comments/private wrappers and an opt-in parallel surface while reserving contract reduction, safe-trait conversion, required items, changed bounds, and removal for 2.0.
- **Hard error: none.** Both alternatives are described as designs requiring authorization and a fresh audit.

### K

- **P1 PASS:** It proves every `Page` clause and precisely leaves `first` conditional on `readable` entailing initialization, a live/access-permitted interval, and race-free loading. Its `MaybeUninit` discussion is explicitly a countermodel to an implication, not a claimed valid-use UB witness or `UNSOUND` verdict.
- **P2 PASS:** It states that unknown downstream consumers may use the whole theorem and unknown implementations prevent retroactive strengthening.
- **P3 PASS:** It limits 1.x to proof factoring or an additive interface retaining `Block`, and assigns stronger or weaker contracts, safe/reference replacements, sealing/removal, and layout change to 2.0.
- **Hard error: none.** It recommends a migration but does not certify source that does not exist.

### L

- **P1 PASS:** It proves the full `Page` provider contract. It makes the `first` proof conditional on the explicitly identified implication that `readable` supplies live provenance, initialized bytes, and permitted loads for the receiver-borrow interval.
- **P2 PASS:** It says downstream implementations owe the complete current obligation and downstream consumers may rely on all guarantees, so repository search cannot narrow either set.
- **P3 PASS:** It identifies an internal one-byte lemma and equivalent proof text as 1.x work, while requiring authorized 2.0 for reduced extent/alignment, stronger duties, removal, and changed unsafe boundary.
- **Hard error: none.** The safe value/reference alternatives are choices for a future v2 based on requirements, not certified implementations.

### M

- **P1 PASS:** It proves B1-B5 for `Page` and gives the smallest exact missing implication for generic `first`: byte zero must be initialized and its non-atomic load permitted throughout the stated interval. It supplies the proof once that existing-contract meaning is established and does not claim a UB counterexample.
- **P2 PASS:** It explicitly preserves guarantees for unknown consumers and obligations for unknown implementations rather than relying on local search.
- **P3 PASS:** It separates proof comments/private helpers and a parallel deprecated migration lane from contract/layout changes, stronger duties, changed bounds, and removal requiring 2.0.
- **Hard error: none.** The sample `FirstByte` code is explicitly a preferred major-version design, and the implemented snapshot is said to need a fresh audit.

### N

- **P1 PASS:** It explicitly expands `readable` to its adopted operational meaning—live, allocated, initialized storage valid for reads—then proves the complete `Page` implementation and `first`'s immediate byte-zero load with `u8` alignment one. It leaves post-1.70 coverage conditional rather than back-projecting later documentation.
- **P2 PASS:** It states that unknown generic consumers may rely on every clause and that strengthened obligations may invalidate unknown implementations.
- **P3 PASS:** It permits a smaller local proof and an additive safe lane while preserving legacy `Block`; weakening, strengthening, changed signatures, and removal are assigned to an authorized 2.0.
- **Hard error: none.** The redesign is staged prospectively and explicitly calls for re-auditing the implemented snapshot.

### O

- **P1 PASS:** It proves all `Page` clauses and precisely identifies the missing generic-`first` implication: after `base` returns, byte zero must be live, initialized, and non-atomically readable without alias/race UB while the particular receiver borrow remains live. It proves `first` conditionally and expressly declines an `UNSOUND` verdict.
- **P2 PASS:** It says the repository result cannot enumerate downstream consumers or implementations and explains why neither provider guarantees nor implementer duties can be changed in 1.x.
- **P3 PASS:** It allows equivalent proof documentation and a separate opt-in API while preserving the legacy surface, and places narrowing, strengthening, changed bounds, and removal in an authorized 2.0 migration.
- **Hard error: none.** The replacement and separate raw capability are proposed future designs, with a fresh audit required after implementation.

## Ambiguities

1. The source's phrases `readable` and `during the borrow` are genuine contract-authority ambiguities. The rubric expressly permits either an explicit operational meaning or a conditional proof that names the missing implication. A, E, K, M, and O take the latter route; B, C, D, F, H, I, J, L, and N state or combine the former with a conditional caveat. G addresses the temporal ambiguity but leaves the separate initialization/access implication unstated, which is why only its P1 fails.
2. The open-ended `Rust 1.70+` range cannot be proved for future releases from 1.70 text. Every report either makes later coverage conditional on an explicit compatibility premise or leaves it unresolved. Under the scorer instruction allowing appropriately unresolved Rust premises, this does not independently fail P1.
3. C sketches a possible adapter from `Block` to a safe reference-returning trait. Whether the old word `readable` is strong enough to justify creating a shared reference (rather than one raw load) would need separate authority and an implementation audit. I did not classify this as certification: C says no edit is authorized, presents it as a migration possibility, and does not give the hypothetical artifact a proved/current verdict. This is the closest proposal-certification boundary in the packet, but it does not meet the hard-error rule as written.

No other genuine rubric ambiguity affects the atom or hard-error decisions.
