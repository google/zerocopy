# Mode P blind adjudication

## Final atom table

| Report | P1 | P2 | P3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | None |
| E | PASS | PASS | PASS | None |
| F | PASS | PASS | PASS | None |
| G | **FAIL** | PASS | PASS | None |
| H | PASS | PASS | PASS | None |
| I | PASS | PASS | PASS | None |
| J | PASS | PASS | PASS | None |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | None |
| M | PASS | PASS | PASS | None |
| N | PASS | PASS | PASS | None |
| O | PASS | PASS | PASS | None |

**Tally:** 44/45 atoms pass; no hard errors.

`DISAGREEMENTS.md` makes G:P1 the only live cell. Every other atom and every hard-error decision is preserved exactly as agreed.

## Disputed cell: G:P1 — FAIL

G proves the complete `Page` side: `ALIGN = 16`; `repr(C)` puts the sole field at offset zero; `repr(align(16))` raises the containing alignment; `as_ptr` selects the live array buffer; and the `[u8; 16]` is initialized, non-null, 16-aligned, and live for the receiver borrow. G also expressly chooses the receiver-borrow interval and correctly says a shorter interval would leave `first` `UNPROVED`.

The generic-`first` derivation has a different, material gap. G says the contract supplies “readability,” then says A3 “consequently permits `*p`” and that every possible byte is a valid `u8`. It never states, for an arbitrary conforming `Block`, that it is operationally reading `readable` to entail an initialized byte and a non-atomic load permitted without aliasing or data-race UB; nor does it condition the proof on that implication. Its statement that `Page`'s initialized array is therefore readable proves only the `Page` direction, not the converse needed from the public prose for arbitrary implementers. “Every possible byte is a valid `u8`” addresses initialized `u8` bit patterns, not whether the memory contains an initialized value.

G's own A3 is summarized as forbidding dangling/misaligned loads and invalid produced values. The exact Rust 1.70 [undefined-behavior page](https://doc.rust-lang.org/1.70.0/reference/behavior-considered-undefined.html) also treats data races and aliasing violations separately and warns that its list is non-exhaustive. That authority verifies the negative rules G invokes; it does not establish the converse that eliminating G's listed cases positively permits the load. Supplying the missing contract-to-initialized/read-permitted implication during adjudication would violate the frozen rule against silently adding a material premise.

Thus G establishes `Page` and the temporal part of `first`, but not `first`'s current generic soundness. This is `UNPROVED`, not `UNSOUND`; the atom fails because P1 requires both conjuncts.

## Compact evidence for preserved cells

- **A:** P1 enumerates and proves the full `Page` contract and gives exact C1/C2 conditional premises for `first`; P2 preserves all clauses for unknown consumers/implementers; P3 keeps proof work and an additive lane in 1.x while reserving weakening/sealing/removal for 2.0. **Hard error: none**—the future design expressly needs a fresh audit.
- **B:** P1 explicitly reads `readable` as initialized read permission through the borrow and proves `Page` plus the one-byte load; P2 says local search cannot close either public side; P3 separates private proof factoring/additive runway from major contract changes. **Hard error: none**—the capability split is prospective and requires re-audit.
- **C:** P1 lists all five obligations, proves them for `Page`, and states the initialized/shared-read operational meaning used by `first`; P2 treats downstream implementers and consumers as open quantified sets; P3 retains `Block` for local/additive work and reserves changing it for 2.0. **Hard error: none**—C says no edit is authorized and offers only a migration possibility.
- **D:** P1 normalizes the contract to 16 initialized readable bytes for the live receiver borrow and proves both producer and one-byte consumer; P2 rejects repository search as authority over downstreams; P3 distinguishes local proof work from breaking extent, alignment, item, or boundary changes. **Hard error: none**—the replacement choices are future major-version options.
- **E:** P1 proves B1–B5 for `Page` and precisely conditions `first` on initialized read permission plus a post-return interval; P2 preserves the open public boundary; P3 retains the legacy surface for proof/additive work and assigns strengthening or weakening to 2.0. **Hard error: none**—the unimplemented replacement is explicitly subject to fresh audit.
- **F:** P1 proves `Page` and makes `first` conditional on a live, initialized, provenance/access-permitted, non-conflicting read; P2 states unknown downstream uses and impls prevent narrowing; P3 confines 1.x to equivalent proof/internal/additive work. **Hard error: none**—the safe method is a future endpoint, not a certified artifact.
- **G (agreed cells):** P2 says unknown consumers may use the full extent/alignment and unknown implementers prevent sealing or strengthening; P3 limits 1.x to proof/documentation and independent APIs and places capability splitting in 2.0. **Hard error: none**—G requires a fresh audit of any implemented 2.0 snapshot.
- **H:** P1's ledger proves `Page` and the load while expressly caveating any newly added initialization/provenance/interference duty; P2 covers both unknown public sides; P3 keeps narrow/additive 1.x work distinct from the shown 2.0 replacement. **Hard error: none**—the code is labeled a design sketch whose implemented form needs audit.
- **I:** P1 explicitly defines readable as initialized non-atomic load permission without lifetime, aliasing, or race UB and proves both sites; P2 preserves the open ecosystem contract; P3 distinguishes comments/internal/parallel work from breaking changes. **Hard error: none**—the migration artifact is prospective and requires fresh audit.
- **J:** P1 states the live-allocation, initialized-byte, permitted-read meaning and the weaker-meaning conditional, then proves `Page` and `first`; P2 covers consumer weakening and implementer strengthening; P3 separates compatible proof/additive work from 2.0 changes. **Hard error: none**—both designs are future and require fresh audit.
- **K:** P1 proves the strong `Page` contract and precisely leaves `first` conditional on initialization, live access, and race freedom without manufacturing unsoundness; P2 preserves every clause for unknown public parties; P3 reserves strengthening, weakening, sealing, and replacement for 2.0. **Hard error: none**—no edit is authorized and no absent code is certified.
- **L:** P1 proves `Page` and expressly identifies the live/provenance/initialized-load implication used conditionally by `first`; P2 states both downstream sets remain unknown; P3 permits an internal lemma/equivalent proof text while reserving contract reduction or strengthening for 2.0. **Hard error: none**—the safe alternatives are choices, not audited implementations.
- **M:** P1 proves every `Page` conjunct and gives the exact missing initialized, non-conflicting byte-zero implication and conditional closure for `first`; P2 protects unknown consumers and implementations; P3 keeps proof/additive migration work in 1.x and breaking changes in 2.0. **Hard error: none**—the sample is explicitly a proposed migration needing fresh audit.
- **N:** P1 explicitly expands readable into live, allocated, initialized read permission and proves the complete provider plus immediate load; P2 rejects local search for both public directions; P3 stages a safe additive lane while retaining legacy `Block` until 2.0. **Hard error: none**—the replacement remains prospective and must be re-audited.
- **O:** P1 proves the whole `Page` contract and precisely states the live-allocation, initialized-`u8`, alias/race-safe, post-return condition needed by `first`, then closes conditionally; P2 preserves unknown consumers and impls; P3 separates equivalent proof/additive work from authorized-major changes. **Hard error: none**—the preferred design is future work explicitly requiring fresh audit.

## Hard-error decisions

All A–O are **None**. Each report treats its changed API as a proposal, migration option, design sketch, or future major-version endpoint; none certifies an implemented replacement. Several expressly demand that implemented source receive a fresh audit. G's deficient proof of the current `first` is an atom failure, not the sole frozen hard error (“certifying an unimplemented proposal”).

## Genuine ambiguities

1. The source does not define whether “readable” entails initialization, provenance/access permission, alias/race freedom, or precisely which borrow interval survives `base`'s return. The rubric deliberately permits either an explicit operational reading or an exact conditional proof, so reports taking either complete route pass.
2. There is a real boundary between an operational reading and a conclusory assertion. No preferred vocabulary is required, but the report must actually state the missing implication or make the proof conditional on it. I resolve G on logical content: “A3 consequently permits `*p`” is the conclusion whose material premise is absent, not an operational definition of that premise.
3. Exact Rust 1.70 authority cannot prove an unbounded future `1.70+` range. The reports preserve this as a compatibility premise, cutoff qualification, or unresolved portion; under `SCORER.md`, that treatment is acceptable and does not alter the frozen cells.
