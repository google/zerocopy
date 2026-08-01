# Bundle P — blind raw scores

`1` means the full proposition is explicit; `0` means at least one conjunct is omitted.

| Report | P1 | P2 | P3 | P4 | P5 | Raw |
|---|---|---|---|---|---|---:|
| A | 1 — proves every `Page` clause and `first` for valid impls, with only interpretation/future-version qualifications | 1 — says downstream consumers and impls are unenumerable | 1 — expressly bars weakened guarantees, sealing, and stronger impl duties in 1.x | 1 — explicitly permits a private one-byte helper, retains the full audit, and reserves breaking replacement/split for authorized 2.0 | 1 — covers provider/impl/consumer directions, migration of both sides, proof effects, and major-release authorization | **5/5** |
| B | 1 — conditionally reconstructs the full `Page` and valid-impl `first` proofs without alleging UB | 1 — says repository search cannot bound downstream parties | 1 — preserves every guarantee and bars strengthened duties/sealing in 1.x | 0 — offers a narrower proof lemma and additive public API, but never explicitly offers a **private internal helper** | 1 — gives directional compatibility effects, adapters/audits, proof consequences, and an unauthorized-until-2.0 boundary | **4/5** |
| C | 1 — proves `Page` and `first` for valid implementations; documentation debt is kept distinct from implementation failure | 1 — explicitly rejects treating repository search as exhaustive | 1 — bars guarantee weakening, obligation strengthening, and sealing in 1.x | 0 — suggests comments and a public successor, but omits the private narrower-helper option | 1 — states both contract directions, migration/re-audit, proof consequences, and says the owner must choose the 2.0 capability | **4/5** |
| D | 1 — proves all provider clauses and conditionally proves `first`, explicitly declining an unsupported unsoundness finding | 1 — identifies unknown downstream consumers and impls | 1 — expressly preserves guarantees and bars new duties/sealing in 1.x | 0 — notes that an adapter cannot eliminate the old audit, but does not explicitly permit a private narrower helper | 1 — explains directional breakage, migration, safe-boundary proof effects, and requires authorized 2.0/product choice | **4/5** |
| E | 1 — proves the full `Page` contract and `first` for every conforming impl, with only the open-ended-version premise | 1 — says downstream impls/consumers are not enumerable | 1 — explicitly forbids weakening, sealing, and stronger implementer duties in 1.x | 1 — explicitly permits a private byte helper/capability while retaining `Block` and its audit, with split/removal only in authorized 2.0 | 1 — covers both contract directions, migration/audits, proof consequences, and the explicit major-release decision | **5/5** |
| F | 1 — proves `Page` and conditionally proves `first` for conforming impls, without converting ambiguity into a defect | 1 — explicitly says repository search cannot bound downstream reliance | 1 — bars guarantee weakening, sealing, and stronger impl duties in 1.x | 0 — narrows the consumer proof and gives 2.0 replacements, but omits an explicit private internal helper | 1 — assigns provider/consumer duties, gives migration and proof consequences, and requires a deliberate 2.0 choice | **4/5** |

## “Readable for 16 bytes” oracle issue

- **A:** Qualified but not declared too ambiguous: it explicitly adopts an operational meaning permitting initialized reads; it does not mark the published phrase itself UNPROVED.
- **B:** Explicitly flags the phrase as too imprecise to establish initialization, provenance, alias permission, and interval without an interpretation; its conditional proof is therefore not penalized.
- **C:** Does not flag the issue; it directly assumes “readable” supplies liveness and initialization.
- **D:** Explicitly flags all initialization/provenance/alias/data-race and temporal components and makes the proof conditional; not penalized.
- **E:** Does not flag the issue; it directly treats the phrase as supplying an initialized readable byte.
- **F:** Explicitly states the operational initialized-access reading and says `first` is UNPROVED if the publication meant less; not penalized.

## Hard errors

None detected in A–F. Every report rejects exhaustive treatment of known consumers, preserves the ordinary-SemVer/public commitment, separates current findings from 1.x maintenance and 2.0 proposals, avoids a proofless condemnation of current code, and does not mark an unimplemented redesign `PROVED`. No forbidden material was read.
