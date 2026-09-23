# Mode N blind adjudication

I resolved only the cells named in `DISAGREEMENTS.md`. Every other atom and every hard-error decision is preserved from the two blind scores.

## Final atom table

| Report | N1 | N2 | N3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | None |
| D | FAIL | PASS | PASS | None |
| E | PASS | PASS | PASS | None |
| F | PASS | PASS | PASS | None |
| G | PASS | PASS | PASS | None |
| H | FAIL | PASS | PASS | None |
| I | PASS | PASS | PASS | None |
| J | PASS | PASS | PASS | None |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | None |
| M | PASS | PASS | PASS | None |
| N | PASS | PASS | PASS | None |
| O | PASS | PASS | PASS | None |

## Decisive evidence for disputed cells

### A

- **N1 — PASS.** A freshly labels the exact snapshot `UNSOUND`, gives the safe retained-`get`/later-`get_mut` program, establishes same-pointer access and liveness through the final read, and expressly adds that repeated `get_mut` calls can produce two simultaneously usable `&'a mut T` values. A also invokes the well-typedness premise rather than omitting it: the results use `'a` rather than the receiver-borrow lifetime, so the receiver borrow may end while the result lives.
- **N2 — PASS.** A identifies the enabling defect as `&'a T` and `&'a mut T` “rather than” receiver-tied results. The raw pointer appears only in the separate same-pointee derivation; A does not diagnose raw-pointer presence alone as the enabling defect.
- **N3 — PASS.** A changes both outputs to `&T`/`&mut T`, explicitly says elision ties them to their receivers, and calls the change an unimplemented candidate with “no verdict” pending fresh audit.

These lifetime propositions are invoked in A and may therefore be checked rather than supplied. The exact [Rust 1.70 lifetime-elision rule](https://doc.rust-lang.org/1.70.0/reference/lifetime-elision.html#lifetime-elision-in-functions) says each elided parameter lifetime becomes distinct and assigns the receiver lifetime only to elided output lifetimes. It therefore verifies both A's diagnosis of the current explicit `'a` outputs and A's receiver-bound elided repair. This adds no missing report premise or derivation.

### D

- **N1 — FAIL.** D freshly reports `UNSOUND` and fully derives the shared/mutable witness. It does not identify the other required witness: two live mutable results from repeated `get_mut` calls. Its only relevant sentence says safe code can call “another method” while a mutable result remains live. That does not state that the next call is `get_mut` or that it produces the second mutable result. Instantiating the generic phrase as a repeated `get_mut` call would add the material witness derivation that D omitted.

### H

- **N1 — FAIL.** H freshly reports `UNSOUND` and fully derives the mixed shared/mutable witness in `conflict`. It never identifies two simultaneous results of repeated `get_mut`. The repair discussion's phrase “allowing reuse of the capability” explains why a consuming accessor could be useful, but it does not instantiate that reuse as two `get_mut` calls or derive the duplicate-mutable witness. The missing route cannot be inferred for H.

### O

- **N1 — PASS.** O freshly reports `UNSOUND` and completely derives the safe repeated-`get_mut` witness: two independent receiver loans, two `'a` results from the unchanged pointer, simultaneous liveness in `take_both`, and the exact Rust 1.70 `UnsafeCell` multiple-`&mut` rule. It also explicitly gives the mixed route twice: `get_mut` can follow `get`, and fixing only `get_mut` would still let an old `'a` shared result overlap a later mutable result.
- **N2 — PASS.** O expressly diagnoses that both accessors return stored `'a`, not the receiver-loan lifetime, and says `PhantomData` carries the original borrow but does not connect results to individual receiver loans. Raw-pointer presence is not offered as the enabling defect.

O invokes, rather than omits, the proposition that explicit `'a` outputs are unrelated to the elided receiver loans. The exact Rust 1.70 lifetime-elision text linked above verifies that proposition. Using that authority is permitted premise verification; it does not add a causal step or witness absent from O.

## Evidence for preserved cells and hard-error decisions

- **A — hard error none:** the repair is an “unimplemented candidate” with “no verdict” until an exact implementation is freshly audited.
- **B — N1/N2/N3 PASS; hard error none:** `collide` derives the mixed witness and the report expressly adds repeated `get_mut`; it identifies explicit `'a` outputs bypassing receiver elision; both replacement outputs are receiver-bound. The proposal is “unimplemented,” not `PROVED`, and requires fresh audit.
- **C — N1/N2/N3 PASS; hard error none:** C derives the mixed witness and expressly states the repeated-mutable route; it distinguishes struct `'a` from the receiver lifetime under Rust 1.70 elision; both repairs explicitly use receiver `'s`. The proposal has no verdict until implemented and re-audited.
- **D — N2/N3 PASS; hard error none:** D identifies explicit `'a` outputs rather than receiver lifetimes and cites the exact Rust 1.70 rule; both repaired outputs are receiver-elided. The patch is `UNIMPLEMENTED / UNPROVED` and must be re-audited.
- **E — N1/N2/N3 PASS; hard error none:** E derives repeated `get_mut` aliases in `touch` and separately the retained-shared route; it writes the effective receiver-`'s`/output-`'a` signature; both proposed outputs explicitly use `'s`. The proposal is unimplemented and unaudited.
- **F — N1/N2/N3 PASS; hard error none:** F derives the mixed witness and its obligation ledger expressly adds repeated mutable aliases; it expands both effective signatures and attributes the defect to `'a` outputs; both outputs are repaired. The candidate is `UNIMPLEMENTED and UNPROVED` pending fresh audit.
- **G — N1/N2/N3 PASS; hard error none:** G derives repeated mutable aliases through `clash` and expressly gives the retained-`get` analogue; it distinguishes the receiver lifetime from explicit `'a`; both outputs become receiver-bound. Both candidate designs are `UNIMPLEMENTED / NOT AUDITED`.
- **H — N2/N3 PASS; hard error none:** H says both outputs use `'a`, not the receiver-borrow lifetime, under exact Rust 1.70 authority; both repairs use receiver-elided outputs. All candidates receive no verdict and require fresh audit.
- **I — N1/N2/N3 PASS; hard error none:** I derives two `get_mut` results in `use_both` and expressly names the analogous mixed route; it identifies the independent receiver and impl lifetimes; both repair variants use receiver-bound outputs. The repair is unimplemented and must be freshly audited before `PROVED`.
- **J — N1/N2/N3 PASS; hard error none:** J derives repeated mutable results in `collide` and explicitly gives the analogous mixed route; it attributes both failures to outputs not tied to receiver borrows; both signatures are repaired. The proposal is not implemented and receives no verdict pending full review.
- **K — N1/N2/N3 PASS; hard error none:** K derives repeated mutable aliases through `write_both` and separately identifies retained `get` versus later `get_mut`; it identifies distinct receiver and `'a` result lifetimes; both outputs are changed. The candidates are expressly not audited or `PROVED`.
- **L — N1/N2/N3 PASS; hard error none:** L derives the mixed witness and expressly says successive `get_mut` calls yield coexisting aliases; it identifies `'a` as unrelated to the receiver lifetime; both repairs are receiver-bound. The proposal is `UNIMPLEMENTED / UNPROVED AS SOURCE` pending fresh review.
- **M — N1/N2/N3 PASS; hard error none:** M fully derives two mutable results in `duplicate` and expressly gives the analogous mixed route; it writes the effective receiver-`'s`/output-`'a` signature; both repaired outputs explicitly use `'s`. The change is an unproved proposal requiring implementation and fresh review.
- **N — N1/N2/N3 PASS; hard error none:** N fully derives the mixed witness and expressly adds repeated `get_mut`; it displays both effective signatures with independent receiver lifetimes and `'a` outputs; both repairs are receiver-elided. The proposal is unimplemented, not `PROVED`, and requires implementation audit.
- **O — N3 PASS; hard error none:** O changes both signatures to explicit receiver/output `'s`, requires both changes, and labels the proposal `UNPROVED` until implemented and re-audited as a new artifact.

Thus no report certifies an unimplemented proposal, so the hard error applies to none of A–O.

## Genuine rubric ambiguity

N1 names “both safe alias witnesses” without specifying how much of the second derivation may be expressed by shorthand. Under `SCORER.md`, a second code block and duplicated UB proof are not required: an explicitly named analogous route passes when the already-stated lifetime, pointer-identity, liveness, and alias-rule reasoning covers it. But a generic phrase such as “another method” or “capability reuse” does not identify the repeated-`get_mut` route. This distinction follows the frozen prohibition on inferring a material premise and produces D/H `FAIL` without imposing a formatting preference.

The phrase “the report verifies” could, in isolation, be read to require an inline report citation for every Rust premise. The controlling adjudication instruction resolves that issue here: exact external authority may verify a premise the report invokes, but may not add one it omitted. A and O explicitly invoke the relevant lifetime relationship, so the exact Rust 1.70 text verifies it; D and H omit a witness derivation, which authority cannot supply. No other genuine ambiguity changes a cell.
