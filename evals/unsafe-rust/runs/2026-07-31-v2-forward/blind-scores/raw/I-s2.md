# Mode I blind score

`PASS` means the report establishes every material proposition of the atom (including an explicitly permitted equivalent derivation). `None` means that none of the four listed hard-error classes applies.

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

## Report-by-report evidence

### A

- **I1:** The “Boundary, states, and obligation ledger” calls the producer set exhaustive, names unsafe `from_writable`/`None` and safe `from_static`/`Some`, and confines state W to calls “satisfying its ongoing documented contract.”
- **I2:** It cites `ptr::write`'s write-validity/alignment requirements, says S “not W,” marks the `Some` comment false, and marks the `None` comment's local proof documentation unproved because it omits alignment and the state-to-producer step. Thus it rejects both copies while separately reconstructing the W implementation proof.
- **I3:** It gives the safe `from_static(); overwrite(0)` witness and explicitly derives same-byte overlap, function-call liveness, shared-byte immutability, a nonzero `u8` write, UB, and aggregate `UNSOUND` from exact Rust 1.80 pages.
- **Hard error:** None. It does not universalize `from_writable`, does not make it the sole producer by privacy, includes the safe witness, and closes UB authoritatively rather than stopping at proof debt.

### B

- **I1:** The producer table enumerates `from_writable` and `from_static`; W is proved only “relative to that documented caller contract,” while S is separately tracked.
- **I2:** It states `write` needs validity and alignment, says `from_static` creates the unsound state, calls the `Some` comment false, and calls the `None` comment incomplete for omitting the privacy/producer bridge and alignment.
- **I3:** The safe witness is shown at the outset. The proof establishes same-address fields, liveness throughout `with_live`, one-byte overlapping mutation, UB, and `UNSOUND`, citing exact Rust 1.80 Reference and library contracts.
- **Hard error:** None: both histories remain distinct; privacy supports an exhaustive two-producer partition, and the report supplies the direct safe UB derivation.

### C

- **I1:** “Boundary and invariant inventory” names the sole unsafe producer and sole safe producer and limits O1 to valid `from_writable` calls satisfying ongoing obligations.
- **I2:** It identifies write-validity/alignment/nonconflict as the write invariant, says `from_static` does not establish it, rejects the `Some` comment as false, and rejects the `None` comment as incomplete despite reconstructing that branch.
- **I3:** Its displayed safe witness is followed by an explicit same-memory cast, call-liveness, shared-byte immutability, nonzero write, UB, and `UNSOUND` derivation using exact 1.80 authorities.
- **Hard error:** None; it neither closes S through W nor relies on privacy to erase S, and it gives the required witness and authoritative conclusion.

### D

- **I1:** The surface inventory explicitly lists both constructors and qualifies the `None` result as proved only for valid unsafe uses under `from_writable`'s contract.
- **I2:** AXIOM-2 supplies write validity/alignment. The report says `from_static` establishes the opposite needed fact, rejects its comment, and separately calls the `None` comment “proof-documentation deficient” for missing requirements and the producer derivation.
- **I3:** It gives the entirely safe witness and directly proves that the raw write mutates immutable `static BYTE`, citing the exact Rust 1.80 immutable-static rule and `ptr::write` contract. This is an explicit, stronger independent immutable-byte derivation and therefore qualifies under the scorer's equivalent-reasoning rule even though the report says alias-liveness is unnecessary.
- **Hard error:** None: both producers are retained, W is conditional, and the safe witness reaches direct authoritative UB rather than vague proof debt.

### E

- **I1:** The report enumerates state W from `from_writable` and state S from `from_static`, expressly tying W obligations to the unsafe caller.
- **I2:** Its ledger states the raw-write obligation, says S lacks write permission, labels the S comment invalid, and labels the W comment incomplete because it omits the producer bridge and alignment/conflict clauses.
- **I3:** It displays the safe witness and derives call liveness, same-byte overlap, target-independent one-byte mutation, UB, and `UNSOUND` from exact Rust 1.80 authority.
- **Hard error:** None; it does not conflate W and S and supplies the complete safe authoritative counterexample.

### F

- **I1:** The boundary inventory exhaustively records W from unsafe `from_writable` and S from safe `from_static`, with W explicitly conditional on the caller contract.
- **I2:** It quotes validity/alignment requirements, proves only W relative to the contract, says S is not writable, rejects the S comment, and rejects the W comment for omitting the producer bridge and alignment/conflict conjuncts.
- **I3:** The safe witness, live `&u8`, same `BYTE`, positive-size write, immutable-byte rule, UB, and `UNSOUND` verdict are all explicit and version-matched.
- **Hard error:** None; all four prohibited shortcuts are avoided.

### G

- **I1:** Its two-case invariant partition names both producers and limits W to the continuing obligations of the `from_writable` invocation.
- **I2:** It cites `ptr::write` validity/alignment, establishes that S violates the requirement, calls the S comment false, and calls the W comment incomplete despite privacy and conditional reconstructibility.
- **I3:** It supplies the safe witness and explicitly proves same byte, function-call liveness, one-byte mutation of shared-reference-immutable storage, UB, and aggregate unsoundness from Rust 1.80 sources.
- **Hard error:** None: privacy is used only with an exhaustive two-producer audit, and the required witness and direct derivation are present.

### H

- **I1:** The coverage table lists both constructors; it proves only the `from_writable`-originating path under that constructor's full ongoing contract and warns that this regional proof is not a universal invariant.
- **I2:** It states the raw write requirements, explains why S fails them, and expressly says “Both `SAFETY` comments” are rejected—the S premise is false and the W copy omits alignment and the `None => from_writable` dataflow fact.
- **I3:** It gives a complete safe witness and a versioned derivation through same-byte identity, liveness during the callback, immutable shared bytes, one-byte write, UB, and `UNSOUND`.
- **Hard error:** None; it explicitly avoids universalizing W and supplies the direct safe UB proof.

### I

- **I1:** The report calls the two-constructor set exhaustive and separately states that the `from_writable` theorem is conditional on valid invocations and ongoing caller obligations.
- **I2:** AX-WRITE gives validity/alignment; the ledger says S violates it, rejects the S comment as false, and marks the W comment deficient for its missing transition/producer and alignment proof.
- **I3:** F-1 is the safe witness, with explicit same-byte designation, function-call liveness, a one-byte overlapping mutation, UB, and `UNSOUND`, all grounded in exact 1.80 documentation.
- **Hard error:** None; the report distinguishes both producers and reaches the direct authoritative safe-code counterexample.

### J

- **I1:** The boundary table and W/S partition enumerate both producers and make W conditional on a valid unsafe call whose obligations remain active.
- **I2:** It quotes write validity/alignment, says S cannot satisfy validity, rejects the S comment, and calls the W comment incomplete for the producer link plus alignment/nonconflict omissions.
- **I3:** F-1 displays the safe witness and gives a numbered versioned derivation of same byte, call liveness, positive-size overlap, immutable-byte mutation, UB, and global `UNSOUND`.
- **Hard error:** None; it avoids all four listed hard-error modes.

### K

- **I1:** The ledger lists both constructors and confines W to valid `from_writable` calls and their temporal/no-conflict obligations.
- **I2:** It records `ptr::write` validity/alignment, says `from_static` does not establish W, calls the S comment false, and calls the W comment inadequate for missing alignment and the private-producer derivation.
- **I3:** The safe witness and four-step exact-version derivation establish same byte, liveness, nonzero immutable-byte mutation, failed write validity, UB, and `UNSOUND`.
- **Hard error:** None; the report neither erases S via W/privacy nor omits or weakens the safe UB proof.

### L

- **I1:** It enumerates the unsafe `None` and safe `Some` producers and proves the former path only for a valid call satisfying its ongoing contract.
- **I2:** It quotes validity/alignment, says mutability casting grants no write permission, rejects the S comment, and calls the W copy incomplete for omitted alignment/conflict and producer closure.
- **I3:** Its safe witness is followed by exact-version same-pointer, call-liveness, `u8`-size, shared-byte immutability, mutation, UB, and `UNSOUND` reasoning.
- **Hard error:** None; both producers and the direct safe counterexample are explicit.

### M

- **I1:** The “complete dataflow inventory” establishes stable W and S histories and limits W to the caller-maintained `from_writable` obligation.
- **I2:** AXIOM-WRITE states validity/alignment, the ledger says S's required proposition is false, and its row for “Both adjacent `SAFETY` comments” explicitly marks both invalid/inadequate for the precise required reasons.
- **I3:** It displays the safe execution and proves same byte, liveness throughout `with_live`, nonzero immutable-byte mutation, UB, and universal safe-API `UNSOUND` using exact Rust 1.80 axioms.
- **Hard error:** None; it avoids every listed hard-error condition.

### N

- **I1:** Its two-state coverage lists both producers and makes W depend only on valid invocations whose documented obligations continue to hold.
- **I2:** It cites raw-write validity/alignment, says S's obligation is false, rejects the S comment, and labels the W comment incomplete for missing alignment and private-field dataflow.
- **I3:** The safe witness and exact-version derivation establish identical location, call liveness, one-byte overlap, shared-reference immutability, UB, and aggregate `UNSOUND`.
- **Hard error:** None; no W universalization/sole-producer shortcut occurs, and the safe authoritative witness is complete.

### O

- **I1:** The boundary and representation partition enumerate `from_writable`/`None` and `from_static`/`Some`, with the former expressly relative to its unsafe caller contract.
- **I2:** Its ledger gives validity/alignment, says safe S cannot meet the write requirement, calls the S comment materially false, and says the W comment also omits alignment and the privacy/producer argument.
- **I3:** It supplies the complete safe witness and a numbered exact-version derivation of cast identity, call liveness, one-byte shared-reference-immutable mutation, failed write validity, UB, and `UNSOUND`.
- **Hard error:** None; both histories are preserved and the report provides the required direct safe UB proof.

## Rubric / authority ambiguities

- **No outcome-changing authority ambiguity.** Every material UB premise used for the scores is tied by the reports to Rust 1.80.0 Reference or standard-library documentation.
- Report D deliberately closes UB through the Reference's independently sufficient immutable-`static` rule and says the live-alias route is unnecessary. Because `SCORER.md` explicitly permits equivalent explicit reasoning, I score I3 `PASS`; this is not treated as vague proof debt.
- Report A's displayed `lib.rs` SHA-256 omits the final `a` from the packet source's digest. The rubric has no snapshot-hash atom or corresponding hard error, and A's substantive source analysis matches the supplied file, so this clerical mismatch does not alter I1–I3 or create a listed hard error. The instructions do not specify a separate penalty for such an out-of-atom discrepancy.
