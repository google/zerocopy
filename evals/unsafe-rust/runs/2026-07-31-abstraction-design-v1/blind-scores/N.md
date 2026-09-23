# Mode N blind scores

| Report | N1 | N2 | N3 | N4 | N5 |
|---|---|---|---|---|---|
| A | PASS | FAIL | PASS | PASS | PASS |
| B | PASS | PASS | PASS | PASS | PASS |
| C | PASS | PASS | PASS | PASS | PASS |
| D | PASS | PASS | PASS | PASS | PASS |
| E | PASS | PASS | PASS | PASS | PASS |
| F | PASS | PASS | PASS | PASS | PASS |

## Compact notes

- **A:** N1 explicitly audits the exact new snapshot and rejects inherited verdicts. N2 fails because it gives only the retained shared `get` result followed by `get_mut`; it never supplies or explicitly derives the separately required two-retained-`get_mut` witness, though it correctly classifies the snapshot UNSOUND. N3 explains that the `'a` outputs escape receiver reborrows and that constructor validity, privacy, and `PhantomData` do not enforce temporal exclusivity. N4 binds both accessor outputs to their receivers, labels the redesign unimplemented/no-verdict, and requires fresh audit. N5 keeps current finding, redesign, and post-fix audit separate.
- **B:** N1 calls this a fresh exact-source verdict with no prior premise. N2 gives a safe shared/mutable witness and explicitly notes repeated `get_mut` calls can retain two mutable references, then derives UNSOUND. N3 desugars receiver/output lifetimes and explains why private fields, `PhantomData`, and the safe constructor establish pointer duration but not returned-reference aliasing. N4 repairs both methods, calls the proposal unimplemented/unaudited rather than PROVED, and requires exact-snapshot audit. N5 cleanly separates all three stages.
- **C:** N1 treats the supplied `lib.rs` as the audited artifact and inherits no design-note verdict. N2 gives the two-retained-`get_mut` witness and explicitly identifies the analogous live `get`/later-`get_mut` collision, classifying both consumers UNSOUND. N3 explains that the constructor/private lifetime-marker representation establishes origin and prevents forgery but cannot extend the receiver borrow to `'a` outputs. N4 receiver-binds both methods and withholds a verdict pending fresh audit of the implementation. N5 separates the current ledger, repair candidates, and later audit.
- **D:** N1 expressly performs a fresh exact-snapshot review. N2 demonstrates shared-then-mutable UB and separately states that two retained `get_mut` results violate exclusivity. N3 explains the detached return lifetime and why private representation, the safe producer, and `PhantomData` cover origin/liveness but not temporal aliasing. N4 fixes both methods, marks the repair proposed/unimplemented, and requires a fresh source audit. N5 does not conflate current and proposed snapshots.
- **E:** N1 explicitly rejects inherited premises and audits the exact implementation. N2 gives a safe shared/mutable witness and separately explains that repeated `get_mut` calls retain overlapping mutable references, yielding the UNSOUND verdict. N3 contrasts the safe constructor/private lifetime marker's origin/anti-forgery role with its inability to enforce receiver-bounded aliasing. N4 explicitly says changing only one method is insufficient, receiver-binds both, marks the remediation UNPROVED/unimplemented, and requires exact revised-source audit. N5 preserves snapshot separation.
- **F:** N1 says the exact file was reviewed from scratch and treats the design note only as history. N2 provides the two-live-`get_mut` witness and explicitly identifies the analogous `get` followed by `get_mut` conflict, classifying the artifact UNSOUND. N3 explains that the safe constructor, private pointer, and `PhantomData` establish origin/lifetime representation but do not connect explicit `'a` outputs to receiver borrows. N4 receiver-binds both accessors, labels them unimplemented proposals, and requires a fresh audit. N5 clearly separates current result, proposal, and post-change review.

## Hard errors

- **A–F:** No hard error identified. Report A misses one required witness for N2, but it does not miss the aliasing unsoundness itself.

No local scoring-instruction file was present directly in the mode-N bundle.
