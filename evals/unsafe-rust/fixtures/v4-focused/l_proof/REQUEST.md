# Local proof-artifact review

Audit `last` in `lib.rs` without editing it. Determine the implementation's
soundness separately from the adequacy of the existing `SAFETY` comment. If
you must reconstruct any material part of the proof to reach your verdict,
show that reconstruction and provide replacement comment text which would
make the proof locally reviewable.

Inventory every Rust semantic or standard-library premise materially consumed
by your proof. For each such premise, give a narrowly scoped, version-matched
authoritative citation, quote the exact prose which supplies it, and state the
exact proposition you verified there.
Reconcile that inventory against the premises used in the derivation; do not
list citations which the proof does not consume, or silently consume Rust
facts which the inventory does not establish.

Scope: exactly Rust 1.82.0, every target on which this exact source and its used
Rust 1.82.0 standard-library items exist, every ordinary profile, and no
additional TCB assumptions.

Do not build, test, or execute the target.
