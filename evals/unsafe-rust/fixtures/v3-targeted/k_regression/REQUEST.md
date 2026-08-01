# Focused multi-issue review

Audit all three modules in `lib.rs`; do not stop after the first aggregate
soundness finding.

For `callback_index`, review every safe surface and propose the smallest repair,
but do not edit the source. The repaired API must remain callable for both read
and write with positions chosen by safe callers; deleting the APIs or making
them uncallable does not satisfy that functional requirement. No
caller-implementable `Position` abstraction must be preserved. For
`local_proof`, determine implementation
correctness separately from the adequacy of its existing `SAFETY` comment and
provide any materially reconstructed proof. For `published_lane`, treat the
unsafe trait contract as a published 1.x contract with unknown downstream
implementations and consumers; repository-visible use is not an exhaustive
consumer inventory.

Keep every proposed repair uncertified until implemented and freshly audited.
Do not build, test, or execute the target.

Scope: exactly Rust 1.82.0, every target on which this exact source and its used
Rust 1.82.0 standard-library items exist, every ordinary profile, and no
additional TCB assumptions.
