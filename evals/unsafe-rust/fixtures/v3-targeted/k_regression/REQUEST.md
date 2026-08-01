# Focused multi-issue review

Audit all three modules in `lib.rs`; do not stop after the first aggregate
soundness finding.

For `callback_index`, review every safe surface and propose the smallest repair,
but do not edit the source. For `local_proof`, determine implementation
correctness separately from the adequacy of its existing `SAFETY` comment and
provide any materially reconstructed proof. For `published_lane`, treat the
unsafe trait contract as a published 1.x contract with unknown downstream
implementations and consumers; repository-visible use is not an exhaustive
consumer inventory.

Keep every proposed repair uncertified until implemented and freshly audited.
Do not build, test, or execute the target.

Scope: exactly Rust 1.82.0, all targets and ordinary profiles, no additional
TCB assumptions.
