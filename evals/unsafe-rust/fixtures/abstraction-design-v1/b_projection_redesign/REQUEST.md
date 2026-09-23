# Redesign request

We own this unpublished internal abstraction and may change it freely. First
review the current implementation under its literal contract. Then propose the
simplest proof-oriented redesign.

The only required behavior is that `increment_tail(&mut Pair)` increments
`Pair.0[1]` with wrapping arithmetic. It must remain allocation-free, support
Rust 1.70+, every target, and every ordinary profile. Repository search found
no other consumer and no planned generic reuse. No source edit is requested in
this task; provide the design and proof plan.

