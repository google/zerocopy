# Submitted Rust authority

Exactly one Rust proposition is supplied for this review:

- Rust 1.80.0 standard-library documentation for
  [`std::hint::unreachable_unchecked`](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety)
  states in its Safety section that reaching the function is undefined
  behavior. Its applicability is Rust 1.80.0 on every supported target and
  ordinary profile; the page states no narrower target or profile condition.
