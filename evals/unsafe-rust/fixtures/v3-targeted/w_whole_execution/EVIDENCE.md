# Submitted Rust authority

- Rust 1.80.0 standard-library documentation for
  [`std::hint::unreachable_unchecked`](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety)
  states in its Safety section that reaching the function is undefined
  behavior.
- Rust 1.80.0's
  [undefined-behavior chapter](https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html)
  is the controlling Reference section for the source-level undefined-behavior
  claim.

Both pages apply on every target in this target's declared domain on which the
exact source and item exist, and every ordinary profile. Open them and verify
the exact propositions used in the report.
