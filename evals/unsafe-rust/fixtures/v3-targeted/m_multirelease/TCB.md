# Accepted TCB entries

## SEM-EMPTY-BLOCK-180-182

- **Category:** OUT-OF-BAND general Rust-semantics proposition.
- **Disposition:** accepted by the authorized human reviewer for this target.
- **Exact proposition admitted:** for every
  `v in {1.80.0, 1.80.1, 1.81.0, 1.82.0}`, every target on which the relevant
  Rust syntax exists, and every ordinary debug or release profile, a well-typed
  call that satisfies its caller obligations to a zero-parameter,
  unit-returning Rust function whose body is exactly `{}` has defined callee
  evaluation and returns `()`. Marking that function `unsafe` changes only the
  static caller obligation, not the admitted callee-evaluation or return
  semantics.
- **Consumers:** only the local proof for `acknowledge`; the consumer must
  independently verify that its exact function body is empty and connect that
  fact to this proposition.
- **Exclusions:** this entry does not assert that `acknowledge` is sound, does
  not describe any nonempty body, and establishes nothing about any pointer
  operation or other API.
- **Re-audit trigger:** any change to `V_ack`, the body of `acknowledge`, its
  signature, its documented contract, or the human disposition.

## COMPAT-COPY-180-182

- **Category:** OUT-OF-BAND compatibility proposition.
- **Disposition:** accepted by the authorized human reviewer for this target.
- **Base identity:** the Rust 1.80.0 `std::ptr::copy_nonoverlapping` page,
  primitive-data-layout section, `u8: Copy` implementation page, and `Copy`
  semantics page named in `EVIDENCE.md`.
- **Exact proposition admitted:** for each
  `v in {1.80.0, 1.80.1, 1.81.0, 1.82.0}`, every target on which the item
  exists, every ordinary debug or release profile, `T = u8`, and `count = 1`,
  Rust preserves without weakening, qualification, or added precondition all
  of these 1.80.0 propositions:
  (1) if `src` is valid to read one initialized `u8`, `dst` is valid to write
  one `u8`, both pointers are properly aligned, and the one-byte regions do not
  overlap, executing `copy_nonoverlapping(src, dst, 1)` satisfies its safety
  contract; and (2) on return it copies the source byte to the destination
  while leaving the source byte unchanged; and (3) `u8` has size 1, implements
  `Copy`, and has the documented `Copy` semantics, so this call copies exactly
  one byte without moving ownership from the source value.
- **Consumers:** only the soundness and documented-postcondition proofs for
  `copy_byte`.
- **Excluded operations:** this entry establishes nothing about `ptr::read`,
  `ptr::write`, `acknowledge`, or any other API.
- **Configuration scope:** for every release and target case above, every
  ordinary debug or release profile; no deployment or backend theorem.
- **Re-audit trigger:** any change to `V_copy`, the base proposition, the exact
  source call, its type/count, or the human disposition.

There is no entry other than `SEM-EMPTY-BLOCK-180-182` and
`COMPAT-COPY-180-182`.
