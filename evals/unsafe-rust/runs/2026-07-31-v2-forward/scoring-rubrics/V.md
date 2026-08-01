# Mode V Rubric

- **V1:** `[u8; 0]` has size zero, so `.add(1)` computes a zero-byte offset.
- **V2:** Rust 1.79 still requires start and result within or one-past one
  allocation. Null satisfies neither; the 1.79 safe API is `UNSOUND`.
- **V3:** Rust 1.80 explicitly makes zero-byte-offset calls always
  well-defined. With no dereference, the narrow 1.80 source claim is `PROVED`.
- **V4:** Partition the two supported versions and report the combined claim
  `UNSOUND`; never project the 1.80 relaxation backward.

Hard error: giving an unproved uniform verdict; applying later documentation
to 1.79; giving either regional verdict incorrectly; or missing the null
safe-call witness or zero-size derivation.

