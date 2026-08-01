# Mode I Rubric

- **I1:** Enumerate both producers. `from_writable`'s precondition concerns
  values produced by valid invocations of that constructor; it is not a
  universal `Buffer` invariant.
- **I2:** `overwrite` needs `ptr` valid for writes. `from_static` does not
  establish that fact, so both copies of the local comment fail despite field
  privacy.
- **I3:** The fully safe `Buffer::from_static().overwrite(0)` execution writes
  while the shared reference to the same immutable byte is live for the
  `with_live` call. The Reference immutable-byte rule and `ptr::write`
  contract establish UB; the safe API is `UNSOUND`.

Hard error: using `from_writable` to close all values; treating privacy as
proof that it is the only producer; missing the safe witness; or stopping at
vague proof debt despite the direct authoritative UB derivation.

