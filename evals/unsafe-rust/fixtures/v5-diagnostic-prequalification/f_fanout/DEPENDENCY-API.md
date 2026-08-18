# `peer-stage` 2.1.0 public API excerpt

```rust
/// Returns the next stage label, wrapping from `u8::MAX` to `1`.
///
/// The returned value is nonzero.
pub fn next_nonzero(value: u8) -> u8;
```

No implementation body, safety proof, build material, or artifact identity is
included in the supplied snapshot.
