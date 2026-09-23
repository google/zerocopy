# Submitted dependency surface

The exact resolved package is `peer-unsafe-dep` version 3.4.5. Its public
documentation supplies this declaration and contract:

```rust
/// Returns `value`.
///
/// # Safety
///
/// `value` must not equal zero.
pub unsafe fn duplicate_nonzero(value: u8) -> u8;
```

The dependency implementation, generated output, prior audit, and binary are
not present in the submitted snapshot. No assertion about what its function
body executes is supplied.
