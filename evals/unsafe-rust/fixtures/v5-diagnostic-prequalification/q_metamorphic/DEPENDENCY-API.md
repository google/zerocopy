# `peer-text` 3.0.0 public API excerpt

```rust
pub unsafe trait AsciiDecoder {
    /// Decodes an ASCII byte slice.
    ///
    /// # Safety
    ///
    /// Every byte in `bytes` must be ASCII. For this contract, a byte is ASCII
    /// exactly when its numeric value is at most `0x7f`.
    unsafe fn decode_ascii(bytes: &[u8]) -> &str;
}

pub struct SelectedDecoder;
```

The selected package's public API metadata records that `SelectedDecoder`
implements `AsciiDecoder`. No method body, implementation proof, build
material, or artifact identity is included in the supplied snapshot.
