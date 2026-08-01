# Audit result

No unsafe-code soundness or correctness findings.

- `item_unchecked` documents exactly the required precondition,
  `index < bytes.len()`, matching Rust 1.85's `slice::get_unchecked` contract.
- `checked_first` performs an unconditional emptiness check before
  `get_unchecked(0)`. It does not rely on a debug assertion, so the proof holds
  in every stated build profile.
- The remaining APIs use valid typed references, safe matching, copying, or
  bounds-checked indexing. `decode_flag` and `profile_index` can panic on
  invalid input, but cannot trigger undefined behavior.
- Callers can cause UB only by violating the clearly documented contract of
  the explicitly `unsafe` `item_unchecked` API.

The snapshot was reviewed statically only; it was not modified, built, tested,
or executed.
