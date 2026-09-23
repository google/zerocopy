# Invariant-boundary redesign

Review the current safe API, then redesign its invariant boundary. External
implementations of `Bytes` are not required, and genuine sealing is authorized.
Preserve safe `last` behavior for supported built-in types: empty values return
`None`; nonempty values return the final byte. New code should use the smallest
practical leaf-module proof boundary and treat safe code outside it as
untrusted. Scope: Rust 1.70+, `std`, all targets/profiles. No edit is requested.

