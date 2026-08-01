# Supported configurations

This snapshot supports Rust 1.85.1 on these target triples:

- `x86_64-unknown-linux-gnu`;
- `aarch64-unknown-linux-gnu`; and
- `wasm32-unknown-unknown`.

Both states of the `burst` feature and both allocator models (`system` and
`arena`, selected as specified in `BUILD.md`) are supported, with exactly one
exclusion: `arena` is unsupported on `wasm32-unknown-unknown`, regardless of
the `burst` feature. The source must reject that excluded target/allocator
pair.

Every other combination of the listed target, feature state, and allocator is
supported in every Cargo profile, with either state of debug assertions.

