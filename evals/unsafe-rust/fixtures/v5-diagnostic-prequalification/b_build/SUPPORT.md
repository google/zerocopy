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

An allocator model is selected only by an accepted raw environment value from
`BUILD.md`. The rejected `arena-stop`, other-Unicode, and non-Unicode classes
are build-interface rejection cases, not additional allocator models or
supported library configurations. A build rejected by a build-script failure
or by the required wasm32/arena source error must not supply a current library
artifact to downstream users.
