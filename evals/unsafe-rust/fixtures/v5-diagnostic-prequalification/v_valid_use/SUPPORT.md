# Review scope

The library snapshot and downstream examples are scoped to Rust 1.83.0,
edition 2021. All targets and profiles supported by that toolchain are in
scope. There are no build scripts, generated sources, conditional
compilation attributes, dependencies, or accepted TCB entries.

`caller_examples.rs` is a supplied downstream-crate fragment. It is not part
of the library crate and has no privileged access to the library.
