# Accepted build-tool premise

## BUILD-MAP-X

- **Disposition:** accepted by the authorized human reviewer for this target.
- **Identity:** Cargo 1.85.1 from the supported Rust 1.85.1 toolchain, operating
  on the supplied manifest, `build.rs`, environment interface, and library.
- **Exact proposition:** Cargo executes the build script when required for the
  selected build; honors its `rerun-if-env-changed=FIXTURE_ALLOCATOR` directive
  when that environment value changes; and passes each emitted
  `cargo::rustc-cfg=fixture_allocator="..."` option to this library
  compilation. Enabling `burst` sets `cfg(feature = "burst")`. Compiling for
  `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, or
  `wasm32-unknown-unknown` sets `target_arch` to `x86_64`, `aarch64`, or
  `wasm32`, respectively.
- **Consumers:** only allocator/feature/target reachability and effective
  rejection for this target.
- **Excluded propositions:** no claim about which string the local build script
  emits, source correctness, Rust abstract semantics, a backend, or a binary is
  admitted.
- **Re-audit trigger:** any change to Cargo/toolchain identity, manifest,
  `build.rs`, environment interface, target set, source cfgs, or human
  disposition.

No other build-tool or implementation premise is accepted.
