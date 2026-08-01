# Accepted build-tool premise

## BUILD-MAP-ORDERED

- **Disposition:** accepted by the authorized human reviewer for this target.
- **Identity:** Cargo 1.85.1 from the supported Rust 1.85.1 toolchain, operating
  on the supplied manifest, `build.rs`, environment interface, and library.
- **Exact proposition:** for every supported Cargo profile, Cargo executes this
  build script when required for the selected build. A successfully written
  `cargo::rerun-if-env-changed=FIXTURE_ALLOCATOR` line records that a later
  change in the raw value (including present-to-present changes) makes the
  prior selection stale and causes the script to run again before Cargo can
  select a library for the current build. Cargo interprets a successfully
  written `cargo::rustc-cfg=fixture_allocator="VALUE"` line from a build script
  that subsequently exits successfully by passing that exact key/value
  configuration option to this library compilation. Such a current library
  compilation receives exactly the `fixture_allocator` directives emitted by
  that successful current script execution and no retained selector from an
  earlier execution. Cargo does not compile the library when the build-script
  process exits unsuccessfully, even if stdout already contains one or more
  complete directive lines. It does not present a library from an earlier
  successful selector value as the result of the current stale, unsuccessful
  build. An uncaught panic of this exact build script's main thread is an
  unsuccessful process exit.

  Enabling `burst` sets `cfg(feature = "burst")`. Compiling for
  `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, or
  `wasm32-unknown-unknown` sets `target_arch` to `x86_64`, `aarch64`, or
  `wasm32`, respectively.
- **Execution scope:** successful-selector emission claims quantify over build
  attempts whose applicable stdout writes succeed and whose script returns
  successfully. An execution ending in a write failure or explicit panic
  produces no library compilation for that current build; any emitted prefix
  does not create a compiled configuration. Such an execution is not an
  accepted selector success, and an incidental write failure is not a new raw
  selector class.
- **Consumers:** only ordered build-output interpretation, freshness,
  allocator/feature/target reachability, selected source, and effective
  rejection for this target.
- **Excluded propositions:** no claim about which string the local build script
  emits or in which order, source correctness, Rust abstract semantics, a
  backend, or a binary is admitted.
- **Re-audit trigger:** any change to Cargo/toolchain identity, manifest,
  `build.rs`, environment interface, target set, source cfgs, or human
  disposition.

No other build-tool or implementation premise is accepted.
