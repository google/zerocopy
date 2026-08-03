# Accepted build-tool premise

## BUILD-MAP-POLICY

- **Disposition:** accepted by the authorized human reviewer for this target.
- **Identity:** the toolchain-bundled Cargo releases corresponding exactly to
  supported Rust 1.84.0, 1.85.0, and 1.86.0, operating on the supplied
  `Cargo.toml` and source.
- **Exact proposition:** for each supported release and every supported Cargo
  profile, enabling the named Cargo feature `turbo` or `hardened` sets the
  corresponding `cfg(feature = "...")` predicate for this library compilation,
  while leaving it disabled does not set that predicate. Compiling for
  `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, or
  `wasm32-unknown-unknown` sets `target_arch` to `x86_64`, `aarch64`, or
  `wasm32`, respectively.
- **Consumers:** only configuration reachability and effective-rejection proofs
  for this target.
- **Excluded propositions:** no Rust semantic fact, source-branch correctness,
  compatibility outside the three exact releases, or backend/binary correctness
  is admitted.
- **Re-audit trigger:** any change to Cargo/toolchain identity, feature names,
  target set, manifest, source cfgs, or human disposition.

No other build-tool or implementation premise is accepted.
