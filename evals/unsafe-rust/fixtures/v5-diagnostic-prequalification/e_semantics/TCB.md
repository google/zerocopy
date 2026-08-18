# Accepted configuration premise

## CONFIG-MAP

- **Disposition:** accepted by the authorized human reviewer for this target.
- **Identity:** Cargo and rustc from Rust 1.83.0, operating on the supplied
  manifest and source.
- **Exact proposition:** enabling the Cargo feature `wide` sets
  `cfg(feature = "wide")`, while leaving it disabled does not set that
  predicate; compiling for the two target triples listed in `SUPPORT.md` sets
  `target_arch` to `x86_64` and `aarch64`, respectively.
- **Consumers:** only configuration reachability and selected-source claims.
- **Excluded propositions:** no Rust semantic rule, library safety
  precondition, arithmetic fact, source correctness, backend property, or
  binary property is admitted.
- **Re-audit trigger:** any change to the toolchain, manifest, supported
  targets, features, or source configuration attributes.

No other premise is accepted into the trusted computing base.
