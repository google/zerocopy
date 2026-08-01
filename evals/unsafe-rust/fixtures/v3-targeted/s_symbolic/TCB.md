# Accepted compatibility premise

## COMPAT-OPTION-184-186

- **Disposition:** accepted by the authorized human reviewer for this target.
- **Base authority:** the Rust 1.84.0 `Option::is_none` and
  `Option::unwrap_unchecked` standard-library pages.
- **Exact proposition:** for every released stable Rust toolchain `r` satisfying
  `1.84.0 <= r <= 1.86.0`, on every supported target and every supported Cargo
  profile, with either feature or debug-assertion state, Rust preserves these
  base propositions without weakening, qualification, or added precondition:
  (1) `is_none` returns true exactly for `None`; and (2)
  `unwrap_unchecked(Some(v))` returns `v`, while calling it on `None` is
  undefined behavior.
- **Consumers:** only the soundness and documented-result proofs for
  `value_or_zero`.
- **Excluded propositions:** this entry establishes neither the members of the
  release interval nor any fact about Cargo, another API, a compiler backend, or
  an emitted binary.
- **Re-audit trigger:** any change to the source, support interval, base
  propositions, feature/target scope, or human disposition.

No other compatibility or implementation premise is accepted.
