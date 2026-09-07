<!-- Copyright 2025 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Validating Changes

This document covers the procedures and requirements for validating changes to
the project, including linting, testing, and pre-submission checks.

## Linting

Clippy should **always** be run on the `nightly` toolchain.

```bash
./cargo.sh +nightly clippy
./cargo.sh +nightly clippy --tests
```

### Strict Linting

- We deny warnings in CI. Even warnings not explicitly listed in `lib.rs` will
  cause CI to fail.
  - **Why:** We maintain a zero-warning policy so that new warnings (which often
    indicate bugs) are immediately obvious and not obscured by existing ones.
- Do not introduce new warnings.
- Respect the strict `deny` list in `src/lib.rs`.

## Validating Changes

Ensure the library builds on all supported toolchains and that Clippy passes.

```bash
./cargo.sh +msrv check --tests --features __internal_use_only_features_that_work_on_stable
./cargo.sh +stable check --tests --features __internal_use_only_features_that_work_on_stable
./cargo.sh +nightly check --tests --all-features
./cargo.sh +nightly clippy --tests --all-features --workspace
```

**Note:** Tests are rarely toolchain-sensitive. Running tests on `nightly` is
usually sufficient.

## Testing Strategy

- **Unit Tests:** Place unit tests in a `mod tests` module within the source
  file they test.
- **UI/Compile-Fail Tests:**
    - **`zerocopy`:** Place in `tests/ui-*` (top-level). The top-level `tests`
      directory contains *only* UI tests.
    - **`zerocopy-derive`:** Place in `zerocopy-derive/tests/ui-*`.
- **Derive Integration Tests:** Place integration tests for derive macros in
  `zerocopy-derive/tests`.
- **Derive Output Tests:** Place unit tests that verify the *generated code*
  (token streams) in `zerocopy-derive/src/output_tests.rs`.
- **Formal Verification (Kani):** Place Kani proofs in a `mod proofs` module
  within the source file they test.
    - **Purpose:** Use the
      [Kani Rust Verifier](https://model-checking.github.io/kani/) to prove the
      soundness of `unsafe` code or code relied upon by `unsafe` blocks. Unlike
      testing, which checks selected executions, Kani exhaustively checks a
      harness's modeled state space. That state space is limited by the
      harness's bounds and assumptions, its target and feature configuration,
      and Kani's model of Rust.
    - **How to Write Proofs:**
        - **Harnesses:** Mark proof functions with `#[kani::proof]`.
        - **Inputs:** Use `kani::any()` to generate arbitrary inputs.
        - **Assumptions:** Use `kani::assume(condition)` to constrain inputs to
          valid states (e.g., `align.is_power_of_two()`).
        - **Assertions:** Use `assert!(condition)` to verify the properties you
          want to prove.
        - **Oracles:** Prefer a safe Rust language or standard-library operation
          as the source of expected behavior. If no such oracle exists, isolate
          the manual oracle, state its normative basis, and explain both its
          independence from the code under proof and its limitations. If the
          predicate merely restates a zerocopy acceptance policy, label it as a
          policy oracle rather than evidence of Rust-level validity.
        - **Factoring:** Share repeated case generation, oracle construction,
          and postcondition checks within the proof module. Keep distinct
          harnesses when they exercise different entry points or contracts.
        - **Domain:** Document whether a proof is universal, target-specific,
          or bounded by a concrete allocation or collection size. State both
          what is covered and what is not covered.
        - **Non-vacuity:** Use `kani::cover!` to check that important input and
          result partitions are reachable. Every assumption must correspond to
          a documented precondition or to the stated proof bound. Do not reject
          inputs using an impossible assumption or a diverging loop.
        - **Bit validity:** `kani::any::<T>()` produces only valid instances of
          `T`. To verify a byte validator, generate arbitrary bytes and
          construct `T` only after the validator accepts them.
        - **Soundness boundary:** State which obligations Kani does not prove.
          In particular, Kani does not completely check reference aliasing,
          pointer provenance, invalid values, or uninitialized memory.
        - **Layout randomization:** `--randomize-layout` checks one randomized
          layout per run; it does not prove behavior for every layout or target.
    - **CI:** Kani runs in CI using the `model-checking/kani-github-action` with
      specific feature flags to ensure compatibility.
    - **Compiler and documentation compatibility:** Kani 0.67.0 bundles
      `rustc 1.93.0-nightly (53732d5e0 2025-11-20)`. Current proof comments
      cite the versioned Rust 1.93.0 Reference and standard-library
      documentation only for guarantees that already applied to that compiler
      snapshot. When changing the Kani pin, recheck both this recorded compiler
      version and every proof premise that depends on versioned language or
      library documentation.

Before running proofs locally, install the Kani version pinned in
`.github/workflows/ci.yml`. Run the same proof configuration as CI with:

```bash
./cargo.sh +stable kani \
  --package zerocopy \
  --features __internal_use_only_features_that_work_on_stable \
  --output-format=terse \
  -Zfunction-contracts \
  --randomize-layout
```

## Feature Gates

When editing code gated by a feature, compile **with and without** that feature.

```bash
./cargo.sh +stable check --tests
./cargo.sh +stable check --tests --feature foo
```
