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
    - **Generated-output exception:** A semantic proof of proc-macro-generated
      code may live in a focused child of the consuming source file's inline
      `mod proofs` when the defining proc-macro crate cannot invoke its own
      macro and the proof requires consumer-crate internals. Keep each concrete
      derive invocation beside the harness that verifies its expansion, and
      cross-link the consumer proof and generator source so that changes to
      either side trigger review. This exception covers only the enumerated
      concrete expansions and their linked runtime paths; it does not turn
      consumer-side verification into a universal theorem about the generator
      or its token output.
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
        - **Oracles:** Every oracle must be independent of the implementation
          under proof. Prefer a safe Rust language or standard-library
          operation whose documented contract directly supplies the expected
          behavior. Do not call the target, reuse its zerocopy helper or policy,
          or manually reconstruct the same unchecked operation. For every
          oracle, state its normative basis, why it is independent, and its
          limitations. If no safe oracle exists, isolate the smallest manual
          rule and cite its normative basis. If a predicate merely restates a
          zerocopy acceptance policy, label it as a policy oracle rather than
          evidence of Rust-level validity.
        - **Factoring:** Share repeated case generation, oracle construction,
          and postcondition checks within the proof module. Keep distinct
          harnesses when they exercise different entry points or contracts.
        - **Domain:** Document every scope dimension independently: the
          symbolic input domain; concrete size, allocation, loop, and unwind
          bounds; assumptions and excluded boundary cases; Kani and bundled
          compiler selection; target and data model; enabled features and
          verifier flags; randomized-layout count or seed; the established
          properties; and explicit non-goals. Shared configuration may be
          factored into a nearby family or module scope only when every covered
          harness refers to it unambiguously.
        - **Non-vacuity:** Use `kani::cover!` to check that important input and
          result partitions are reachable. Every assumption must correspond to
          a documented precondition or to the stated proof bound. Do not reject
          inputs using an impossible assumption or a diverging loop. Kani 0.67
          [treats cover properties as reporting-only][Kani cover renderer] and
          has no
          `--fail-on-cover` option: zero satisfied covers can accompany a
          successful verification result. `ci/run_kani.sh` therefore checks
          every emitted cover summary and fails unless all cover properties are
          satisfied. Its parser is part of the pinned-version audit and must be
          revalidated when Kani or its output format changes.
        - **Bit validity:** `kani::any::<T>()` produces only valid instances of
          `T`. To verify a byte validator, generate arbitrary bytes and decide
          expected acceptance using an independent oracle before consulting the
          target. Never materialize `T` merely because the validator under
          proof accepts: that validator may be the bug. Construct `T` only
          through an independently safe checked operation. If no such operation
          exists, exercise only a non-materializing decision path for invalid
          candidates and document that limitation.
        - **Soundness boundary:** State which obligations Kani does not prove.
          In particular, Kani does not completely check reference aliasing,
          pointer provenance, invalid values, or uninitialized memory. Kani's
          official [Rust feature support] table marks breaking pointer aliasing
          rules and producing invalid values as unsupported (where unsupported
          analyses "should not be trusted"), and describes uninitialized-memory
          checking as partial and experimental. Its [undefined-behaviour guide]
          also explains the corresponding reference-lifetime and invalid-value
          gaps. Treat conclusions that depend on those semantics as TOOL/TCB
          premises rather than proof results.
        - **Layout randomization:** `--randomize-layout` checks one randomized
          layout per run; it does not prove behavior for every layout or target.
    - **Kani CI configuration:** The exact Kani release is the single
      `kani-version` pin in `.github/workflows/ci.yml`; its bundled compiler is
      the proof toolchain. CI runs on `x86_64-unknown-linux-gnu` (64-bit,
      little-endian) with
      `__internal_use_only_features_that_work_on_stable` (`alloc`, `derive`,
      `simd`, and `std`), `-Zfunction-contracts`, and one layout selected by
      `--randomize-layout` per invocation. Source-level proof scopes should
      refer to this common configuration and state any deviations.
    - **Compiler and documentation compatibility:** After installing the
      pinned Kani release, inspect the `kani-compiler` executable in that
      release's installation directory (normally
      `~/.kani/kani-<version>/bin/kani-compiler`) with `--version --verbose`,
      and inspect its data model with `--print cfg`. Proof premises must cite
      versioned Rust Reference or standard-library documentation. When changing
      the Kani pin, manually recheck every such premise against the new compiler
      snapshot; mechanically changing citation versions does not establish that
      a guarantee still applies. This compatibility check is a manual TOOL/TCB
      premise: a successful Kani run does not itself establish that the cited
      documentation describes the bundled compiler snapshot.
    - **Fail-closed audit synchronization:** `ci/check_actions.sh`, run by
      pre-push and CI, requires the `kani-version` pin to equal the version named
      by the recorded audit below. The scheduled Kani roller intentionally
      changes only the executable pin, so its PR cannot pass this check until a
      human completes the audit workflow. Do not mechanically update the audit
      version label: first install the new release; replace the compiler,
      target, CBMC, and option-behavior record; recheck every versioned Rust
      contract against the new compiler snapshot; and rerun the complete Kani
      suite. Only then update the label to the new pin.
    - **Recorded toolchain audit for `kani-version: 0.67.0`:** On 2026-09-08,
      `kani-compiler --version --verbose` reported `rustc 1.93.0-nightly`, commit
      `53732d5e076329a62f71d3c6901886ce8a71e812` dated 2025-11-20, LLVM 21.1.5,
      and host `x86_64-unknown-linux-gnu`; `kani-compiler --print cfg` reported
      Linux/gnu, x86_64, little endian, 64-bit pointers, and panic unwinding.
      The bundled `cbmc --version` reported CBMC 6.8.0, and its `--help`
      reported `--no-malloc-may-fail  disable potential malloc failure` and
      `--malloc-may-fail  allow malloc calls to return a null pointer`. The
      admitted compatibility proposition is that the versioned Rust 1.93.0
      contracts cited by the current proofs describe the corresponding
      behavior of this nightly snapshot. This was checked manually, not proved
      by Kani. The audited terse output reports cover summaries as
      `** N of M cover properties satisfied`; `ci/run_kani.sh` requires `N ==
      M` for every summary and requires at least one recognized summary. Kani
      0.67 [does not model stack unwinding][Kani panic strategies] even though
      its bundled compiler's target cfg reports `panic="unwind"`; proofs may
      use reachable panics as failed properties but may not infer cleanup or
      post-panic behavior.

[Rust feature support]: https://model-checking.github.io/kani/rust-feature-support.html
[undefined-behaviour guide]: https://model-checking.github.io/kani/undefined-behaviour.html
[Kani cover renderer]: https://github.com/model-checking/kani/blob/kani-0.67.0/kani-driver/src/cbmc_property_renderer.rs
[Kani panic strategies]: https://github.com/model-checking/kani/blob/kani-0.67.0/docs/src/rust-feature-support.md#panic-strategies

Before running proofs locally, install the Kani version pinned in
`.github/workflows/ci.yml`. Run the same proof configuration as CI with:

```bash
ci/run_kani.sh \
  --manifest-path Cargo.toml \
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
