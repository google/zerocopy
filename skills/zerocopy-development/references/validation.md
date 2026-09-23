# Validation

Choose validation that covers the behavior and configuration changed, then run
the repository's pre-push checks before submission.

## Linting

Run Clippy on nightly:

```bash
./cargo.sh +nightly clippy
./cargo.sh +nightly clippy --tests
```

CI denies warnings. Do not introduce new warnings, including warnings not
explicitly listed in `src/lib.rs`, and respect the crate's explicit deny list
there.

## Supported Toolchains

Check the library on the supported compiler classes and run workspace Clippy:

```bash
./cargo.sh +msrv check --tests \
  --features __internal_use_only_features_that_work_on_stable
./cargo.sh +stable check --tests \
  --features __internal_use_only_features_that_work_on_stable
./cargo.sh +nightly check --tests --all-features
./cargo.sh +nightly clippy --tests --all-features --workspace
```

Tests are rarely compiler-version-sensitive; nightly is usually sufficient for
ordinary test execution unless the changed behavior is toolchain-specific.

## Test Placement

- Put unit tests in a `mod tests` module in the source file they exercise.
- Put main-crate UI and compile-fail tests in `tests/ui-*`. The top-level
  `tests` directory otherwise contains only UI tests.
- Put derive-crate UI and compile-fail tests in
  `zerocopy-derive/tests/ui-*`.
- Put derive integration tests in `zerocopy-derive/tests`.
- Put tests of generated derive token streams in
  `zerocopy-derive/src/output_tests.rs`.
- Put Kani proofs in a `mod proofs` module in the source file they exercise.

For Kani, mark harnesses with `#[kani::proof]`, use `kani::any()` for arbitrary
inputs, `kani::assume(...)` for explicit preconditions, and `assert!(...)` for
properties being checked. When Kani evidence supports an unsafe-code soundness
claim or safety argument, also use the
`unsafe-rust` skill and account for
the exact harness, assumptions, model, and proved property under that skill's
evidence rules. Kani runs in CI with repository-selected feature flags; inspect
the current CI configuration rather than copying those flags into this guide.

<!-- FIXME: Describe how to ensure that a Kani proof is "total" (esp wrt
function inputs). -->

## Feature Gates

When editing feature-gated code, compile both without and with the affected
feature. For example:

```bash
./cargo.sh +stable check --tests
./cargo.sh +stable check --tests --feature foo
```

## Pre-Submission Check

Run:

```bash
../githooks/pre-push
```

The hook runs the repository's comprehensive formatting, toolchain, and script
checks. Fix failures rather than bypassing the hook.
