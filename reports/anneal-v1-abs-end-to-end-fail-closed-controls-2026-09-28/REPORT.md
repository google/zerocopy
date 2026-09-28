# Anneal V1 executed proof and fail-closed controls

## Summary

A small retained V1 `abs(i32)` example can complete the actual Rust → Charon LLBC → Aeneas Lean model → Anneal-generated specification → Lean checking path. The generated `abs.spec` theorem elaborates and reports only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Three controls separate pipeline failures: an ill-typed Rust body fails during Charon/rustc; a false postcondition fails during Lean proof checking; but misspelling the annotation marker causes `cargo-anneal verify` to exit successfully without running the pipeline. In that no-op case, artifacts from a previous successful run remain byte-identical. Callers therefore must check that a run actually selected annotated input and produced fresh outputs, not only that the process exited zero.

## Applicability

The executed subject is retained Anneal V1 at `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, using its `anneal/v1/examples/abs.rs` fixture adapted as a one-binary Cargo package. It was run on a macOS aarch64 host with `cargo-anneal 0.1.0-alpha.24`, Charon 0.1.210, Aeneas pinned at `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`, and Lean 4.30.0-rc2 with the package set identified in the toolchain manifest.

The source-built CLI initially refused the installed Aeneas Lake manifest because its package entries were Git dependencies, while this V1 code requires path dependencies. To execute without fetching or changing installed package sources, the probe used a disposable toolchain view: executable/source trees were symlinked and the Lake manifest's package entries were represented as local paths to the already installed `.lake/packages` trees. `support/prepare-toolchain-mirror.py` reproduces this adaptation. It changes manifest dependency representation, so the execution establishes the V1 pipeline behavior under that local path-manifest adaptation; it is not evidence that an unmodified release toolchain passes V1 setup.

## Findings

### A complete small proof traverses all major stages

The `abs` fixture specifies the signed 32-bit minimum-value precondition, nonnegative result, identity behavior for nonnegative inputs, and negation for negative inputs. With the pinned local toolchain view, `cargo-anneal verify` exited 0. Preserved outputs include the Rust source, Charon LLBC, Aeneas `Funs.lean` and `Types.lean`, Anneal-generated specification/proof module, Lake manifest, and full verification log. The generated model is the expected branch on whether `x < 0#i32`, and its specification module proves `abs.spec` using the fixture's progress and correctness scripts.

The generated module was separately re-elaborated with `#print axioms v1_abs_probe.abs.spec`; Lean exited 0 and reported `[propext, Classical.choice, Quot.sound]`. This checks the named generated theorem's Lean axiom dependencies in this configuration. It does not prove that Charon's LLBC faithfully represents arbitrary Rust semantics, that Aeneas is an independently verified compiler, or that all assumptions in the Rust-to-Lean trust chain are sound.

Basis: **execution** + **source**. See `support/abs.rs`, `support/charon-llbc.json`, `support/aeneas-Funs.lean`, `support/aeneas-Types.lean`, `support/anneal-generated-proof.lean`, `support/verify-success.log`, and `support/axioms-query.log`.

### Rust compilation errors and false specifications fail at different stages

Changing the `abs` body to return a string produced exit 1, with a rustc E0308 type mismatch surfaced in Charon's diagnostic path. The preceding successful LLBC, Aeneas Funs, Anneal specification, and Lake manifest remained present and byte-identical. A failed invocation therefore does not itself remove stale prior outputs.

Restoring valid Rust and changing the postcondition from `ret >= 0` to the false `ret < 0` also produced exit 1, this time with Lean `scalar_tac` failures and `Lean verification failed`. The Aeneas functional model remained unchanged while the generated Anneal specification changed. This distinguishes extraction/translation from proof failure for the tested example.

Basis: **execution**. Inputs and outputs are retained as `support/abs-invalid-rust.rs`, `support/abs-invalid-postcondition.rs`, `support/fail-rust.log`, and `support/fail-postcondition.log`.

### A misspelled annotation marker is a successful no-op and preserves stale results

After a successful run, changing the opening annotation fence from `lean` to `leanx` resulted in exit 0, empty stdout, and empty stderr with default logging. With `RUST_LOG=warn`, the same case exited 0 and logged `No Anneal annotations ... Nothing to verify.` The CLI did not invoke the extraction and verification stages, and the earlier LLBC, Aeneas, specification, and Lake manifest files all retained their previous hashes.

Thus process success alone is not a freshness or coverage signal. A wrapper that reports verification success should also establish that the expected annotations/targets were discovered and that outputs correspond to the current invocation (for example, by using a clean output directory or comparing an invocation-specific artifact manifest). This probe does not prescribe a particular product interface.

Basis: **execution** + **derived**. The inference follows from zero output at default logging, the warning-level no-annotation message, and unchanged output hashes after the marker typo. See `support/abs-misspelled-annotation.rs`, `support/no-annotation-default.log`, and `support/no-annotation-warning.log`.

## Boundaries

- The positive proof is one tiny function and one target configuration. It does not establish completeness for Rust features, unsupported MIR/LLBC constructs, generic or dependency-heavy crates, or large workspaces.
- The local toolchain mirror adapts the Lake manifest from Git entries to local path entries. The original V1 attempt failed before extraction at that manifest check; the successful run does not erase or explain away that compatibility boundary.
- The axiom query reports Lean's dependencies for the generated theorem. It does not capture all semantic trust assumptions across Rust, rustc, Charon, LLBC, Aeneas, and Anneal.
- Failed runs and no-op runs left prior successful artifacts in place. This is an observed stale-output risk for this invocation sequence, not evidence about every output directory or every possible invocation.
- No assertion is made about V2, which has a different implementation.

## Evidence

The report package preserves sanitized reproducers and relevant successful/failing outputs in `support/`. Source fixture: `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988:anneal/v1/examples/abs.rs`. The CLI was built offline and locked from that checkout with `cargo build --offline --locked --manifest-path anneal/v1/Cargo.toml --bin cargo-anneal`; the binary SHA-256 was `9f8283296b0150fbfe1043bbe3633879c900067915bb46aa293e55711564aee8`. Host Cargo was `1.98.0-nightly (fbb61be30 2026-05-26)` and rustc was `1.98.0-nightly (f8a08b688 2026-05-30)`. The revalidation run using the packaged mirror helper completed with exit 0 on 2026-09-28.

The `support/observations.json` file records artifact sizes, hashes, exit statuses, and the stale-output comparisons. Paths in the preserved logs and LLBC have been redacted where they contained machine-local absolute directories; the hashes in observations refer to pre-redaction local outputs and therefore need not match the redacted copies.

## Revalidation

Use the exact retained V1 checkout and source fixture, build the CLI with its locked dependencies, and point `ANNEAL_TOOLCHAIN_DIR` at an installed matching toolchain. If its Lake manifest uses Git package entries, either establish that the V1 manifest check has changed or reproduce the documented disposable local-path adaptation with `support/prepare-toolchain-mirror.py`. Run the positive case in a clean Cargo project, then independently try (1) the type-invalid Rust body, (2) the false postcondition, and (3) the misspelled annotation after a success. Record process exits and hashes of all generated artifacts before and after each control. The key regression question is whether a no-annotation invocation still returns zero while leaving prior outputs untouched.
