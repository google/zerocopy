# Cargo unit graphs and rustc invocations at the Anneal-era 2026-05-31 toolchain

## Summary

At `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, Cargo turns command-selected targets into a recursive graph of compilation units. Roots only describe work requested directly. Cargo adds dependency libraries, same-package libraries for binaries/tests/examples, host procedural macros, and separate build-script compile and execution units. Cross builds therefore contain both host and target work.

A Rust compilation unit becomes a `rustc` process in stages. Cargo selects the compiler and wrapper chain, adds unit-derived arguments, then adds dependency artifacts as search paths and `--extern` inputs. Some command state is delayed until execution because build-script output does not exist when Cargo constructs the unit graph. Build-script results can later add native search paths and libraries, compiler flags, and environment variables.

The unstable `--unit-graph` output is therefore a planned-work graph rather than a final compiler-command transcript. It exposes units, roots, platforms, modes, features, and dependency edges, including `run-custom-build` nodes, but not the complete final argv/environment. A planned unit can also be skipped when Cargo's fingerprint says its existing artifact is fresh.

Compiler wrappers form another process boundary. With both wrapper mechanisms configured, Cargo documents the effective process as `$RUSTC_WRAPPER $RUSTC_WORKSPACE_WRAPPER $RUSTC ...` for workspace-member compilation.

No fresh Cargo, rustc, wrapper, build-script, or cross-target execution was performed. This package establishes the source-level graph and invocation construction at the exact pin. See [Findings](FINDINGS.md), [Boundaries](BOUNDARIES.md), [Evidence](EVIDENCE.md), and [Revalidation](REVALIDATION.md).

## Applicability

Primary subject:

- Cargo: `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`.
- Rust integration: `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, whose `src/tools/cargo` submodule points to that Cargo revision.
- Anneal context: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, whose `anneal/flake.nix` selects the 2026-05-31 Rust toolchain.
- Charon context: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, whose `rust-toolchain` selects `nightly-2026-05-31`.

The companion report `cargo-compilation-subject-identity-2026-05-31` establishes which fields distinguish Cargo `Unit` values and the limits of the serialized unit graph. This package follows those units through dependency expansion and command construction.

The source revision, Rust submodule relation, and matching toolchain date establish the implementation studied and its relevance. They are not byte-for-byte provenance evidence for the published Cargo binary archive.

## Findings

See [FINDINGS.md](FINDINGS.md).

## Boundaries

See [BOUNDARIES.md](BOUNDARIES.md).

## Evidence

See [EVIDENCE.md](EVIDENCE.md). Evidence roles are **source**, **documentation**, and **derived**. There is no fresh **execution** evidence.

## Revalidation

See [REVALIDATION.md](REVALIDATION.md).
