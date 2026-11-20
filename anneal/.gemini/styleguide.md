<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Coding and Review Guidelines

Follow [`AGENTS.md`](../AGENTS.md) and the applicable skills in
[`skills/`](../skills/README.md) when authoring or reviewing changes in this
repository.

## Dedicated Trust-Boundary Review Pass

In addition to general code review, evaluate every pull request against
[`skills/trust-review/SKILL.md`](../skills/trust-review/SKILL.md),
[`PRINCIPLES.md`](../PRINCIPLES.md), and
[`docs/trust-model.md`](../docs/trust-model.md) across two distinct goals, and
treat any violation as a blocking finding:

1. **Changes outside `trusted/`, `ci/`, and `.github/` (Enforcement-bypass
   audit):** Verify that untrusted code (such as `theory/`, tests, or new
   files) cannot intentionally or accidentally bypass `anneal-audit` or CI:
   - Reject Rust crates, `build.rs` scripts, proc-macros, Makefiles,
     `lakefile.lean`, shell/Python scripts, or ambient config overrides
     (`.cargo/config.toml`, `rust-toolchain*`, `.envrc`) outside `trusted/`.
   - Reject `.lean` files outside `trusted/lean/` and `theory/`, symlinks, or
     checked-in `.olean`/`.ilean`/`.ir` artifacts.
   - Reject metaprogramming, file/env I/O, compiler overrides
     (`@[implemented_by]`, `@[extern]`, `@[csimp]`), `Trusted` namespace
     declarations, `-- anneal-trust-tier:` directives, `axiom`, `sorry`,
     `unsafe`, `partial`, `opaque`, `native_decide`, `by_elab`, or `#eval` in
     `theory/`, including constructs that exploit gaps in
     `TrustedBoundary.lean`.
   - Flag vacuous or contradictory specifications in `theory/` that trivially
     discharge proof obligations.
2. **Changes inside `trusted/`, `ci/`, `.github/`, and pinned root manifests
   (TCB and harness audit):** Whenever a PR touches these paths (or
   `Cargo.toml`, `Cargo.lock`, `flake.nix`, or `flake.lock`), include a
   `### Trust-Boundary Assessment` section in the review and verify:
   - **`trusted/lean/` & `trusted/rustc-capture/`:** Semantic rules and MIR
     capture must fail closed (including `tcx.dcx().has_errors()` guards),
     perform no unverified semantic normalization in Rust, maintain
     `vetted` vs. `candidate:<feature>` `-- anneal-trust-tier:` separation, and
     quote and cite the Rust Reference (`rust-lang/reference`) or `rustc`
     (`rust-lang/rust`) at a pinned commit hash.
   - **`trusted/audit/` & lock files:** Do not weaken `anneal-audit` syntax,
     attribute, axiom, or Cargo containment checks, `.olean` loading flags
     (`trustLevel := 0`, `loadExts := false`), or kernel replay without sound
     justification and negative tests in
     `trusted/audit/tests/boundary_audit.rs`. Keep
     `trusted/root-manifest.sha256` and `trusted/lean/foundation-lock.json`
     updated in lockstep with root manifests and foundation files.
   - **`ci/` & `.github/workflows/`:** Preserve `root-manifest.sha256` checks,
     `anneal-audit` execution, fail-closed `all-jobs-succeed` dependencies,
     40-char Action SHA pins, `permissions: contents: read`, and cache/artifact
     token stripping in jobs running scripts outside `trusted/`.
