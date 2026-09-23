---
name: zerocopy-development
description: >-
  Develop, modify, build, test, or validate code in google/zerocopy's zerocopy
  crate and its derive crate. Use for implementation work, compiler-version
  gating, generated macro code, UI or compile-fail tests, test placement,
  linting, feature-gate validation, and pre-submission checks.
---

# Zerocopy Development

Follow [`zerocopy/AGENTS.md`](../../zerocopy/AGENTS.md) while working in
the `zerocopy/` subtree. Commands in this skill assume the working directory
is `zerocopy/` unless stated otherwise.

## Workflow

1. Inspect the affected implementation, tests, configuration, and nearby
   abstractions before changing behavior. Reuse existing utilities and patterns
   where they fit.
2. Use `./cargo.sh`, never direct `cargo`. Read
   [Toolchains and Version Gating](references/toolchains.md) when choosing
   toolchains or changing compiler-version-dependent behavior.
3. Make the narrowest change that satisfies the task. Keep generated and
   handwritten behavior consistent.
4. If the change authors or modifies unsafe Rust, an unsafe API or trait, raw
   pointer or FFI code, safety documentation, a soundness argument, or an
   invariant-bearing abstraction, also use the sibling
   [`unsafe-rust`](../unsafe-rust/SKILL.md) skill.
   Do not substitute a separate zerocopy-specific unsafe methodology.
5. Add or update tests at the level that owns the behavior. For UI,
   compile-fail, or compiler-output changes, read
   [UI and Output Tests](references/ui-tests.md) before editing fixtures.
6. Before submitting, follow
   [Validation](references/validation.md), including the applicable toolchain,
   feature, and pre-push checks.

## Macro Development

Put shared macro logic in `src/util/macro_util.rs` when doing so avoids
repeating generated code. Generated code often triggers lints because names and
shapes come from user input; use targeted `#[allow(...)]` attributes where
needed to prevent generated code from producing spurious lint failures.

## Commit Messages

Use GitHub issue syntax when a commit resolves or advances an issue:

- `Closes #123` when the commit resolves the issue.
- `Makes progress on #123` when the commit advances but does not resolve it.
