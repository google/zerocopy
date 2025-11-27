<!-- Copyright 2025 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Instructions for AI Agents

## Agent Persona & Role

You are an expert Rust systems programmer contributing to **zerocopy**, a
library for zero-cost memory manipulation which presents a safe API over what
would otherwise be dangerous operations. Your goal is to write high-quality,
sound, and performant Rust code that adheres to strict safety and soundness
guidelines and works across multiple Rust toolchains and compilation targets.

## Critical Rules

> [!IMPORTANT]
> **NEVER** run `cargo` directly.
> **ALWAYS** use `yes | ./cargo.sh` for all cargo sub-commands.
>
> **Why?** `cargo.sh` ensures that the toolchains used in development match
> those in CI, which is important because some features are only available on
> specific toolchains, and because UI tests rely on the text of compiler errors,
> which changes between toolchain versions.

- **README Generation:** **DON'T** edit `README.md` directly. It is generated
  from `src/lib.rs`. Edit the top-level doc comment in `src/lib.rs` instead.
  - **To regenerate:**
    `yes | ./cargo.sh +stable run --manifest-path tools/generate-readme/Cargo.toml > README.md`

- **TODOs:** **DON'T** use `TODO` comments unless you explicitly intend to block
  the PR (CI fails on `TODO`). Use `FIXME` for non-blocking issues.

- **Strict Version Matching:** `zerocopy` and `zerocopy-derive` must always have
  the exact same version.
  - **Why:** These crates are tightly coupled. Mismatched versions can lead to
    build errors or undefined behavior because `zerocopy-derive` generates code
    that relies on specific, hidden implementation details of `zerocopy` which
    are not subject to semantic versioning, and so can have
    backwards-incompatible changes even when the crate's major version number
    does not increase.
  - **Dependencies:** `zerocopy` must depend on the exact same version of
    `zerocopy-derive` (e.g., `=0.8.0`).

- **Documentation:** **DO** ensure that changes do not cause documentation to
  become out of date (e.g., renaming files referenced here).

## Project Context

### Overview

Zerocopy is a library designed to make zero-copy memory manipulation safe and
easy. It relies heavily on Rust's type system and specific traits to ensure
memory safety.

### Documentation & Policies

You must read and adhere to the following documents:
- [`POLICIES.md`](./POLICIES.md): Contains strict policies on soundness, safety
  comments, and versioning.
- [`CONTRIBUTING.md`](./CONTRIBUTING.md): General contribution guidelines.

### MSRV (Minimum Supported Rust Version)

The MSRV is **1.56.0**.

- **Do NOT** use features stabilized after 1.56.0 (e.g., `let else`,
  `bool::then_some`) unless they are version-gated.
- **Exception:** It is permitted to use features from toolchains more recent
  than our MSRV so long as they are gated by a `--cfg` flag defined in
  `Cargo.toml`. It is also permitted to use such features if they are gated by
  a Cargo feature defined in `Cargo.toml`.
- **Requirement:** You **MUST** ask for explicit user approval before
  introducing new version-gated behavior, as this always implicates API design
  decisions which a human should make.
- Ensure code compiles on 1.56.0 (i.e., `yes | ./cargo.sh +msrv ...`).

#### Version Gating Convention

We use a specific convention to gate features that require newer Rust versions:

1.  **Define in `Cargo.toml`**: Add a key in `[package.metadata.build-rs]` named
    `no-zerocopy-<feature>-<version>`.
    - Example: `no-zerocopy-core-error-1-81-0 = "1.81.0"`

2.  **Use in Code**: The build script emits a cfg with underscores instead of
    dashes.
    - To **enable** the feature on newer toolchains:
      `#[cfg(not(no_zerocopy_core_error_1_81_0))]`
    - To **disable** (fallback) on older toolchains:
      `#[cfg(no_zerocopy_core_error_1_81_0)]`

3.  **Document Public Items**: When version-gating public items, you **MUST**
    use `doc_cfg` so the requirement appears in the generated documentation.
    - **Syntax:** `#[cfg_attr(doc_cfg, doc(cfg(...)))]`
    - **Example:**
      ```rust
      #[cfg(not(no_zerocopy_core_error_1_81_0))]
      #[cfg_attr(doc_cfg, doc(cfg(rust = "1.81.0")))]
      impl Error for MyType {}
      ```
    - **Note:** The `doc_cfg` attribute is enabled by `docs.rs` and requires the
      nightly toolchain.

## Development Workflow

### Build and Test

This repository uses a wrapper script (`cargo.sh`) which invokes
`tools/cargo-zerocopy` to ensure consistent toolchain usage and configuration.

#### Syntax

`yes | ./cargo.sh +<toolchain> <command> [args]`

This is equivalent to:

`cargo +1.2.3 <command> [args]`

...where `1.2.3` is the toolchain version named by `<toolchain>` (e.g., `msrv` ->
`1.56.0`).

#### Toolchains

The `<toolchain>` argument is mandatory:
- `msrv`: Minimum Supported Rust Version.
- `stable`: Stable toolchain.
- `nightly`: Nightly toolchain.
- `all`: Runs on `msrv`, `stable`, and `nightly` sequentially.
- Version-gated: e.g., `no-zerocopy-core-error-1-81-0` (see `Cargo.toml`).

**Important:** The toolchains listed in `.github/workflows/ci.yml` and
`Cargo.toml` (under `[package.metadata.build-rs]`) must be kept in sync. If you
add a new version-gated feature, ensure it is reflected in both places.

### Linting

Clippy should **always** be run on the `nightly` toolchain.

```bash
yes | ./cargo.sh +nightly clippy
yes | ./cargo.sh +nightly clippy --tests
```

**Strict Linting:**
- We deny warnings in CI. Even warnings not explicitly listed in `lib.rs` will
  cause CI to fail.
  - **Why:** We maintain a zero-warning policy so that new warnings (which often
    indicate bugs) are immediately obvious and not obscured by existing ones.
- Do not introduce new warnings.
- Respect the strict `deny` list in `src/lib.rs`.

### Semver Checks

- We run `cargo-semver-checks` in CI.
- If `cargo-semver-checks` incorrectly flags a change as breaking (a false
  positive), you may add `SKIP_CARGO_SEMVER_CHECKS=1` to your commit message to
  bypass the check.
- **Note:** This is **NOT** for authorizing actual breaking changes. Breaking
  changes require a major version bump and extensive discussion.

### Validating Changes

Ensure the library builds on all supported toolchains and that Clippy passes.

```bash
yes | ./cargo.sh +msrv check --tests --features __internal_use_only_features_that_work_on_stable
yes | ./cargo.sh +stable check --tests --features __internal_use_only_features_that_work_on_stable
yes | ./cargo.sh +nightly check --tests --all-features
yes | ./cargo.sh +nightly clippy --tests --all-features --workspace
```

**Note:** Tests are rarely toolchain-sensitive. Running tests on `nightly` is
usually sufficient.

### Testing Strategy

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
    - **Purpose:** Use the [Kani Rust Verifier](https://model-checking.github.io/kani/)
      to prove the soundness of `unsafe` code or code relied upon by `unsafe`
      blocks. Unlike testing, which checks specific inputs, Kani proves
      properties for *all* possible inputs.
    - **How to Write Proofs:**
        - **Harnesses:** Mark proof functions with `#[kani::proof]`.
        - **Inputs:** Use `kani::any()` to generate arbitrary inputs.
        - **Assumptions:** Use `kani::assume(condition)` to constrain inputs to
          valid states (e.g., `align.is_power_of_two()`).
        - **Assertions:** Use `assert!(condition)` to verify the properties you
          want to prove.
    - **CI:** Kani runs in CI using the `model-checking/kani-github-action` with
      specific feature flags to ensure compatibility.

<!-- TODO: Describe how to ensure that a Kani proof is "total" (esp wrt function inputs). -->

### Feature Gates

When editing code gated by a feature, compile **with and without** that feature.

```bash
yes | ./cargo.sh +stable check --tests
yes | ./cargo.sh +stable check --tests --feature foo
```

### UI Tests

When updating UI test files (`tests/ui*` or `zerocopy-derive/tests/ui*`) or functionality
which could affect compiler error output, run: `./tools/update-ui-test-files.sh`.

**Note:** We maintain separate UI tests for different toolchains (`ui-msrv`,
`ui-stable`, `ui-nightly`) because compiler output varies. The script handles
this automatically.

**NEVER** edit `.stderr` files directly. Only update them via the script or the
commands it runs. If a `.stderr` file is causing a test failure and updating it
via tooling does not fix the failure, that indicates a bug.

**Tip:** You can run `TRYBUILD=overwrite ./cargo.sh ...` to update UI tests
manually if needed, but the script is preferred.

### Pre-submission Checks

Run `./githooks/pre-push` before submitting. This runs a comprehensive suite of
checks, including formatting, toolchain verification, and script validation. It
catches many issues that would otherwise fail in CI.

### Pull Requests and Commit Messages

Use GitHub issue syntax in commit messages:

- Resolves issue: `Closes #123`
- Progress on issue: `Makes progress on #123`

## Coding Standards

### Safety Guidelines

#### Pointer Casts

- **Avoid `&slice[0] as *const T`**: Use `slice.as_ptr()`. Accessing subsequent
  elements via pointer arithmetic on a single-element pointer is UB.
  ```rust
  let slice = &[1, 2];

  // BAD: Derived from reference to single element.
  let ptr = &slice[0] as *const i32;
  // SAFETY: UB! `ptr` has provenance only for the first element.
  // Accessing `ptr.add(1)` is out of bounds for this provenance.
  let val = unsafe { *ptr.add(1) };

  // GOOD: Derived from the slice itself.
  let ptr = slice.as_ptr();
  // SAFETY: Safe because `ptr` has provenance for the entire slice.
  let val = unsafe { *ptr.add(1) };
  ```
- **Avoid converting `&mut T` to `*const T`**: This reborrows as a shared
  reference, restricting permissions. Cast `&mut T` to `*mut T` first.
  ```rust
  let mut val = 42;
  let r = &mut val;

  // BAD: `r as *const i32` creates a shared reborrow.
  // The resulting pointer loses write provenance.
  let ptr = r as *const i32 as *mut i32;
  // SAFETY: UB! Writing to a pointer derived from a shared reborrow.
  unsafe { *ptr = 0 };

  // GOOD: `r as *mut i32` preserves write provenance.
  let ptr = r as *mut i32;
  // SAFETY: Safe because `ptr` retains mutable provenance.
  unsafe { *ptr = 0 };
  ```

#### Safety Comments

Every `unsafe` block must be documented with a `// SAFETY:` comment.
- **Requirement:** The comment must prove soundness using *only* text from the
  stable [Rust Reference](https://doc.rust-lang.org/reference/) or standard
  library documentation.
  <!-- TODO: Provide link to standard library documentation. -->
- **Citation:** You must cite and quote the relevant text from the documentation.
- **Prohibition:** Do not rely on "common sense" or behavior not guaranteed by
  the docs.
  ```rust
  // BAD: Missing justification for "obvious" properties.
  // SAFETY: `ptr` and `field` are from the same object.
  let offset = unsafe { field.cast::<u8>().offset_from(ptr.cast::<u8>()) };

  // GOOD: Explicitly justifies every requirement, even trivial ones.
  // SAFETY:
  // - `ptr` and `field` are derived from the same allocated object.
  // - The distance between them is trivially a multiple of `u8`'s size (1),
  //   satisfying `offset_from`'s alignment requirement.
  let offset = unsafe { field.cast::<u8>().offset_from(ptr.cast::<u8>()) };
  ```
  <!-- TODO: Update this example to cite the docs. -->

### Macro Development

- **Shared Logic:** Put shared macro logic in `src/util/macro_util.rs` to avoid
  code duplication in generated code.
- **Lints:** Generated code often triggers lints. Use `#[allow(...)]` liberally
  in generated code to suppress them.
  ```rust
  // GOOD: Suppress lints that might be triggered by generated names.
  // Example: Using a variant name (PascalCase) as a field name (snake_case).
  // Input: `enum MyEnum { VariantA }`
  // Generated: `union Variants { __field_VariantA: ... }`
  quote! {
      #[allow(non_snake_case)]
      union ___ZerocopyVariants {
          #(#fields)*
      }
  }
  ```

### Code Style

#### File Headers

Each file must contain a copyright header (see `src/lib.rs` for example) which
is based on that file's creation year.

#### Formatting

Refer to `ci/check_fmt.sh`.

#### Comments

- Wrap all comments (`//`, `///`, `//!`) at **80 columns**.
- **Exceptions:** Markdown tables, ASCII diagrams, long URLs, code blocks, or
  other cases where wrapping would impair readability.

#### Markdown Files

- Wrap paragraphs and bulleted lists at **80 columns** from the left margin,
  taking into account any preceding code or comments.
  <!-- TODO: Provide an example of this in the context of a code comment. -->
  - In bulleted lists, indent subsequent lines by 2 spaces.
  - Do not wrap links if it breaks them.
- Always put a blank line between a section header and the beginning of the
  section.
