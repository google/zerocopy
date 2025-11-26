<!-- Copyright 2025 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Instructions to coding agents and AI code reviewers

In addition to this document, please also read our `CONTRIBUTING.md` guide.

## Build and Test

This repository uses a wrapper script around Cargo to ensure consistent
toolchain usage and configuration.

**IMPORTANT:** You must **NEVER** run `cargo` directly. Instead, you must
**ALWAYS** use `yes | ./cargo.sh` for all `cargo` sub-commands (e.g., `check`,
`test`, `build`). Using `yes |` is required to bypass interactive prompts for
toolchain installation.

### Syntax
`yes | ./cargo.sh +<toolchain> <command> [args]`

### Toolchains
The `<toolchain>` argument is mandatory and can be one of the following:

- `msrv`: Runs with the Minimum Supported Rust Version.
- `stable`: Runs with the stable toolchain.
- `nightly`: Runs with the nightly toolchain.
- `all`: Runs the command on `msrv`, `stable`, and `nightly` sequentially.
- Version-gated toolchains: You can also pass specific version-gated toolchains
  defined in `Cargo.toml`, such as `zerocopy-core-error-1-81-0`.

### Linting

Clippy should **always** be run on the `nightly` toolchain. We do not run Clippy
in CI on earlier toolchains, so it is not guaranteed to work on those
toolchains.

```bash
yes | ./cargo.sh +nightly clippy
yes | ./cargo.sh +nightly clippy --tests
```

### Examples

```bash
# Check the code using the nightly toolchain
# DO NOT RUN: cargo check
yes | ./cargo.sh +nightly check

# Run tests on all supported toolchains
# DO NOT RUN: cargo test
yes | ./cargo.sh +all test

# Run a specific test on stable
# DO NOT RUN: cargo test -- test_name
yes | ./cargo.sh +stable test -- test_name
```

## Workflow

### Validating changes

We support multiple toolchains, as far back as our MSRV (minimum supported Rust
version). When making any change, make sure that the library continues to build
on all supported toolchains. You can do this by running `yes | ./cargo.sh +msrv
check --tests --features __internal_use_only_features_that_work_on_stable`, `yes
| ./cargo.sh +stable check --tests --features
__internal_use_only_features_that_work_on_stable`, and `yes | ./cargo.sh
+nightly check --tests --all-features`.

Zerocopy's tests are rarely sensitive to toolchain. Thus, it is generally
sufficient to run tests only on the nightly toolchain – it is rare for tests to
pass on nightly but fail on other toolchains.

When editing code that is gated by a Cargo feature, make sure to compile both
with *and without* that feature to confirm that everything still works. E.g.,
`yes | ./cargo.sh +stable check --tests` and `yes | ./cargo.sh +stable check
--tests --feature foo`.

When editing code that is only enabled on particular Rust toolchains (see the
list of toolchain gates in `Cargo.toml`), make sure to compile on both the MSRV
toolchain and on the toolchain in question (e.g., `yes | ./cargo.sh
+no-zerocopy-foo check --tests --features
__internal_use_only_features_that_work_on_stable`). Confusingly,
`no-zerocopy-foo` is the earliest toolchain that *does* support feature `foo`
(see `Cargo.toml` for an explanation of why it works that way).

### UI Tests

When updating UI test files (in `tests/ui*` or `zerocopy-derive/tests/ui*`), run
`./tools/update-ui-test-files.sh` to update the corresponding stderr files.

### Pre-submission Checks

Before submitting code, run `./githooks/pre-push` to confirm that all pre-push
hooks succeed.

### Pull Requests and Commit Messages

When a PR resolves an issue, the PR description and commit message should
include a line like `Closes #123`. When a PR makes progress on, but does not
close, an issue, the PR description and commit message should include a line
like `Makes progress on #123`.

## Safety

### Pointer Casts

- **Avoid `&slice[0] as *const T` or `&slice[0] as *mut T`.** Instead, use
  `slice.as_ptr()` or `slice.as_mut_ptr()`. Casting a reference to a single
  element creates a raw pointer that is only valid for that element. Accessing
  subsequent elements via pointer arithmetic is Undefined Behavior. See
  [unsafe-code-guidelines#134](https://github.com/rust-lang/unsafe-code-guidelines/issues/134).

- **Avoid converting `&mut T` to `*const T` (or `*const U`)**. This advice
  applies if you intend to later cast the pointer to `*mut T` and mutate the
  data. This conversion reborrows `&mut T` as a shared reference `&T`, which may
  restrict permissions under Stacked Borrows. Instead, cast `&mut T` directly to
  `*mut T` first, then to `*const T` if necessary. See
  [rust#56604](https://github.com/rust-lang/rust/issues/56604).

## Code Style

### File Headers

Each file should contain a copyright header (excluding auto-generated files such
as `.stderr` files). The header should follow the format found in existing files
(e.g. `src/lib.rs`), using the appropriate comment syntax for the file type.

### Formatting

To determine how to format code, read the formatting checker script in
`ci/check_fmt.sh`.

### Comments

All comments (including `//`, `///`, and `//!`) should be wrapped at 80 columns.

**Exceptions:**
- Markdown tables
- Inline ASCII diagrams
- Long URLs
- Comments inside of code blocks
- Comments which trail non-comment code
- Other cases where wrapping would significantly degrade readability (use your
  judgment).

### Markdown

Wrap Markdown paragraphs at 80 columns, e.g.:

```markdown
<!-- Do this -->
Lorem Ipsum is simply dummy text of the printing and typesetting industry. Lorem
Ipsum has been the industry's standard dummy text ever since the 1500s, when an
unknown printer took a galley of type and scrambled it to make a type specimen
book. It has survived not only five centuries, but also the leap into electronic
typesetting, remaining essentially unchanged. It was popularised in the 1960s
with the release of Letraset sheets containing Lorem Ipsum passages, and more
recently with desktop publishing software like Aldus PageMaker including
versions of Lorem Ipsum.

<!-- DO NOT do this -->
Lorem Ipsum is simply dummy text of the printing and typesetting industry. Lorem Ipsum has been the industry's standard dummy text ever since the 1500s, when an unknown printer took a galley of type and scrambled it to make a type specimen book. It has survived not only five centuries, but also the leap into electronic typesetting, remaining essentially unchanged. It was popularised in the 1960s with the release of Letraset sheets containing Lorem Ipsum passages, and more recently with desktop publishing software like Aldus PageMaker including versions of Lorem Ipsum.
```