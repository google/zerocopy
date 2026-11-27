<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Curated Tier B Miri UB Regression Corpus

This directory contains original, standalone, zero-dependency undefined-behavior
(UB) regression fixtures and valid negative-control fixtures executed by
`anneal/ci/run_miri_ub_oracle.py`.

Every fixture is registered in `manifest.json`. Orphan `.rs` or `.json` files
are rejected fail-closed so newly added regressions cannot be silently skipped.

This corpus executes against `anneal-rustc-capture` and the zero-TCB Rust MIR
evaluator (`anneal-mir-eval`), not Lean `Trusted.MirSemantics`; a green run
does not by itself establish correspondence between the mirror and Lean.

## Running the Oracle Locally

> **Prerequisite (Linux only):** `anneal/ci/run_miri_ub_oracle.py` requires an
> unprivileged (non-root) user on a **Linux** host (`x86_64` or `aarch64`) with
> kernel **Landlock ABI >= 3**, **seccomp-bpf**, and unprivileged
> user/PID/mount/network namespaces enabled; non-Linux hosts (macOS, Windows)
> and root (`UID 0`) invocations fail closed before executing any fixture. On
> `aarch64` hosts, Tier A still targets the pin's `x86_64-unknown-linux-gnu`
> triple, so install that target first:
> `rustup target add --toolchain nightly-2026-05-31 x86_64-unknown-linux-gnu`.

Build `anneal-rustc-capture` (with Anneal's pinned nightly toolchain) and
`anneal-mir-eval`, then invoke `anneal/ci/run_miri_ub_oracle.py`:

```sh
SYSROOT="$(rustc +nightly-2026-05-31 --print sysroot)"
RUSTFLAGS="-L ${SYSROOT}/lib -C link-arg=-Wl,-rpath,${SYSROOT}/lib" \
  cargo +nightly-2026-05-31 build --release --locked \
    --manifest-path anneal/Cargo.toml -p anneal-rustc-capture
cargo build --release --locked \
  --manifest-path tools/anneal-mir-eval/Cargo.toml

# Tier B (offline curated in-repo regression corpus):
python3 -I -B anneal/ci/run_miri_ub_oracle.py --tier-b --no-network \
  --capture-bin anneal/target/release/anneal-rustc-capture \
  --eval-bin tools/anneal-mir-eval/target/release/anneal-mir-eval \
  --sysroot "${SYSROOT}"

# Tier A (SHA-256-pinned upstream rust-lang/miri tests/fail corpus; pass
# --archive /path/to/miri.tar.gz --no-network for offline runs):
python3 -I -B anneal/ci/run_miri_ub_oracle.py --tier-a \
  --capture-bin anneal/target/release/anneal-rustc-capture \
  --eval-bin tools/anneal-mir-eval/target/release/anneal-mir-eval \
  --sysroot "${SYSROOT}"
```

## Fixture Categories

- **`rust_ub_caught` (`*.rs`)**: Minimal Rust programs compiled with
  `anneal-rustc-capture --scope crate` and executed with `anneal-mir-eval`.
  Every fixture must be caught as modeled UB (`caught_ub`, exit code `2`).
  They use only stable APIs (`unchecked_add`, `unchecked_sub`, and
  `unchecked_mul` across integer widths, including through an enum `match`):
  capture refuses every crate that enables `core_intrinsics`, even under
  `--allow-unstable-feature`.
- **`mir_ub_caught` (`mir/*.json`)**: Direct MIR `Program` JSON fixtures
  evaluated with `anneal-mir-eval` to cover evaluator UB rules directly
  (unchecked arithmetic/shift overflow, uninitialized/dead local reads, and
  unreachable terminators), including division or remainder by zero and signed
  `MIN / -1` / `MIN % -1`, which stable Rust cannot reach without intrinsics.
- **`rust_ub_fail_closed` (`*.rs`)**: Valid compiling Rust UB programs covering
  zero-sized and non-zero-sized misalignment, null/out-of-bounds/dangling
  pointers, uninitialized reads, invalid scalar validity (`bool`, `char`,
  fieldless enums, `NonZeroU32`), unchecked shifts, immutable writes,
  and pre-`main` `.init_array` constructors. Every fixture must compile cleanly
  and fail closed or be caught as UB (`unsound_accept == 0`, zero compiler
  failures). Fixtures that graduate to `caught_ub` are reported in
  `promotion_candidates` so their expectation can be tightened to
  `rust_ub_caught`.
- **`rust_valid_control` (`*.rs`) & `mir_valid_control` (`mir/*.json`)**:
  Valid, UB-free controls (including non-overflowing `unchecked_*` calls)
  that must be accepted (`accepted_valid`, exit code `0`, normal return) so the
  oracle harness cannot pass vacuously by rejecting all inputs.
