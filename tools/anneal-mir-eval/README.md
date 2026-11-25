<!--
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-->

# `anneal-mir-eval`

Pure, `#![no_std]` + `alloc`, `#![forbid(unsafe_code)]` concrete evaluator and
pre-proof counterexample stepper for captured Anneal MIR JSON manifests
(`anneal-rustc-capture` schema version 4, strict Profile v1 by default, and
opt-in preview Profile v2 extensions).

## Purpose

`anneal-mir-eval` lives outside `anneal/trusted/` and adds zero bytes to
Anneal's soundness trusted computing base (`TCB`). Its role is developer and
CI ergonomics:

1. **Fast pre-proof counterexample discovery**: Exercise captured MIR functions
   on boundary and deterministic pseudorandom inputs before running full Lean
   theorem proving.
2. **Concrete execution trace inspection**: Inspect step-by-step control flow,
   arithmetic/overflow/shift/division UB faults, and stack memory lifecycle
   without spawning a solver or Lean process.
3. **Rule alignment checks**: Align with `Trusted.MirSemantics` Profile v1
   rules in standalone Rust tests and inspect captured MIR manifests directly
   (1-aligned zero-sized memory accesses succeed without allocation lookup,
   matching both `Trusted.MirSemantics.Memory` and `rustc`'s `get_place_alloc`
   / `get_place_alloc_mut`, while over-aligned zero-sized accesses check
   allocation existence and alignment).
4. **Portable core library**: Zero OS/filesystem dependencies in the library
   crate (`cargo check --target wasm32-unknown-unknown`).

## CLI Usage

By default, CLI subcommands enforce strict Profile v1 (`mir_profile_version ==
1`) and skip `unsafe fn` bodies during `probe` unless `--include-unsafe` is
passed (because `probe` explores unconstrained boundary and random inputs
without caller safety preconditions).

```bash
# List bodies in a captured manifest
cargo run --manifest-path tools/anneal-mir-eval/Cargo.toml -- \
  list path/to/capture.json

# Evaluate a specific body with concrete arguments and step trace
cargo run --manifest-path tools/anneal-mir-eval/Cargo.toml -- \
  eval path/to/capture.json --body 0 --arg 30 --arg 12 \
  [--endian big|little] [--profile-v2] [--trace]

# Probe safe bodies for concrete undefined behavior counterexamples
cargo run --manifest-path tools/anneal-mir-eval/Cargo.toml -- \
  probe path/to/capture.json --all --cases 256 \
  [--endian big|little] [--profile-v2] [--include-unsafe]
```

Pass `--profile-v2` to opt into preview Profile v2 extensions (tuples, `.field`
projections, `Assert`, direct `Call` terminators, `Isize` pointer checks, and
`UnwindAction::Terminate`, which are not yet stabilized in
`Trusted.MirSemantics`); manifest `configuration.endian` is honored when
`--endian` is omitted.

Exit codes for `eval` and `probe`:

- `0`: For `eval`, execution returned or unwound without UB. For `probe`, no
  modeled Undefined Behavior, `Unsupported` fault, `OutOfFuel` timeout, or
  unprobed parameter shape occurred (inspect `cases=`, `ok=`, `unwound=`,
  `aborted=`, and `skipped_unsafe` entries).
- `1`: CLI usage, file I/O, or JSON/argument parse error.
- `2`: Modeled Rust Undefined Behavior (`FaultKind::Undefined`) encountered.
- `3`: `eval` or `probe` hit `FaultKind::Unsupported`, `Outcome::OutOfFuel`, or
  an unsupported parameter shape.
- `4`: `eval` aborted execution via `UnwindAction::Terminate`
  (`Outcome::Aborted`, only reachable under `--profile-v2`).
