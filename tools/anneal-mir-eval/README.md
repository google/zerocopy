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
(`anneal-rustc-capture` schema version 5, Profile v1 and Profile v2).

## Purpose

`anneal-mir-eval` lives outside `anneal/trusted/` and adds zero bytes to
Anneal's soundness trusted computing base (`TCB`). Its role is developer and
CI ergonomics:

1. **Fast pre-proof counterexample discovery**: Exercise captured MIR functions
   on boundary and deterministic pseudorandom inputs before running full Lean
   theorem proving.
2. **Concrete execution trace inspection**: Inspect step-by-step control flow,
   arithmetic/overflow/shift/division UB faults, Profile v1 intra-crate and
   pinned `core::num` calls, and Profile v2 pointer/reference/slice operations
   without spawning a solver or Lean process.
3. **1:1 `Trusted.MirSemantics` alignment and witness classification**:
   - Profile v1 matches `Trusted.MirSemantics.{State,Step,Boundary}` including
     multi-frame intra-crate `Call` (refusing `unsafe fn` callees), pinned
     `SysrootCall`, and unchecked arithmetic.
   - Profile v2 matches `Trusted.MirSemantics.{Layout,Memory,Bytes,Step}`
     including `CallerMemory`, thin and wide slice pointers, `PtrMetadata`,
     `BinOp::Offset`, `CastKind::{PtrToPtr,IntToPtr}`, `Rvalue::{UseRetag,Ref,
     AddressOf,AggregateRangeTo,AggregateRangeFrom}`, `CoreCallOp`, `Assert`
     (`MisalignedPtrDeref`/`NullPtrDeref` -> `Undefined`, other panicking
     asserts -> `Unsupported`), single-level `PartialTuple` moves, and
     allocation-checked zero-sized memory reads/writes.
   - Captured constructs that the evaluator does not model yet (array
     aggregates and repeats, `ConstantIndex` projections, `Unsize` casts,
     read-only data constants, and the `IntToLeBytes` and `ArrayEq` core calls)
     still parse, and evaluating them fails closed with `Unsupported`.
   - Every `Undefined` counterexample is explicitly classified as either
     `replayable_miri_ub` (concrete Rust/Miri UB) or `model_only_unreplayed`
     (documented conservative `Trusted.MirSemantics` over-approximation or
     synthetic artifact) so replay gates never bypass or misreport unreplayed
     witness classes.
4. **Portable core library**: Zero OS/filesystem dependencies in the library
   crate (`cargo check --lib --target wasm32-unknown-unknown`).

## CLI Usage

By default, CLI subcommands auto-select Profile v1 or Profile v2 from
`program.mir_profile_version` (overrideable with `--strict-v1` or
`--profile-v2`) and skip `unsafe fn` bodies during `probe` unless
`--include-unsafe` is passed (because `probe` explores unconstrained boundary
and random inputs without caller safety preconditions).

```bash
# List bodies in a captured manifest
cargo run --manifest-path tools/anneal-mir-eval/Cargo.toml -- \
  list path/to/capture.json

# Evaluate a specific body with concrete arguments (or --query <query.json>)
cargo run --manifest-path tools/anneal-mir-eval/Cargo.toml -- \
  eval path/to/capture.json --body 0 --arg "[10,20,30,40]" --arg 2 \
  [--endian big|little] [--strict-v1 | --profile-v2] [--trace]

# Probe bodies for concrete undefined behavior counterexamples
cargo run --manifest-path tools/anneal-mir-eval/Cargo.toml -- \
  probe path/to/capture.json --all --cases 256 \
  [--endian big|little] [--strict-v1 | --profile-v2] [--include-unsafe]
```

For non-byte-slice references, raw pointers, or explicit caller memory (where
`--arg` is unsupported), pass `--query <query.json>` (control the step budget on
the CLI via `--fuel <n>`). The file deserializes `Query` (`args`: tagged `Val`
array; optional `caller_mem`: `CallerMemory` with `allocations` whose `bytes`
entries are `{ "kind": "init", "byte": <u8>, "prov": <u64|null> }` or
`{ "kind": "uninit" }`; thin pointers use `"kind": "ptr"`):

```json
{
  "args": [
    {
      "kind": "slice_ptr",
      "value": {
        "ptr": { "alloc_id": 2, "offset_bytes": 0, "width": "isize" },
        "len": 3
      }
    },
    {
      "kind": "scalar",
      "value": { "width": "isize", "signed": false, "bits": "1" }
    }
  ],
  "caller_mem": {
    "allocations": [
      {
        "alloc_id": 2,
        "align_log2": 0,
        "mutability": "shared",
        "bytes": [
          { "kind": "init", "byte": 1, "prov": null },
          { "kind": "init", "byte": 2, "prov": null },
          { "kind": "init", "byte": 3, "prov": null }
        ],
        "live": true
      }
    ]
  }
}
```

Exit codes for `eval` and `probe`:

- `0`: For `eval`, execution returned or unwound without UB (`Returned` or
  `Unwound`). For `probe`, no modeled Undefined Behavior, `Unsupported` fault,
  `OutOfFuel` timeout, or unprobed parameter shape occurred (inspect `cases=`,
  `ok=`, `ub=`, `replayable=`, `model_only_unreplayed=`, and `skipped_unsafe`
  entries).
- `1`: CLI usage, file I/O, or JSON/argument parse error.
- `2`: Modeled Rust Undefined Behavior (`FaultKind::Undefined`) encountered.
- `3`: `eval` or `probe` hit `FaultKind::Unsupported`, `Outcome::OutOfFuel`, or
  an unsupported parameter shape.
- `4`: Reserved for `Outcome::Aborted` (kept for API exhaustiveness; not
  emitted by `Trusted.MirSemantics` Profile v1 or Profile v2 execution).

## Miri Witness-Replay Gate

`tests/witness_replay.rs` enforces the anti-bypass invariants of
`gate_witness_replay` (rejecting exit `0`, compiler errors, ordinary panics,
and promotion of `model_only_unreplayed` or unclassified witnesses) and runs
live Miri witness replay on a fixed set of five representative UB scenarios:
verbatim `zerocopy/proofs/08_byte_slice_split_at_unchecked`, `unchecked_add`
overflow, out-of-bounds `ptr.add`, null `raw_ptr_deref`, and misaligned `u32`
dereference (plus a `dead_ptr.add(0)` contrast classified as
`model_only_unreplayed`). Other `ReplayableMiriUb` classes (such as division by
zero, signed division overflow, dead-local access, and escaping stack
references) are covered by unit semantics tests rather than live Miri replay.

- **Default stable CI (`ci/scripts/run_anneal_mir_eval_check.sh`)**: runs all
  probe witness extractions and anti-bypass gate unit tests on every run, and
  automatically executes live Miri replay whenever one of the auto-detected
  candidate toolchains (`nightly-2026-05-31`, `nightly-2026-09-30`, or unpinned
  `nightly`) is already installed in `rustup toolchain list` with the `miri`
  component in `rustup component list --installed` and an offline-ready Miri
  sysroot. Other installed Miri nightlies are not auto-detected; select them
  explicitly via `ANNEAL_MIRI_TOOLCHAIN=<toolchain>`.
- **`ANNEAL_REQUIRE_MIRI_REPLAY=1`**: turns missing Miri into a hard test
  failure instead of skipping the live Miri subprocess check.
- **`ANNEAL_MIRI_TOOLCHAIN=<toolchain>`**: pins the exact `cargo +<toolchain>
  miri` toolchain to run (including dated nightlies outside the default
  auto-detection list, failing closed if that toolchain is uninstalled or
  unusable instead of falling back to another nightly).
