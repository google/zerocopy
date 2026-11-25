<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Zerocopy Semi-Verification Proofs (`zerocopy/proofs`)

> [!WARNING]
> **This is alpha software!** Anneal (`0.2.0-alpha`, Stage 0) has not yet
> completed an independent TCB audit. The units below verify only **9 currently
> capturable scalar, unit, and empty sentinel functions** in `../src/` under
> Profile v1 (`x86_64-unknown-linux-gnu`, `-C opt-level=0`,
> `no_zerocopy_allocator_api_1_100_0` only). Passing CI here **does not** verify
> pointer or slice operations (`Ref`, `Ptr`, `transmute!`), Cargo features
> (`alloc`, `simd`, `derive`), or the `unsafe impl` safety contracts of marker
> traits such as `FromBytes` (only the empty
> `only_derive_is_allowed_to_implement_this_trait` sentinel methods are checked
> today). Treat passing runs as experimental alpha checks under intact-host
> assumptions and human review of stated specifications (each unit's primary
> specification module—here `Spec.lean`—plus any `specification`-role modules
> and their transitive meaning dependencies), `request.json`, CI workflows, and
> TCB audit logs (complete review-surface reporting remains under active
> development; see [alpha usage][alpha-doc] and [threat model][threat-doc]).

[alpha-doc]: ../../anneal/docs/alpha.md
[threat-doc]: ../../anneal/THREAT_MODEL.md

This directory contains out-of-line Anneal formal specifications and
kernel-checked Lean 4 proofs covering those 9 verbatim Profile v1 scalar/unit
and marker-sentinel items in `../src/`.

`../Cargo.toml` excludes `/proofs` from crates.io packages so downstream
`zerocopy` users incur zero new dependencies, zero MSRV impact, and zero build
overhead. CI continuously enforces every proof unit in
`../../.github/workflows/anneal-current.yml` via
`../../anneal/ci/verify_zerocopy.py`.

## Verified Units

| Unit | Verbatim `zerocopy/src/` Targets | Properties Proved | Axioms |
| --- | --- | --- | --- |
| `01_usize_pointer_metadata` | `<usize as PointerMetadata>::{from,to}_elem_count` | Total execution over all `2^64` `usize` inputs; two-way bijection round-trips; safe signatures (`isUnsafe = false`) | `["propext"]` |
| `02_unit_pointer_metadata` | `<() as PointerMetadata>::{from,to}_elem_count` | Universal constant `()` and `0usize` return; round-trip invariants; safe signatures (`isUnsafe = false`) | `["propext"]` |
| `03_macros_unsafe` | `util::macros::__unsafe` | Exact identity, `isUnsafe = true`, zero-argument signature, non-vacuous safety precondition, total `()` return | `["propext"]` |
| `04_substantive_and_frombytes_markers` | All 5 substantive scalar/unit/macro items above plus 4 `u8` derive-only sentinel methods (`only_derive_is_allowed_to_implement_this_trait` for `Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`; does not verify `unsafe impl` soundness) | Compositional 9-body `BodiesVerified` dispatch and functional postconditions | `["propext"]` |

## Reproducing Locally

Run the CI driver against unmodified `zerocopy/src/` from the repository root:

```sh
python3 -I -B anneal/ci/verify_zerocopy.py
```

Or run `cargo anneal verify` on an individual unit:

```sh
cargo anneal verify --request zerocopy/proofs/01_usize_pointer_metadata/request.json
```
