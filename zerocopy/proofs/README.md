<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Zerocopy Semi-Verification Proofs (`zerocopy/proofs`)

> [!WARNING]
> **This is alpha software!** Anneal (`0.2.0-alpha`, Stage 0) has not yet
> completed an independent TCB audit. The units below verify **9 currently
> capturable scalar, unit, and empty sentinel functions** in `../src/` under
> Profile v1 and **4 byte-slice functions** under the experimental Profile v2
> (`x86_64-unknown-linux-gnu`, `-C opt-level=0`,
> `no_zerocopy_allocator_api_1_100_0` only). Passing CI here **does not** verify
> other pointer or slice operations (`Ref`, `Ptr`, `transmute!`), Cargo features
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
and marker-sentinel items and 4 verbatim Profile v2 byte-slice items in
`../src/`.

The Profile v2 units (`06_*` and `08_*`) rest on additional assumptions,
described in [Profile v2][profile-v2-doc]. Profile v2 has no aliasing model:
the theorems quantify only over entries whose reference arguments are valid,
initialized, and, for `&mut`, disjoint, and receipts record these as
assumptions. Receipts also mark `correspondence_provenance` inapplicable,
because the `lean-miri` correspondence covers only Profile v1 rules.

[profile-v2-doc]: ../../anneal/docs/alpha.md#experimental-mir-profile-v2-borrowed-slices-and-raw-pointers

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
| `06_byte_slice_into_byte_slice` | `<&[u8] as IntoByteSlice>::into_byte_slice`, `<&mut [u8] as IntoByteSlice>::into_byte_slice`, `<&mut [u8] as IntoByteSliceMut>::into_byte_slice_mut` | Profile v2 stability over all valid entries and caller memory: each body is well-formed and returns the same slice address and length with caller memory unchanged as its only terminal behavior | `["propext"]` |
| `08_byte_slice_split_at_unchecked` | `<&[u8] as SplitByteSlice>::split_at_unchecked` | Profile v2 (`UnitTheoremV2`) over all valid entries satisfying `mid <= len`, execution reaches a return of `(s[..mid], s[mid..])` (second slice at `addr + mid`, lengths summing to `len`) with caller memory unchanged | `["propext"]` |

## Reproducing Locally

Run the CI driver against unmodified `zerocopy/src/` from the repository root:

```sh
python3 -I -B anneal/ci/verify_zerocopy.py
```

Or run `cargo anneal verify` on an individual unit:

```sh
cargo anneal verify --request zerocopy/proofs/01_usize_pointer_metadata/request.json
```
