<!-- Copyright 2024 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.

WARNING: DO NOT EDIT THIS FILE. It is generated automatically. Edits should be
made in the doc comment on `src/lib.rs` or in `tools/generate-readme`.
-->

# zerocopy

***<span style="font-size: 140%">Fast, safe, <span
style="color:red;">compile error</span>. Pick two.</span>***

Zerocopy makes zero-cost memory manipulation effortless. We write `unsafe`
so you don't have to.

*For an overview of what's changed from zerocopy 0.7, check out our [release
notes][release-notes], which include a step-by-step upgrading guide.*

*Have questions? Need more out of zerocopy? Submit a [customer request
issue][customer-request-issue] or ask the maintainers on
[GitHub][github-q-a] or [Discord][discord]!*

[customer-request-issue]: https://github.com/google/zerocopy/issues/new/choose
[release-notes]: https://github.com/google/zerocopy/discussions/1680
[github-q-a]: https://github.com/google/zerocopy/discussions/categories/q-a
[discord]: https://discord.gg/MAvWH2R6zk

## Overview

###### Conversion Traits

Zerocopy provides four derivable traits for zero-cost conversions:
- `TryFromBytes` indicates that a type may safely be converted from
  certain byte sequences (conditional on runtime checks)
- `FromZeros` indicates that a sequence of zero bytes represents a valid
  instance of a type
- `FromBytes` indicates that a type may safely be converted from an
  arbitrary byte sequence
- `IntoBytes` indicates that a type may safely be converted *to* a byte
  sequence

These traits support sized types, slices, and [slice DSTs][slice-dsts].

[slice-dsts]: KnownLayout#dynamically-sized-types

###### Marker Traits

Zerocopy provides three derivable marker traits that do not provide any
functionality themselves, but are required to call certain methods provided
by the conversion traits:
- `KnownLayout` indicates that zerocopy can reason about certain layout
  qualities of a type
- `Immutable` indicates that a type is free from interior mutability,
  except by ownership or an exclusive (`&mut`) borrow
- `Unaligned` indicates that a type's alignment requirement is 1

You should generally derive these marker traits whenever possible.

###### Conversion Macros

Zerocopy provides six macros for safe casting between types:

- (`try_`[try_transmute])`transmute` (conditionally) converts a value of
  one type to a value of another type of the same size
- (`try_`[try_transmute_mut])`transmute_mut` (conditionally) converts a
  mutable reference of one type to a mutable reference of another type of
  the same size
- (`try_`[try_transmute_ref])`transmute_ref` (conditionally) converts a
  mutable or immutable reference of one type to an immutable reference of
  another type of the same size

These macros perform *compile-time* size and alignment checks, meaning that
unconditional casts have zero cost at runtime. Conditional casts do not need
to validate size or alignment runtime, but do need to validate contents.

These macros cannot be used in generic contexts. For generic conversions,
use the methods defined by the [conversion traits](#conversion-traits).

###### Byteorder-Aware Numerics

Zerocopy provides byte-order aware integer types that support these
conversions; see the `byteorder` module. These types are especially useful
for network parsing.

## Cargo Features

- **`alloc`**
  By default, `zerocopy` is `no_std`. When the `alloc` feature is enabled,
  the `alloc` crate is added as a dependency, and some allocation-related
  functionality is added.

- **`std`**
  By default, `zerocopy` is `no_std`. When the `std` feature is enabled, the
  `std` crate is added as a dependency (ie, `no_std` is disabled), and
  support for some `std` types is added. `std` implies `alloc`.

- **`derive`**
  Provides derives for the core marker traits via the `zerocopy-derive`
  crate. These derives are re-exported from `zerocopy`, so it is not
  necessary to depend on `zerocopy-derive` directly.

  However, you may experience better compile times if you instead directly
  depend on both `zerocopy` and `zerocopy-derive` in your `Cargo.toml`,
  since doing so will allow Rust to compile these crates in parallel. To do
  so, do *not* enable the `derive` feature, and list both dependencies in
  your `Cargo.toml` with the same leading non-zero version number; e.g:

  ```toml
  [dependencies]
  zerocopy = "0.X"
  zerocopy-derive = "0.X"
  ```

  To avoid the risk of [duplicate import errors][duplicate-import-errors] if
  one of your dependencies enables zerocopy's `derive` feature, import
  derives as `use zerocopy_derive::*` rather than by name (e.g., `use
  zerocopy_derive::FromBytes`).

- **`simd`**
  When the `simd` feature is enabled, `FromZeros`, `FromBytes`, and
  `IntoBytes` impls are emitted for all stable SIMD types which exist on the
  target platform. Note that the layout of SIMD types is not yet stabilized,
  so these impls may be removed in the future if layout changes make them
  invalid. For more information, see the Unsafe Code Guidelines Reference
  page on the [layout of packed SIMD vectors][simd-layout].

- **`simd-nightly`**
  Enables the `simd` feature and adds support for SIMD types which are only
  available on nightly. Since these types are unstable, support for any type
  may be removed at any point in the future.

- **`float-nightly`**
  Adds support for the unstable `f16` and `f128` types. These types are
  not yet fully implemented and may not be supported on all platforms.

[duplicate-import-errors]: https://github.com/google/zerocopy/issues/1587
[simd-layout]: https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html

## Security Ethos

Zerocopy is expressly designed for use in security-critical contexts. We
strive to ensure that that zerocopy code is sound under Rust's current
memory model, and *any future memory model*. We ensure this by:
- **...not 'guessing' about Rust's semantics.**
  We annotate `unsafe` code with a precise rationale for its soundness that
  cites a relevant section of Rust's official documentation. When Rust's
  documented semantics are unclear, we work with the Rust Operational
  Semantics Team to clarify Rust's documentation.
- **...rigorously testing our implementation.**
  We run tests using [Miri], ensuring that zerocopy is sound across a wide
  array of supported target platforms of varying endianness and pointer
  width, and across both current and experimental memory models of Rust.
- **...formally proving the correctness of our implementation.**
  We apply formal verification tools like [Kani][kani] to prove zerocopy's
  correctness.

For more information, see our full [soundness policy].

[Miri]: https://github.com/rust-lang/miri
[Kani]: https://github.com/model-checking/kani
[soundness policy]: https://github.com/google/zerocopy/blob/main/POLICIES.md#soundness

## Relationship to Project Safe Transmute

[Project Safe Transmute] is an official initiative of the Rust Project to
develop language-level support for safer transmutation. The Project consults
with crates like zerocopy to identify aspects of safer transmutation that
would benefit from compiler support, and has developed an [experimental,
compiler-supported analysis][mcp-transmutability] which determines whether,
for a given type, any value of that type may be soundly transmuted into
another type. Once this functionality is sufficiently mature, zerocopy
intends to replace its internal transmutability analysis (implemented by our
custom derives) with the compiler-supported one. This change will likely be
an implementation detail that is invisible to zerocopy's users.

Project Safe Transmute will not replace the need for most of zerocopy's
higher-level abstractions. The experimental compiler analysis is a tool for
checking the soundness of `unsafe` code, not a tool to avoid writing
`unsafe` code altogether. For the foreseeable future, crates like zerocopy
will still be required in order to provide higher-level abstractions on top
of the building block provided by Project Safe Transmute.

[Project Safe Transmute]: https://rust-lang.github.io/rfcs/2835-project-safe-transmute.html
[mcp-transmutability]: https://github.com/rust-lang/compiler-team/issues/411

## MSRV

See our [MSRV policy].

[MSRV policy]: https://github.com/google/zerocopy/blob/main/POLICIES.md#msrv

## Changelog

Zerocopy uses [GitHub Releases].

[GitHub Releases]: https://github.com/google/zerocopy/releases

## Thanks

Zerocopy is maintained by engineers at Google and Amazon with help from
[many wonderful contributors][contributors]. Thank you to everyone who has
lent a hand in making Rust a little more secure!

[contributors]: https://github.com/google/zerocopy/graphs/contributors

## Disclaimer

Disclaimer: Zerocopy is not an officially supported Google product.
