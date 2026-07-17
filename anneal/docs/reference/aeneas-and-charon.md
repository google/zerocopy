<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Aeneas and Charon

Anneal is being developed in collaboration with the
[Charon](https://github.com/AeneasVerif/charon) and
[Aeneas](https://github.com/AeneasVerif/aeneas) projects. This page records the
revision-sensitive facts contributors need when working on that integration;
it does not assign future responsibilities among the projects.

Upstream documentation and source are authoritative for a pinned release. This
page was last reviewed on 2026-07-17, when `anneal/flake.nix` selected Aeneas
release `nightly-2026.06.03`. Recheck the current pin before relying on a
supported construct, result type, or API described here.

## Charon: compiler-integrated extraction

Charon runs with the Rust compiler and exports Rust programs into LLBC (Low
Level Borrow Calculus), an intermediate representation designed for formal
reasoning. In the reviewed toolchain it provides compiler-resolved program
information after macro expansion and conditional compilation, including
resolved types, control flow, and source spans.

Charon is not a verifier. Successful extraction means that it produced LLBC
for the selected compilation; it does not prove that the source is sound or
that a later Lean model is adequate.

LLBC currently serves as Aeneas's semantic input. It can also provide
compiler-authoritative facts against which Anneal may reconcile annotations,
contracts, operations, calls, and diagnostics. Whether ordinary LLBC is
sufficient or another compiler-resolved interface is needed remains open.

## Aeneas: functional translation and proof support

Aeneas consumes LLBC and translates supported Rust into definitions in proof
assistants, including Lean. For a useful subset of Rust whose mutation follows
ordinary borrowing, this produces pure functional transformations rather than
an explicit whole-program heap model. Mutable-borrow translations carry the
information needed to reconstruct the final borrowed value.

In the revision reviewed for this page, the Aeneas Lean library includes
weakest-precondition specifications and tactics such as `step` and `step*`.
Their exact interfaces and supported semantic envelope are revision-sensitive
and must be checked against the current pin.

Aeneas does not by itself establish adequacy for every Rust program. Anneal's
questions about unsupported operations, resource-sensitive semantics,
exceptional execution, and the source-to-model correspondence are tracked in
the design documents linked below.

## Checked-in Anneal integration

The checked-in Anneal executable does not yet translate applications or verify
contracts. It currently packages and installs the pinned Aeneas distribution,
including the Aeneas and Charon executables and the Aeneas Lean libraries, and
constructs a Lean workspace which imports those libraries. See the
[current state](current-state.md) for the authoritative implementation summary.

Anneal obtains the distribution from Aeneas's published
`nightly-2026.06.03` archive through `anneal/flake.nix`. The archive contains
Charon as part of the bundled toolchain; the checked-in setup does not maintain
a separate Charon pin.

## Design questions owned elsewhere

This reference intentionally does not decide what Charon should expose, what
semantics Aeneas should own, whether Anneal should extend either project, or
which downstream adaptations are acceptable. Those choices are governed by
the [project principles](../design/principles.md) and tracked in:

- [Aeneas and Charon integration](../design/open-questions/aeneas-charon-integration.md);
- [source/model adequacy](../design/open-questions/source-model-adequacy.md);
- [memory, resources, and effects](../design/open-questions/memory-resources-and-effects.md); and
- [proof authoring and user experience](../design/open-questions/proof-authoring-and-user-experience.md).

Experience from Anneal's earlier Aeneas integration is recorded separately in
[V1 lessons](../history/v1-lessons.md).
