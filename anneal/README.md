<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal

Anneal is a verification framework for Rust under active development. See
[`PRINCIPLES.md`](PRINCIPLES.md) for the current project principles.

## Repository layout

The current verifier builds from this directory. The independent workspaces
in [`v1/`](v1/) and [`v2/`](v2/) retain the earlier implementations
and the Aeneas toolchain used by V1.

Zerocopy's [Anneal workflow](../.github/workflows/anneal.yml) calls the
[current verifier checks](../.github/workflows/anneal-current.yml). The
standalone release and review workflows under this directory are retained
for reference. This integration enables CI for the current verifier.
The existing V1 workflow continues to own publication.

## Correctness policy and `trusted/`

[`PRINCIPLES.md`](PRINCIPLES.md) promises that if the code in a verification
result's TCB audit log is correct, its assumptions are valid, and Anneal emits
no errors, then the verified code is correct. A **verification result** asserts
that:

1. its **TCB** satisfies its **trust policy**, and
2. if the trusted code in its **TCB** is correct, and its trusted assumptions
   are jointly valid, then its requested **claim** holds.

The `trusted/` directory isolates every first-party component of Anneal on
which those two assertions depend without checked evidence. The invariant of
`trusted/` is that **auditing `trusted/` and its explicit, pinned dependency
manifest is sufficient to verify that Anneal upholds
[`PRINCIPLES.md`](PRINCIPLES.md)**: an auditor never needs to inspect
first-party code outside `trusted/` to trust a verification result. This must
remain true in the face of adversarial implementations in any other part of
the repository.

To keep the human audit surface tractable and reliable, `trusted/` permits
battle-tested, widely-used external libraries for routine utilities (such as
command-line flag parsing, serialization, and trace logging). Using established
libraries for generic infrastructure is strongly preferred over hand-rolling
bespoke implementations inside `trusted/`, which inflates audit burden and
invites defect-prone reinvented wheels.

(Currently, `.github` is an exception to this rule, although we aim to tighten
that as well.)

## Design documentation

- [`PRINCIPLES.md`](PRINCIPLES.md): Anneal's mission, correctness promise, and
  decision-making priority order.
- [`docs/design.md`](docs/design.md): Overall system design, end-to-end
  verification workflow, library-centric verification, multi-modal
  specifications, and incremental adoption.
- [`docs/architecture.md`](docs/architecture.md): The three-stage MIR pipeline,
  repository layout, `rustc` extraction lifecycle, and multi-version toolchain
  strategy.
- [`docs/trust-model.md`](docs/trust-model.md): The `trusted/` vs. `theory/`
  boundary, Statement-Origin Separation, and repository CI boundary auditing.
