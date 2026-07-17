<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Current V2 priorities

**Snapshot date: 2026-07-17. This page is volatile and non-normative.**

This page helps an agent apply Anneal's long-term principles to the early V2
implementation. It describes a useful near-term optimization lens, not an
accepted roadmap or a new ordering among the project's values. An explicit
task from the project authors, the [normative design](../README.md#normative-design),
and accepted decisions take precedence.

## Starting point

The checked-in V2 executable implements toolchain setup, installation, and
supporting archive infrastructure. It does not yet discover a Rust artifact,
invoke Charon or Aeneas as a verification pipeline, generate proof obligations,
check an application proof, or issue a verification result. Read
[current architecture](current-architecture.md) and
[current limitations](current-limitations.md) before planning from this page.

Open and stacked pull requests explore nearby pipeline stages. They are useful
evidence about active engineering and integration pressure, but neither their
existence nor their implementation choices make them authoritative. Check the
current tree, tests, and history before claiming a capability has landed. The
[research index](../history/research-index.md) is only a dated navigation aid.

## Near-term optimization lens

Absent more specific direction, prefer work that turns the setup-only
foundation into a dependable, inspectable pipeline one reviewable stage at a
time. In practice, high-leverage work tends to have several of these
properties:

- It makes the pinned Rust, Charon, Aeneas, Lean, and supporting artifacts
  reproducible, installable, testable, or diagnosable.
- It connects a concrete Cargo compilation artifact to the next pipeline stage
  through an explicit, machine-readable interface.
- It preserves compilation-subject identity and verification provenance rather
  than relying on ambient state or an unreported default.
- It has a focused test that demonstrates the capability on the checked-in
  branch and fails clearly when a dependency or stage is unavailable.
- It improves failure reporting and makes unsupported coverage or trust visible
  rather than treating absence as success.
- It uses maintained Charon, Aeneas, Lean, Cargo, or rustc interfaces where
  they fit, while keeping an upstream change in scope when that is the cleaner
  long-term boundary.
- It is narrow enough to land without prematurely fixing an open semantic,
  annotation, proof-authoring, or command-policy design.

This lens favors durable enabling infrastructure over speculative completion
of the entire verifier. It does not make infrastructure more important than
soundness: any stage that begins making semantic claims must satisfy the
[settled requirements](../design/settled-requirements.md) and preserve the
[trust model](../design/trust-model.md).

## Working near the pipeline frontier

Nearby work may involve Cargo target and artifact resolution, Charon execution,
LLBC transport, Aeneas generation, dependency discovery, Lake workspaces,
diagnostic mapping, or toolchain fixups. Treat that list as a description of
the engineering neighborhood, not a prescribed sequence or component boundary.

For each change:

1. Establish what is already present in this checkout; do not plan against a
   sibling worktree or an open PR by accident.
2. Name the concrete input, output, and failure modes of the stage being added.
3. Preserve enough identity and provenance to relate its output to the fixed
   [compilation subject and verification result](../design/verification-artifact.md).
4. Test the stage independently where practical and test the newly connected
   boundary end to end.
5. Update current-state references only after the capability is checked in.
6. If the implementation would choose an answer recorded as open, pause for
   explicit agreement or frame the work as a reversible experiment.

In particular, pipeline plumbing must not incidentally settle the source of
annotation metadata, the Anneal/Aeneas/Charon ownership boundary, the unsafe
memory model, proof arguments versus sidecar theorems, or the final property
and outcome taxonomy. Those questions and their settled constraints live in
the [open-question index](../design/open-questions/README.md).

## What not to optimize for yet

Do not infer that the project currently wants:

- a broad but unaudited claim of Rust coverage;
- compatibility with V1 syntax or architecture for its own sake;
- a polished `verify` success mode before its claim and trust reporting are
  defined;
- local textual patches when a robust programmatic boundary is available; or
- premature generalization across target, feature, or configuration matrices
  when the settled initial unit is one fixed compilation artifact.

These cautions do not forbid experiments. They require experiments to be
identified as such and prevent temporary scaffolding from silently becoming a
project-wide decision.

## Refreshing this page

Revalidate this snapshot whenever the checked-in executable gains a pipeline
stage or project authors state a new near-term priority. Keep volatile work
sequencing here, current facts in the other `reference/` pages, and lasting
constraints or decisions in `design/`. Remove priorities that no longer help
choose work; do not preserve them as historical authority.
