<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal Research Index

**Snapshot date: 2026-07-17.**

Issues and pull requests record experiments, incomplete arguments, and views
which may already have changed. They are evidence and prompts for further
thinking, never normative design. Before relying on one, check its current
status, stack position, discussion, and diff. Normative constraints live in
[`agent_docs/design/`](../design/).

## Coordinating issue

[Tracking issue #3016](https://github.com/google/zerocopy/issues/3016) is the
best entry point into the work. At this snapshot it organizes work around:

- making the implementation and infrastructure suitable for external
  contribution;
- manually formalizing Rust from generated Lean in order to discover the
  abstractions automation should eventually produce;
- separation-logic support in Aeneas;
- user-facing annotation and proof syntax; and
- internal code generation and organization.

Its milestone and workstream wording is a planning snapshot, not a contract.
Use [principles](../design/principles.md),
[settled requirements](../design/settled-requirements.md), and the
[open-question index](../design/open-questions/README.md) to interpret it.

## Open V2 and cross-cutting pull requests

The following PRs were returned as open by a repository query on the snapshot
date. Many are GHerrit-managed stacked changes, so adjacent PRs can overlap or
be rebased together. Open status is not evidence that a change is absent from
this checkout: an open PR may be a stack ancestor or the current branch.
Inspect the tree and history to determine what is present, and use
[the current implementation state](../reference/current-state.md) for the
checked-in behavior rather than treating PR descriptions as authoritative.

### Current orchestration and toolchain stack

- [#3474: Compile merged util module at stack base](https://github.com/google/zerocopy/pull/3474)
- [#3463: Include Cargo in the exocrate Rust toolchain](https://github.com/google/zerocopy/pull/3463)
- [#3400: Add exocrate toolchain setup and `Toolchain` resolver](https://github.com/google/zerocopy/pull/3400)
- [#3401: Add Cargo workspace and target resolution](https://github.com/google/zerocopy/pull/3401)
- [#3402: Map workspace packages to `AnnealArtifact`s](https://github.com/google/zerocopy/pull/3402)
- [#3418: Add a pinned `charon_lib` dependency](https://github.com/google/zerocopy/pull/3418)
- [#3404: Add the Charon execution engine, `generate` CLI, and integration tests](https://github.com/google/zerocopy/pull/3404)
- [#3405: Chase out-of-tree dependencies for generation](https://github.com/google/zerocopy/pull/3405)
- [#3485: Prime Lake traces in one server traversal](https://github.com/google/zerocopy/pull/3485)
- [#3486: Audit cached Lean artifacts against clean builds](https://github.com/google/zerocopy/pull/3486)
- [#3403: Map compiler diagnostics back to Rust source](https://github.com/google/zerocopy/pull/3403)
- [#3436: Add an exocrate install-fixup hook](https://github.com/google/zerocopy/pull/3436)

These changes are useful evidence about Cargo artifact identity, Charon
integration, diagnostics, cache portability, and the cost of dependency
chasing. They do not settle the long-term Anneal/Aeneas/Charon boundary.

### Earlier or parallel V2 infrastructure

- [#3361: Introduce Nix-based toolchain management](https://github.com/google/zerocopy/pull/3361)
- [#3362: Initial `setup` implementation](https://github.com/google/zerocopy/pull/3362)
- [#3378: Pass manifest and lockfile paths explicitly through exocrate](https://github.com/google/zerocopy/pull/3378)
- [#3487: Reorganize Anneal V1 and V2](https://github.com/google/zerocopy/pull/3487)

Some effects of these proposals may already exist through different merged
commits. Read the current tree before assuming an open PR remains the intended
route.

## Other open Anneal PRs: primarily V1 evidence

These PRs were also open at the snapshot date. Most target the prototype or
pre-date the clean V2 boundary. They belong in historical research, not in the
V2 implementation plan by default.

### Annotation, naming, and verification experiments

- [#3478: Preserve module paths in generated function names](https://github.com/google/zerocopy/pull/3478)
- [#3477: Validate `isSafe` trait invariants while parsing](https://github.com/google/zerocopy/pull/3477)
- [#3321: Replace annotation syntax with verbatim Lean](https://github.com/google/zerocopy/pull/3321)
- [#3320: Translate and verify integration tests for the new syntax](https://github.com/google/zerocopy/pull/3320)
- [#3261: Add Lake package-management files](https://github.com/google/zerocopy/pull/3261)

### Build, cache, and release experiments

- [#3339: Remove redundant integration-test harness code](https://github.com/google/zerocopy/pull/3339)
- [#3338: Avoid copying Lean dependencies into the build directory](https://github.com/google/zerocopy/pull/3338)
- [#3337: Update integration tests for Nix](https://github.com/google/zerocopy/pull/3337)
- [#3336: Replace Docker with Nix](https://github.com/google/zerocopy/pull/3336)
- [#3335: WIP experimental changes](https://github.com/google/zerocopy/pull/3335)
- [#3334: WIP Docker-to-Nix conversion](https://github.com/google/zerocopy/pull/3334)
- [#3327: Download and install artifacts in parallel](https://github.com/google/zerocopy/pull/3327)
- [#3298: Adopt the Lake artifact cache and share workspace packages](https://github.com/google/zerocopy/pull/3298)
- [#3285: Overhaul release artifact and PR generation](https://github.com/google/zerocopy/pull/3285)
- [#3258: Roll prebuilts](https://github.com/google/zerocopy/pull/3258)
- [#3255: Reuse prebuilt Lean artifacts in generated workspaces](https://github.com/google/zerocopy/pull/3255)

The repeated approaches are themselves evidence: setup latency, hermeticity,
Lake cache relocation, release provenance, and clean-build equivalence are
important engineering problems. No abandoned mechanism should be revived
solely because several old PRs explored it.

## Issue map by research question

The tracking discussion and repository issue search surfaced the following
threads. Open or closed status does not determine whether the underlying
question is settled.

### Semantic coverage and artifact identity

- [#3041: What about unreachable code?](https://github.com/google/zerocopy/issues/3041)
  asks whether MIR elimination before Charon can hide code or produce a
  misleading coverage claim. This is the concrete form of the question about
  extraction before optimizations which assume or erase behavior.
- [#3017: Support `#[cfg]` in verification targets](https://github.com/google/zerocopy/issues/3017)
  motivates making one resolved compilation artifact the source of truth.
- [#3350: Imported Rust types get unqualified names in generated specs](https://github.com/google/zerocopy/issues/3350)
  illustrates the danger of a source-derived shadow naming system.

### Trust, axioms, and proof completeness

- [#3206: Ban axioms in non-axiom annotations](https://github.com/google/zerocopy/issues/3206)
  is evidence for syntactic and semantic auditing of the Lean environment.
- [#3110: Visit all annotations and reject invalid locations](https://github.com/google/zerocopy/issues/3110)
  concerns fail-closed coverage rather than only parsing supported locations.

### Proof authoring and syntax

- [#3201: Interactive proofs tracking](https://github.com/google/zerocopy/issues/3201)
- [#3062: Write Anneal specifications in Rust](https://github.com/google/zerocopy/issues/3062)
- [#3218: Make an entire annotation one Lean AST](https://github.com/google/zerocopy/issues/3218)
- [#3090: Pretty-print generated Lean](https://github.com/google/zerocopy/issues/3090)
- [#3086: Parse attributes with `chumsky`](https://github.com/google/zerocopy/issues/3086)
- [#3057: Support non-indented comments](https://github.com/google/zerocopy/issues/3057)

These record syntax and tooling experiments. V2 has not selected a surface
language or proof location.

### Hermeticity, packaging, and contributor workflow

- [#3331: Manage all toolchain dependencies hermetically](https://github.com/google/zerocopy/issues/3331)
- [#3259: Build `Anneal.lean` independently in CI and locally](https://github.com/google/zerocopy/issues/3259)
- [#3256: Minimize dependencies of `Anneal.lean` and generated Lean](https://github.com/google/zerocopy/issues/3256)
- [#3266: Sanitize Cargo values used in Docker image creation](https://github.com/google/zerocopy/issues/3266)
- [#3420: Use standard base directories instead of polluting home directories](https://github.com/google/zerocopy/issues/3420)
- [#3060: Embed assets in the Anneal binary](https://github.com/google/zerocopy/issues/3060)

Later Nix/exocrate work answers parts of these issues through different
mechanisms. Re-evaluate the underlying requirement rather than assuming the
issue's proposed implementation is still current.

## Upstream reading

- [Charon repository and documentation](https://github.com/AeneasVerif/charon)
- [Aeneas repository and documentation](https://github.com/AeneasVerif/aeneas)
- [Lean reference manual](https://lean-lang.org/doc/reference/latest/)
- [Rust Reference: behavior considered undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)
- [Rust Unsafe Code Guidelines reference](https://rust-lang.github.io/unsafe-code-guidelines/)
- [RustBelt project and papers](https://plv.mpi-sws.org/rustbelt/)

Read the pinned Aeneas and Charon revisions used by `flake.nix`, not only their
latest default branches. Anneal collaborates with both projects, so upstream
changes are possible; current upstream behavior remains distinct from a
proposed extension. The concise Anneal-specific division of responsibility is
in [Aeneas and Charon](../reference/aeneas-and-charon.md).

## Maintaining this index

When refreshing the snapshot:

1. record the new date;
2. query current issue and PR state rather than copying this list;
3. preserve historically useful links under an explicitly historical heading;
4. summarize what question a source informs, not what decision it allegedly
   dictates; and
5. move a conclusion into normative documentation only after the project has
   actually accepted it.
