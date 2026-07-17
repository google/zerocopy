<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal V2 agent guide

This file governs work in `anneal/`, except that work under `anneal/v1/` must
also follow the more specific `v1/AGENTS.md`.

Anneal V2 is a clean-room, ground-up rewrite and redesign. V1 is an
experimental prototype from which we draw evidence and lessons; it is not a
default architecture, specification language, or user interface for V2. Copy
from it when a choice has been reconsidered and remains appropriate, not merely
because code already exists.

## Mission

Anneal's long-term goal is to let Rust users verify arbitrarily subtle
correctness properties for arbitrary Rust codebases. This requires a general
framework for user-defined properties and unusually strong support for the
memory-safety reasoning needed by unsafe-heavy systems code.

Soundness is special and non-negotiable. Rust compilers and Anneal's source
models need not preserve the behavior of a program after undefined behavior.
Anneal must therefore establish the soundness conditions on which its own
model fidelity depends. Functional correctness, panic freedom, protocol
correctness, resource bounds, and other properties may be selected or defined
by users; they may depend on soundness and on one another.

Read [the design principles](docs/design/principles.md) for the project's value
function and [the settled requirements](docs/design/settled-requirements.md) for
the constraints every design must satisfy.

## Required reading

When entering from an unfamiliar checkout or worktree, first use the
[agent-corpus preflight](docs/agent-corpus.md) to confirm that you have found
Anneal V2 rather than V1 or a sibling worktree.

Before making a design change, read:

1. The [documentation map](docs/README.md) and
   [glossary](docs/glossary.md).
2. [Design principles](docs/design/principles.md).
3. [Settled requirements](docs/design/settled-requirements.md).
4. The [accepted-decision index](docs/design/decisions/README.md) and each
   accepted decision relevant to the change.
5. [Verification model](docs/design/verification-model.md),
   [verification subject and result identity](docs/design/verification-artifact.md), and
   [trust model](docs/design/trust-model.md).
6. The [worked example](docs/design/worked-example.md), remembering that its
   concrete proof shape is illustrative rather than decided.
7. The relevant file in
   [open design questions](docs/design/open-questions/README.md).
8. [Current architecture](docs/reference/current-architecture.md),
   [current limitations](docs/reference/current-limitations.md), and the
   explicitly non-normative
   [current priorities](docs/reference/current-priorities.md).

For work involving translation or proof infrastructure, also read
[Aeneas and Charon](docs/reference/aeneas-and-charon.md). For a question shaped
by V1, read [V1 lessons](docs/history/v1-lessons.md) and then inspect the V1
implementation itself.

## How to make judgment calls

Apply these rules together rather than as a rigid total ordering:

- Preserve soundness. Do not gain simplicity, coverage, or convenience by
  weakening a soundness obligation or silently adding trust.
- Preserve semantic fidelity. A simple model is valuable only while it
  faithfully supports the claim Anneal makes. Resource ownership, provenance,
  initialization, concurrency protocols, or effects must not become freely
  duplicable facts when doing so could invalidate soundness.
- Prefer local, compositional reasoning. The key scalability property is that
  an implementation can be checked against an abstraction boundary and then
  used without re-examining the whole program.
- Prefer the simplest faithful abstraction. Pure functional contracts are
  excellent where they capture the interface; resource- or effect-aware
  interfaces are required where purity would discard soundness-relevant facts.
- Make trust explicit and auditable. A trusted leaf can be a legitimate
  engineering boundary; a hidden assumption or uncovered operation cannot.
- Build on maintained Lean, Aeneas, and Charon abstractions when they fit.
  Reinvention is permitted, but should carry a concrete benefit that outweighs
  duplicated semantics and maintenance.
- Prefer robust programmatic interfaces over textual patching. Upstream changes
  to Aeneas, Charon, Lean libraries, and Rust itself are in scope. Choose
  upstream or downstream ownership case by case, including the burden placed on
  collaborators.
- Optimize for useful coverage, evolvability, debuggability, and eventual use
  by ordinary Rust engineers. AI assistance is expected to help, but may not be
  used to excuse an incoherent or unauditable interface.
- Support incremental adoption without confusing an assumption with a proof.
  Prose safety justifications and incomplete proofs must remain visible in the
  resulting trust or coverage report.
- Fail closed relative to the exact claim and command mode being reported.
  Unsupported semantics, missing coverage, or an undischarged obligation may
  never produce an unconditional verification claim. An explicitly named
  incremental mode may report a weaker conditional result only when every
  assumption and incomplete obligation is part of that result; command names
  and exit policies remain open.

When principles conflict, state the conflict and justify the tradeoff in those
terms. Do not invent a permanent priority ordering from one local decision.

## Settled constraints and open designs

The documentation taxonomy is defined in [docs/README.md](docs/README.md).
In brief:

- `docs/design/` states the normative intent.
- Accepted records in `docs/design/decisions/` capture settled choices and
  their rationale.
- `docs/design/open-questions/` records constraints, candidates, and evidence,
  not decisions.
- `docs/reference/` describes the checked-in implementation and may change as
  the code changes.
- `docs/history/` is evidence, not authority.

Do not resolve an open question incidentally in implementation code. Before a
change commits the project to an answer, obtain explicit agreement from the
project authors. With that agreement, add or update an accepted decision record
and reconcile the normative documents. Without it, keep the record proposed,
describe the implementation as an experiment, or stop and surface the choice.
If documents conflict, surface the conflict instead of silently selecting the
convenient text.

In particular, the following remain open unless an accepted decision says
otherwise:

- the final property/outcome taxonomy;
- whether proof obligations are encoded as Lean arguments or sidecar theorems;
- how Anneal's property tracking builds on or parallels Rust's `unsafe`
  machinery;
- the annotation and proof-authoring syntax;
- the precise boundary among Anneal, Aeneas, Charon, and rustc;
- the exact audit-ledger schema and success modes of `cargo anneal verify`.

Do not describe a candidate from an issue, PR, V1, or an open-question document
as settled.

## Current implementation

The checked-in V2 executable currently provides toolchain setup scaffolding;
much of the intended verification pipeline is not yet present on this branch.
Open and stacked PRs may contain additional implementation, but are not the
source of truth for the checked-in tree. See
[current architecture](docs/reference/current-architecture.md).

From the repository root, useful checks are:

```bash
cargo test --locked --manifest-path anneal/Cargo.toml
cargo fmt --check --manifest-path anneal/Cargo.toml --all
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s anneal/tests -p 'test_*.py'
bash anneal/check-flake-eval.sh
```

Tests behind the `exocrate_tests` feature expect CI to place a prebuilt archive
at `anneal/target/anneal-exocrate.tar.zst`.

V1 has different commands and a different architecture. Follow
`anneal/v1/AGENTS.md` when working there.

## Documentation maintenance

- Update design documentation in the same change that alters a settled
  contract, trust boundary, or project-wide constraint.
- Give requirements stable identifiers and link implementation decisions back
  to them.
- Record meaningful rejected alternatives; do not preserve conversational
  misunderstandings after the terminology has been clarified.
- Date volatile research notes and link primary sources. Issues and PRs are
  guides to thinking, not authoritative specifications.
- Keep current-state reference documents honest about what exists today and
  separate from intended architecture.
- Prefer links to the canonical explanation over copying it into agent-only
  prose.
