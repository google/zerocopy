<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal agent guide

This file governs work in `anneal/`. Work under `anneal/v1/` must also follow
the more specific `v1/AGENTS.md`.

Anneal is a clean-room, ground-up redesign of the experimental V1 prototype.
V1 is useful evidence, not a default architecture, specification language, or
user interface. Reuse a V1 idea or implementation only after evaluating it
against the current design.

## Mission

Anneal is a general verification tool for Rust, with unsafe-code soundness as
its foundational use case. It aims to let ordinary Rust teams verify subtle
properties of real Rust programs while preserving the guarantees expected of
safe Rust.

Soundness is non-negotiable. Rust compilers and Anneal's source models need not
preserve a program's behavior after undefined behavior, so Anneal must establish
the soundness conditions on which its own model fidelity depends. Never gain
simplicity, coverage, or convenience by weakening such a condition, silently
omitting an operation, or hiding trust.

## Start here

In an unfamiliar checkout, first complete the
[agent-corpus preflight](docs/agent-corpus.md). Then follow the canonical
[documentation map](docs/README.md), which owns the reading order, document
authority, and reconciliation procedure for the design canon.

## Working protocol

- Evaluate alternatives using the [design principles](docs/design/principles.md)
  and satisfy every applicable
  [settled requirement](docs/design/settled-requirements.md).
- Follow accepted decision records. Treat open-question documents, issues,
  pull requests, research, experiments, and V1 as evidence rather than settled
  authority.
- Do not settle an open design incidentally in implementation. Before a change
  commits the project to an answer, obtain explicit agreement from the project
  authors and record the accepted decision. Otherwise label the implementation
  as an experiment or surface the choice.
- If documents disagree, surface and reconcile the disagreement using the
  process in the documentation map instead of silently choosing convenient
  text.
- Fail closed relative to the exact claim being reported. Unsupported
  semantics, omitted coverage, hidden assumptions, and undischarged obligations
  must not produce an unconditional verification claim.
- Determine current behavior from the checked-in code and the
  [current-state reference](docs/reference/current-state.md). Open or stacked
  pull requests may provide context, but are not authoritative for the current
  checkout.
- Prefer existing, maintained Lean, Aeneas, Charon, and Rust mechanisms when
  they fit. Flag abstractions or extensions which may belong upstream; decide
  ownership case by case, including the maintenance burden on collaborators.
- Prefer robust programmatic interfaces over textual patching and keep the
  proof and diagnostic experience usable by ordinary Rust engineers.

## Documentation maintenance

- Update the design canon in the same change that alters a settled contract,
  trust boundary, or project-wide constraint.
- Give requirements stable identifiers and link implementation decisions back
  to them.
- Record meaningful evidence and rejected alternatives, but remove temporary
  misunderstandings once terminology has been clarified.
- Keep current-state references synchronized with checked-in behavior. Issues
  and pull requests are guides to thinking, not specifications.
- Link to canonical explanations instead of copying them into agent-only prose.
