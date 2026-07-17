<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Open design questions

This directory records consequential Anneal V2 design questions that have not
yet been decided. It exists to preserve the reasoning behind candidate designs
without turning the current implementation, Anneal V1, an issue, or a passing
conversation into policy by accident.

An open question is not a blank slate. Each document begins with **settled
constraints** that every acceptable answer must satisfy. Agents and humans may
explore the remaining design space, but must not silently relax those
constraints. Conversely, candidates and current leanings are evidence and
working hypotheses, not commitments.

The normative [project principles](../principles.md),
[settled requirements](../settled-requirements.md), and
[accepted decisions](../decisions/README.md) take precedence over this ledger.
Anneal V1 is a source of experience, not a default architecture for V2. When a
choice is accepted, record it in a decision record and update or close the
corresponding question here rather than merely changing an implementation.

## Index

| Area | Central question |
| --- | --- |
| [Property kinds and outcomes](property-kinds-and-outcomes.md) | How should Anneal represent distinct guarantees, execution outcomes, dependencies, and user selection without baking in a premature taxonomy? |
| [Rust safety integration](rust-safety-integration.md) | Which obligations should reuse Rust's `unsafe` machinery, and which require a richer Anneal-owned tracking system? |
| [Contracts and invariants](contracts-and-invariants.md) | How should function contracts, type invariants, and trait invariants be stated, enforced, and made available to callers? |
| [Source/model adequacy](source-model-adequacy.md) | How can proofs about a model that assumes soundness establish the soundness of the source program itself? |
| [Memory, resources, and effects](memory-resources-and-effects.md) | Where can unsafe implementations close to simple functional models, and where must resource or effect semantics remain visible? |
| [Trust and incremental adoption](trust-and-incremental-adoption.md) | How should axioms, incomplete proofs, prose justifications, and the audit ledger affect the meaning of verification? |
| [Aeneas and Charon integration](aeneas-charon-integration.md) | What information and machinery should Anneal consume, extend upstream, or own itself? |
| [Proof authoring and user experience](proof-authoring-and-user-experience.md) | What proof surface can eventually serve ordinary Rust engineers, formal-methods specialists, and agents without sacrificing rigor? |

These areas intentionally overlap. A proposed answer should follow the related
links and account for its consequences elsewhere. In particular, choices about
property kinds affect Rust integration, contracts, trust reporting, and the
command-line interface; choices about source adequacy affect the Aeneas/Charon
boundary and the memory model.

## How to update this ledger

When adding evidence or a candidate design:

1. State which settled constraints it preserves.
2. Distinguish observed facts from inferences and preferences.
3. Explain the user-visible and trusted-computing-base consequences.
4. Record dependencies on Rust, Lean, Aeneas, Charon, compilers, or hardware.
5. Prefer a small experiment or counterexample over confidence based only on
   architectural taste.

When deciding a question:

1. Derive the decision from the project's principles and concrete evidence.
2. Add a decision record with alternatives and consequences.
3. Update every affected document, including settled requirements and current
   architecture where appropriate.
4. Leave enough historical context here to explain what was learned, while
   clearly marking the question or sub-question as resolved.

Temporary disagreements about terminology should not be preserved as design
questions after the underlying meaning is understood. This ledger tracks real
choices that could change Anneal's guarantees, architecture, or user
experience—not conversational cleanup.
