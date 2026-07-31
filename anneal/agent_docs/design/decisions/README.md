<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Design decisions

This directory records Anneal V2 design decisions whose alternatives matter to
future work. A decision record says what was decided, why that choice follows
from Anneal's principles, and which questions it deliberately leaves open.

Decision records complement, rather than replace, the other design documents:

- [Principles](../principles.md) supplies reusable rules for evaluating design
  alternatives.
- [Settled requirements](../settled-requirements.md) collects the constraints
  that an acceptable design must satisfy.
- [Open questions](../open-questions/README.md) tracks design spaces in which no
  choice has yet been made.

An accepted record is normative until it is superseded. Historical evidence,
the V1 implementation, issues, and pull requests do not override it. If new
evidence changes a decision, add a new record that names the record it
supersedes instead of silently rewriting the old rationale. Small corrections
which do not change the decision may be made in place.

## Statuses

- **Proposed:** available for discussion, but not binding.
- **Accepted:** a current project commitment.
- **Rejected:** considered and deliberately not adopted.
- **Superseded:** retained as history, with a link to its replacement.

## Authoring a record

Copy [the template](0000-template.md), allocate the next four-digit number, and
keep the decision as narrow as the available evidence permits. In particular:

- distinguish required outcomes from possible implementations;
- derive the rationale from project principles rather than precedent alone;
- list costs and constraints as well as benefits;
- move unresolved choices to **Deferred questions**; and
- link the evidence that made the decision possible.

Do not turn a promising direction, an implementation trend, or a V1 design into
an accepted decision without explicit project agreement.

## Accepted decisions

| Record | Decision |
| --- | --- |
| [0001](0001-v2-is-a-clean-room-redesign.md) | V2 is a clean-room, ground-up redesign. |
| [0002](0002-verification-is-artifact-scoped.md) | A verification claim initially covers one fixed compilation artifact. |
| [0003](0003-expanded-generated-rust-is-input.md) | Expanded, generated Rust is verification input, not trusted source. |
| [0004](0004-invariants-support-all-property-kinds.md) | Type and trait invariants support arbitrary property kinds. |
| [0005](0005-incremental-adoption-supports-prose-justifications.md) | Incremental adoption supports explicit, audited prose justifications. |
| [0006](0006-the-tcb-is-explicit-and-shrinkable.md) | The trusted computing base is explicit, auditable, and shrinkable. |
