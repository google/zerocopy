<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Meta-Principles for Anneal

This document records the underlying goals that govern
[`PRINCIPLES.md`](PRINCIPLES.md) and [`THREAT_MODEL.md`](THREAT_MODEL.md). When
evaluating or revising those documents—or the architecture in
[`docs/`](docs/design.md) that implements them—preserve the commitments below.

## 1. The end-to-end human-review sufficiency guarantee

A maintainer using Anneal wants to accept Rust code and Lean proofs—including
contributions written by untrusted humans or reward-hacking AI coding
agents—and have a sound mathematical guarantee that the resulting code behaves
as the maintainer expects.

No automated tool can defend against a compromised host operating system or
know what specifications and assumptions exist only in a human's head. Anneal
therefore factors end-to-end assurance into an explicit division of labor:

- **If:**
  1. Verification runs in an **uncompromised execution environment** (such as
     an isolated CI runner),
  2. A human (or review agent) audits **only** two clearly bounded surfaces and
     agrees with their contents:
     - **The stated specifications** (trusted to define *what the user intended
       to prove* beyond baseline soundness/UB-freedom, which is defined by
       Anneal and always on), and
     - **The TCB audit log** (trusted to be *true without proof*, covering
       Anneal's own Trusted Computing Base and any unproved assumptions or
       waivers), and
  3. **Anneal emits no errors**,
- **Then:** The verified code is sound (UB-free) and behaves as the maintainer
  expects.

**Bounded human review (corollary):** A human reviewer must know which code can
define or affect the meaning of specifications and which code can define or
affect the TCB audit log, and must be able to **safely ignore everything
outside those two categories**—including all proofs and all verified Rust
implementation bodies that do not define specifications or TCB assumptions—no
matter how complex or adversarial they are.

## 2. No security theater: total defenses vs. explicit assumptions

Every threat considered in Anneal's design must be classified by whether Anneal
can defend against it **totally** without harming legitimate use cases:

- **Explicit assumptions for threats that cannot be prevented in principle:**
  When a threat cannot in principle be prevented totally by Anneal—such as a
  compromised execution environment, build-time code tampering with an
  un-sandboxed host, or an agent proposing a weaker specification or an
  additional assumption inside the human-reviewed surfaces—Anneal must not
  implement partial, bypassable band-aids that create a false sense of
  confidence. Instead, the threat model must state the boundary explicitly as
  an execution-environment or human-review requirement.
- **Total enforcement for in-scope threats:** When a threat *is* in scope for
  Anneal—specifically, untrusted proofs making a false theorem pass, or
  untrusted code outside the human-reviewed surfaces silently altering the
  meaning of a specification or introducing an unlogged assumption—Anneal's
  defense must be **mathematically or structurally total** (un-bypassable
  within the threat model) and **must not reject legitimate Rust crates, Cargo
  workspaces, or Lean 4 specifications and proofs**.

## 3. Roles and hierarchy of governing documents

Anneal separates its governing commitments across three layers so each document
has a single responsibility and audience:

1. **[`META_PRINCIPLES.md`](META_PRINCIPLES.md) (This document — *Why*):**
   Defines the invariant goals above [`PRINCIPLES.md`](PRINCIPLES.md) and
   [`THREAT_MODEL.md`](THREAT_MODEL.md): the end-to-end sufficiency of bounded
   human review in an uncompromised environment, and the prohibition on partial
   security theater.
2. **[`PRINCIPLES.md`](PRINCIPLES.md) and [`THREAT_MODEL.md`](THREAT_MODEL.md)
   (User-facing — *What*):**
   - [`PRINCIPLES.md`](PRINCIPLES.md) states Anneal's mission, core hypotheses,
     conditional correctness promise, and decision-making priorities.
   - [`THREAT_MODEL.md`](THREAT_MODEL.md) states what Anneal does and does not
     aim to defend against (and why) so that [`PRINCIPLES.md`](PRINCIPLES.md)
     and this document's sufficiency guarantee hold, without prescribing
     internal implementation mechanisms or file representations.
3. **[`docs/*`](docs/design.md) (Developer-facing — *How*):**
   [`docs/design.md`](docs/design.md),
   [`docs/architecture.md`](docs/architecture.md), and
   [`docs/trust-model.md`](docs/trust-model.md) treat
   [`META_PRINCIPLES.md`](META_PRINCIPLES.md), [`PRINCIPLES.md`](PRINCIPLES.md),
   and [`THREAT_MODEL.md`](THREAT_MODEL.md) as controlling and specify how
   Anneal's architecture implements them.
