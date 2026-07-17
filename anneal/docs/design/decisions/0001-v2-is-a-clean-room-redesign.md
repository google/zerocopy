<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# 0001: V2 is a clean-room redesign

- **Status:** Accepted
- **Date:** 2026-07-17

## Context

Anneal V1 was an early experiment and demonstration. It established that parts
of the idea were useful, but it also embedded provisional choices about syntax,
proof structure, trust, and integration with Aeneas. Treating those choices as
an inherited compatibility surface would turn experiments into constraints
before V2's requirements are understood.

V1 remains valuable evidence. Some of its code and designs may still be the
best way to implement a V2 requirement.

## Decision

Anneal V2 is a clean-room, ground-up rewrite and redesign. The presence of a
concept, interface, or implementation in V1 creates no presumption that V2 will
retain it.

V2 may borrow or copy from V1 when a fresh evaluation shows that doing so serves
V2's principles and requirements. V2 documentation may refer to V1 to record a
lesson, or after a V1 choice has independently been accepted for V2. In all
other cases, V1 is historical context rather than design authority.

Here, “clean-room” describes design inheritance; it is not a prohibition on
reusing suitable code.

## Rationale

Anneal's purpose requires substantial changes to the prototype. Starting from
the desired assurance and user experience keeps accidental V1 constraints from
outweighing soundness, semantic fidelity, composability, or maintainability.
Retaining V1 as evidence still lets V2 benefit from working code and hard-won
lessons.

## Consequences

- V2 proposals must be justified from current requirements and principles, not
  merely by matching V1.
- Compatibility with V1 syntax, generated Lean, or workflows is not a default
  requirement.
- Copying a V1 component requires checking that its assumptions still hold.
- V1 documentation lives under [`v1/`](../../../v1/) and must not be read as V2
  documentation.
- Lessons from V1 should be distilled into V2 history documents instead of
  requiring contributors to reverse-engineer the prototype.

## Alternatives considered

### Evolve V1 in place

This would reduce short-term movement but would make it easy to preserve
experimental architecture for compatibility rather than merit.

### Treat every V1 behavior as a compatibility promise

V1 was not intended to define a production interface. This alternative would
prematurely constrain both the proof model and the user experience.

### Forbid all V1 reuse

That would discard useful implementations and lessons without improving the
quality of V2's decisions.

## Deferred questions

- Which V1 components, if any, should be reused?
- Will V2 offer migration tools or compatibility syntax for V1 users?
- What specification language, proof surface, and generated-Lean interface
  should V2 expose?

Those questions belong in the relevant
[open design discussions](../open-questions/README.md), not in this record.

## Evidence

- The project author explicitly characterized V1 as an early experimental and
  demonstration prototype and V2 as a clean-room redesign.
- The [V1 design document](../../../v1/docs/design/design.md) records several
  prototype-specific choices which are being reconsidered.
- [V1 lessons](../../history/v1-lessons.md) distills the evidence that should
  inform V2 without becoming implicit precedent.

## Links

- [Design principles](../principles.md)
- [Settled requirements](../settled-requirements.md)
- [V1 lessons](../../history/v1-lessons.md)

