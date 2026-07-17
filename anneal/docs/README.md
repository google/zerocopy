<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal V2 documentation

This directory is the shared design canon for humans and agents working on
Anneal V2. Agent-specific files provide reading order and working instructions;
they do not define a second version of the project's philosophy.

## Reading order

Agents entering from an unfamiliar checkout should first run the
[agent-corpus preflight](agent-corpus.md). Then read:

1. [Glossary](glossary.md): stable vocabulary used throughout the canon.
2. [Principles](design/principles.md): the value function behind design
   judgment.
3. [Settled requirements](design/settled-requirements.md): concrete constraints
   every acceptable design must meet.
4. [Accepted decisions](design/decisions/README.md): choices already made and
   their rationale.
5. [Verification model](design/verification-model.md): the intended local and
   global claims.
6. [Verification subject and result identity](design/verification-artifact.md):
   the concrete program to which a result applies and the evidence attached to
   that claim.
7. [Trust model](design/trust-model.md): what may be assumed and how trust must
   be exposed.
8. [Worked example](design/worked-example.md): one schematic application of
   the model, with illustrative choices clearly separated from requirements.
9. [Open questions](design/open-questions/README.md): unresolved designs and
   their settled constraints.
10. [Current architecture](reference/current-architecture.md),
    [limitations](reference/current-limitations.md), and non-normative
    [priorities](reference/current-priorities.md): what the checked-in
    implementation does today and the present engineering frontier.

Read [V1 lessons](history/v1-lessons.md) before borrowing from the prototype.

## Document classes

### Navigation and vocabulary

This map, the [agent corpus](agent-corpus.md), and the
[glossary](glossary.md) help readers locate and interpret the canon. They do
not create design commitments independently of the normative documents and
accepted decisions to which they point.

### Normative design

The normative files directly under `design/` state the current consolidated
intent. They distinguish principles from requirements so that a local tradeoff
can be reasoned from the project's values without mistaking a preference for a
hard constraint. The worked example is a teaching companion in that directory:
its concrete choices are illustrative, and only the requirements it cites are
normative.

### Decisions

Accepted records under [`design/decisions/`](design/decisions/README.md) capture
a choice, its rationale, and its consequences. A decision may be changed, but
only explicitly through a superseding record. Normative design files should be
updated when a decision changes their consolidated account.

### Open questions

Files under [`design/open-questions/`](design/open-questions/README.md) are
design workspaces. Their settled-constraints sections are normative by
reference to the core design documents; candidate approaches and provisional
analyses are not. An implementation experiment does not silently decide the
question.

### Reference

Files under [`reference/`](reference/current-architecture.md) describe current
code, commands, external tools and their relevant concepts, and limitations.
Current-state pages are factual rather than aspirational. The dated
[current-priorities page](reference/current-priorities.md) is explicitly
non-normative guidance for the present engineering frontier. Any discussion of
intended roles must be labeled as such and defer to normative design documents.

### History and research

Files under [`history/`](history/v1-lessons.md) preserve evidence, lessons, and
source indexes. V1, issues, PRs, and research papers can motivate a decision but
do not override the V2 canon. Volatile source indexes must be dated.

## Resolving conflicts

If two normative files or an accepted decision and a consolidated document
disagree, do not silently select one. Identify whether one record explicitly
supersedes the other, then surface and repair the inconsistency. Until it is
reconciled, avoid making an irreversible design choice based on the disputed
point.

Likewise, do not promote language from an open question, issue, PR, or V1 into a
settled claim merely because an implementation uses it. Record the decision
first or describe the implementation as an experiment.

## Changing the canon

A project-wide question becomes settled only with explicit agreement from the
project authors. Implementation alone is not ratification. After that
agreement, the change should:

1. add or update an accepted decision record;
2. update the relevant normative design files;
3. update open-question status and links;
4. update current-state references if implementation changed; and
5. preserve significant evidence and rejected alternatives without retaining
   obsolete conversational misunderstandings.
