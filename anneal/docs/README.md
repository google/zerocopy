<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal documentation

This directory is the shared design canon for humans and agents working on the
current Anneal redesign. This page is the canonical owner of the reading order,
document authority, and reconciliation process. Agent instructions may point
here, but must not maintain a competing copy of that information.

## Reading order

Agents should first follow [`AGENTS.md`](../AGENTS.md). In an unfamiliar
checkout, complete the [agent-corpus preflight](agent-corpus.md) before relying
on any local document.

Before making or reviewing a design change, read the following completely, in
order:

1. The user-facing [project introduction](../README.md), to understand the
   audience and product promise.
2. [Glossary](glossary.md), for stable vocabulary used throughout the canon.
3. [Principles](design/principles.md), for the goals and choice rules behind
   design judgment.
4. [Settled requirements](design/settled-requirements.md), for constraints
   every acceptable design must meet.
5. [Accepted decisions](design/decisions/README.md), including every decision
   relevant to the change.
6. [Verification model](design/verification-model.md), for the intended local
   proof and global composition argument.
7. [Result and trust model](design/result-and-trust.md), for the identity and
   scope of a claim, its evidence, its residual dependencies, and what must be
   reported.
8. [Worked example](design/worked-example.md), as an illustration whose
   concrete proof choices are not decisions unless the text cites one.
9. [Open questions](design/open-questions/README.md), including every page
   relevant to the task. Candidate approaches are not decisions.
10. [Current state](reference/current-state.md) and the explicitly
    non-normative [current priorities](reference/current-priorities.md), for
    checked-in behavior and the present engineering frontier.

For translation, semantics, or proof-infrastructure work, also read
[Aeneas and Charon](reference/aeneas-and-charon.md). Read
[development and CI](reference/development-and-ci.md) before changing commands
or automation. Read [V1 lessons](history/v1-lessons.md) before borrowing from
the prototype, and inspect V1 itself only when the task requires primary
historical evidence.

The [agent-corpus guide](agent-corpus.md) explains how to discover every
documentation file for a full audit or context-free comprehension test.

## Document classes

### Navigation and vocabulary

This map, the [agent-corpus guide](agent-corpus.md), and the
[glossary](glossary.md) help readers find and interpret the canon. They do not
create design commitments independently of the normative documents and
accepted decisions they describe.

### Normative design

The files directly under [`design/`](design/) give the current consolidated
design. Principles guide choices; settled requirements constrain every
acceptable design. The worked example is a teaching companion: its concrete
choices are illustrative, and only the requirements and decisions it cites are
normative.

### Accepted decisions

Records under [`design/decisions/`](design/decisions/README.md) capture an
accepted choice, its rationale, and its consequences. A decision changes only
through an explicit amendment or superseding record. Consolidated design files
must be updated when such a change affects their account.

### Open questions

Files under [`design/open-questions/`](design/open-questions/README.md) are
design workspaces. Their settled constraints come from the normative documents
and accepted decisions they cite. Candidate approaches, provisional analyses,
and implementation experiments do not settle the question.

### Reference

Files under [`reference/`](reference/current-state.md) describe checked-in
code, commands, external tools, and current limitations. They are factual, not
aspirational. The dated
[current-priorities page](reference/current-priorities.md) is non-normative
guidance for the present engineering frontier. References must label intended
future roles and defer to the normative design where appropriate.

### History and research

Files under [`history/`](history/v1-lessons.md) preserve evidence, lessons, and
source indexes. V1, issues, pull requests, and research papers may motivate a
decision but do not override the current canon. Volatile source indexes must be
dated.

## Resolving disagreements

If normative files disagree with one another, or a consolidated design file
disagrees with an accepted decision, do not silently select one. Check whether
one record explicitly supersedes the other, then surface and repair the
inconsistency. Until it is reconciled, avoid making an irreversible design
choice which depends on the disputed point.

Do not promote language from an open question, issue, pull request, experiment,
or V1 into a settled claim merely because it is convenient or has been
implemented. Record the decision first or continue to label the implementation
as an experiment.

## Changing the canon

A project-wide question becomes settled only with explicit agreement from the
project authors; implementation alone is not ratification. After agreement:

1. add or update an accepted decision record;
2. update the relevant normative design files;
3. update the status and links of affected open questions;
4. update current-state references if checked-in behavior changed; and
5. preserve significant evidence and genuinely considered alternatives without
   retaining obsolete conversational misunderstandings.
