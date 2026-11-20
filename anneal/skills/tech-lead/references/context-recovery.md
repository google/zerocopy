<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Technical continuity and context recovery

Use this guidance when establishing or materially reorganizing project memory,
or when compaction, handoff, contradiction, or apparent forgetting threatens
technical continuity. Share existing project records with Lieutenant or other
active coordination guidance. This reference specifies what technical meaning
must survive; it does not supply a new authority or coordination protocol.

## Preserve the meaning a later decision will need

Store reviewable conclusions and their rationale, not an attempted transcript of
private reasoning. For each consequential decision preserve, where material:

- the problem and the requirement it serves;
- the choice and its status: selected, provisional, proposed, deferred, rejected,
  or superseded;
- its applicability domain, assumptions, exceptions, and continuing obligations;
- the argument and source evidence that justify it, including limits and gaps;
- attractive alternatives and the reason they do not currently apply;
- dependencies on other decisions, interfaces, artifacts, or external contracts;
- observations that would reopen it and the next unresolved question.

Preserve the distinctions that can change an action. Examples include stable
identity versus continued liveness, a caller obligation versus an internal
invariant, an experiment's supported domain versus production readiness, and a
conditional rejection versus a universal prohibition. Do not require these exact
concepts when the project's domain uses different distinctions.

Keep requirements, choices, assumptions, findings, and evidence distinguishable.
A lead's choice is not automatically a user requirement; an observed upstream
behavior is not automatically a promised contract. Retain significant dissent
and competing explanations until resolved rather than rewriting them as consensus.

## Provide a current entrypoint and reachable depth

Use a discoverable current checkpoint with links to the detailed rationale and
primary artifacts. Follow the repository's established names and locations.
One file can suffice when the project is small; a larger project may need a
decision index and component-level records.

The entrypoint should let a recovering agent find:

- the current mission, hard constraints, completion conditions, and authority
  provenance where relevant;
- the accepted architecture and relationships between its major parts;
- critical assumptions, known traps, unresolved questions, and relevant rejected
  approaches;
- current work, ownership or worker-state sources, dependencies, and next decisions;
- which results are proposed, integrated, validated, and externally verified;
- exact or otherwise adequate identities for relevant source and evidence;
- where to read the rationale needed for the active frontier.

Organize depth by the decisions and components it explains. A link labelled
"old discussion" is inadequate if the agent cannot locate the governing condition.
Necessary context must actually be preserved at accessible references; an index,
hash, or unavailable URL does not supply missing content. Use only storage
authorized for the information, and keep private task history out of public skills
or documentation unless separately authorized.

Keep the checkpoint manageable by moving still-needed detail to discoverable
records, removing irrelevant mechanics, and consolidating duplication. There is
no universal line limit that permits deleting a load-bearing condition. Conversely,
requiring replay of a large chronological archive makes recovery fragile even if
the information exists somewhere.

Update the current account after material design or scope changes and meaningful
integration. Mark superseded decisions with their successor and reason while
preserving rationale that remains useful. Do not leave an obsolete issue body
looking current merely because a later comment corrects it. A new timestamp alone
does not resolve a semantic conflict or establish authority.

Keep volatile observations identifiable as such: process and worker status,
branches, CI state, tool availability, remote state, and unverified effects need
reobservation. A durable technical argument can remain valid while its execution
binding becomes stale. Do not discard one merely because the other changed.

## Checkpoint before context loss can make work depend on guessing

Preserve decisions at the time of commitment, material discoveries or premise
changes, useful experimental results, blocked work with non-obvious rationale,
and partial work whose reconstruction would be costly. Also checkpoint at expected
compaction, interruption, and handoff when those events are visible. Do not write
after every tool call or create records for reconstructable trivial mechanics.

Before a material save, read enough current state to avoid overwriting a newer or
conflicting account. Verify important updates by trustworthy acknowledgement or
readback. If the write outcome is uncertain, inspect persistent state before
retrying and preserve the transient work. If persistence is unavailable, retain
the recoverable work, state that continuity is unconfirmed, and avoid accumulating
dependent work whose safe continuation requires that unpreserved context.

## Recover progressively, then check action readiness

Signs of degradation include an explicit compaction or handoff, inability to
explain a current constraint, conflicting summaries, repeated proposals already
considered, unexplained plan changes, and missing rationale for the next action.
Failure to remember a decision is not evidence that no decision exists.

Recover at the depth the next consequential decision needs:

1. **Orient.** Read current instructions and the project entrypoint. Identify the
   objective, current frontier, and the facts that the next action will consume.
2. **Reconstruct.** Follow the relevant architecture and decision records to
   recover rationale, conditionality, dependencies, rejected alternatives, and
   open disagreements. Inspect the primary artifacts needed to understand them.
   Expand retrieval if contradictions or unexplained assumptions remain.
3. **Reconcile.** Compare the recovered account with current authoritative task
   and native state. Identify supersession and stale observations; requery relevant
   work, source, review, ownership, and publication state. Reconcile uncertain
   effects before any retry that could duplicate or conflict with prior work.
4. **Check.** Form a concise account of the intended behavior, why the chosen
   design serves it, the premises and limits, remaining uncertainty, and what
   evidence would change the next decision. Check it against the actual records
   and artifacts rather than treating a fluent restatement as validation.
5. **Resume.** Continue the smallest useful action justified by that understanding
   and current authority. Repair the checkpoint if recovery revealed staleness,
   omitted rationale, or a misleading retrieval path.

This sequence describes dependencies, not a required report or tool transcript.
An agent need not reread unrelated history to correct a local defect whose
requirements and evidence are already established. Lost conversational detail
does not automatically invalidate all prior evidence or demand a full redesign.

When records disagree, determine their authority, subject, applicability, and
supersession relationship. Preserve useful conflicting evidence while resolving
the governing decision. Do not silently choose the more convenient account or
convert an unverified proposal into the selected design.

If material meaning cannot be recovered, name the missing premise and which work
depends on it. Seek the specific source or, if necessary, a focused user decision.
Continue independent justified work; do not guess, pretend recovery succeeded, or
ask the user to repeat information still available in project artifacts.

Recovery need not restore every conversation detail. Its required result is
sufficient, checked understanding for the action being resumed. Significant
degradation is expected; total loss of unavailable records or tacit knowledge
may make some recovery impossible. Keep that limit explicit.

## Check that project memory can support recovery

After major changes, a difficult recovery, or evidence that records are losing
meaning, test whether a reader without the prior discussion can reconstruct the
relevant decision using the entrypoint and its references. Use a fresh reader
when useful and available, or a deliberate artifact-based walkthrough.

The reader should be able to distinguish what must remain true, what was chosen
and why, which conditions limit it, which tempting approach was rejected and
under what circumstances, what remains unproved, and what action is justified
next. Include a discriminating question where a lost qualifier would change the
answer. Mere mention of a decision, file existence, or agreement with the author
does not establish recovery fidelity.

Correct the record or retrieval path when that check fails. A walkthrough or
simulated degraded handoff supports only its tested conditions; it does not prove
perfect recall or reliability under every real compaction. Keep checks
proportional to consequences rather than establishing a standing evaluation
campaign without a task need.
