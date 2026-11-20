---
name: reader-oriented-explanation
description: >-
  Draft, revise, or review technical explanations for readers who do not share
  the writer's context. Use to select and connect the facts, rationale,
  evidence, and qualifications readers need, including in commit messages, bug
  reports, and code comments. Not for formatting-only edits or independent
  technical investigation; artifact-specific evidence and completeness rules
  still apply.
---

# Reader-oriented explanation

Help the intended reader recover the supported understanding this artifact is
responsible for providing. Respect the requested transformation, supply the
relationships the reader needs, and exclude material that serves only the
writer. Neither covering every fact nor minimizing words is the objective.
These responsibilities are not a required sequence or visible worksheet.

## Match the task: what must change and what must remain

Establish the subject, revision or time, audience, and requested result. A new
explanation, summary, critique, faithful rewrite, and grammar correction permit
different transformations. Apply the request and relevant domain or project
rules, including mandatory fields, identities, evidence, independent obligations,
qualifications, and output boundaries. Required content need not separately
justify its relevance. Distinguish source claims being edited or assessed from
facts established for a new account. Unavailable required information stays
unknown.

For an edit, identify both the requested changes and the assertions that must
survive. Keep the source in view rather than retelling it from a general impression.
A local correction should normally repair the affected construction. Clarifying
one duty does not remove a separate observation; preserving observations does
not excuse leaving the requested clarification undone. Follow each permission
or restriction where it applies, including when they differ within a passage.

Preserve meaning, not merely vocabulary: participants and referents, number,
tense, conditions, negation, units, and certainty can carry substantive claims.
Keep unresolved alternatives unresolved unless clarification is authorized and
supported. A faithful edit may require retaining an unverified or apparently
inconsistent source claim. Do not silently repair or erase it; flag the concern
separately only when output scope permits. Protect exact quotations, identifiers,
and file regions as required; carry those bytes through rather than rewriting
them with surrounding prose. Semantic fidelity does not require unchanged wording
when an equivalent or explicitly authorized transformation is available.

## Start from the reader's context

Ask what the reader needs to understand, verify, preserve, or decide here, and
what they can already know or inspect. Expertise is local: a domain expert may
not know this subsystem; a maintainer may understand constraints the agent has
missed. Use supported audience and project context, not a fictional biography.
Without more context, assume a technically competent reader at the artifact's
intended interface, not a participant in the writer's work session.

The writer's briefing is not the reader's knowledge. Private prompts, drafts,
experiments, and review exchanges are not automatically shared or requested
content. Address a consequential misunderstanding reasonably invited by the
reader's actual context, names, or interface, without inventing one to justify
an explanation. Reader expectations guide presentation, not technical truth.

Consider access and reconstruction cost. A log reader may not open the diff;
an API caller should not have to inspect the implementation; nearby code may
not reveal an external assumption. Supply an established premise or connection
the reader lacks, without reteaching familiar concepts. Distinguish this gap in
explanation from a gap in evidence: an unestablished premise calls for handling
uncertainty, not inventing the missing part of a persuasive account.

## Select and connect what serves this artifact

When selection is authorized, include additional material for its concrete
contribution to this reader's understanding or task. Truth, technical relevance,
discovery effort, source prominence, and usefulness in another task do not by
themselves earn space. Required completeness remains a constraint on selection.

**Facts can constrain your reasoning without belonging in the explanation.**
Use writer-only background to avoid a mistaken account; do not automatically
introduce and refute it. The same fact may belong when a real reader question,
likely inference, or required record makes the distinction useful.

Treat history by that rule. Explain a real predecessor, affected release, or
rejected alternative when it supplies consequential context. Preserve the
lasting constraint or tradeoff rather than the private sequence of attempts.
When chronology or faithful editing requires that sequence, retain it and its
committed, deployed, or uncommitted status. Neither age nor privacy determines
relevance; confidentiality separately limits disclosure.

Identify the answer and the relationship that makes it intelligible: a premise,
mechanism, contrast, or consequence. Naming a technique and benefit may not
explain why this change matters. Conversely, a clear equation, example, or
contextual reference may already do that work. Explain the property that matters,
not every implementation step. A report, commit, and current-code comment can
use the same facts differently without changing their truth.

Choose support as a whole. Parts of an argument may be necessary together; two
alternative witnesses may each be replaceable, but removing both loses the
proof. An analogy, example, or repetition may clarify an existing relationship
without adding facts. Preserve its limits. Omit unnecessary material rather than
hiding it in an appendix; keep useful secondary material accessible. Give a
qualification the prominence needed to constrain the claim. A later caveat
cannot repair an unsupported headline.

## Keep the account within its support

Check the account a reader would reasonably infer in context, not just isolated
sentences. Preserve each claim's subject and relationships. Do not move a fact or
an unknown to an associated event, a different time, or a broader scope.
Distinguish system facts, evidence availability, and writing instructions; none
substitutes for another.

For a consequential assertion, work backward to its premises, including ones
the source never labels missing. Would another mechanism consistent with the
evidence change the claimed result? If so, obtain the needed support within
scope, narrow the claim, or present a warranted hypothesis when the task needs
one. A familiar story, suggestive API name, or caller preconditions do not supply
an implementation effect. A requirement does not prove compliance or a particular
violation; necessary conditions do not guarantee success.

Use established domain semantics, ordinary reference, and supported deductions.
Context can establish a premise without a separate source sentence; missing a
necessary fact is different from missing a preferred phrasing. Do not withhold
a conclusion whose premises are established. Distinguish a particular observed
outcome from a conditional consequence and an empirical generalization from a
deduction. Preserve attribution, comparison bases, independent conditions, and
exceptions. A recorded motive may be attributed; a beneficial effect alone does
not establish that motive. Verification of one property does not verify a related
property.

Support the claims the artifact makes or endorses, including introductions,
connectives, glosses, and editorial flags. Faithfully representing a source claim
is not verifying its truth; an attributed claim needs support for that attribution.
Check agreement with formulas, examples, and evidence in direction, extent, and
conditions. A correct conclusion does not validate an incorrect explanation.
In a critique, assess the claim actually made, not a stronger one substituted
for it. Identify what follows and where support ends when the requested assessment
needs both; a narrowly requested single-defect critique does not require a
balanced survey or a rewrite.

## Make the understanding accessible

Orient the reader with the main point and arrange its support by the dependencies
they need. Use an established governing rule to connect details; keep independent
claims and alternatives independent. Do not invent a hierarchy for tidiness.
Preserve precise technical terms, explaining unfamiliar ones rather than replacing
them with lossy synonyms. A local label should repay the effort of learning it.

Avoid creating stale duplicate explanations. Within editing authority, prefer
clearer code or another direct representation to prose that only repeats it.
Explain stable relationships to distant code instead of copying mutable details.
Use references with the version and lifetime the claim needs. Links can provide
evidence or further detail, not replace necessary local explanation. Preserve
attribution and disclosure boundaries; do not expose restricted material or
present inaccessible evidence as independently available to the reader.

## Check the delivered result

Compare the result with the task and source in both directions: did every required
change happen, did everything required to remain survive, and did any wording add
or alter a claim? For saved files, inspect the saved text and protected boundaries,
not just the replacement you intended or a status message. Byte checks and semantic
checks answer different questions. Review the whole delivered explanation,
including any added flag; assurances cannot substitute for the checks.

Then read with only the intended reader's context. Can they recover the supported
answer, its important reason or contrast, and its limits? Remove writer-only
material when selection permits, but do not mistake avoiding overclaims for
supplying the understanding the artifact owes. Recheck affected judgments when
the evidence, audience, subject, or output changes.

Stop when the requested result is adequate. No edit, no comment, or no body can
be correct. Return the requested artifact or assessment, not a reader profile or
a transcript of these diagnostics. Domain-specific verification, general writing
guidance, and disclosure rules retain their responsibilities. This skill does
not authorize research, tests, code changes, publication, or prohibited authorship.
