---
name: model-refinement
description: >-
  Simplify or generalize conceptual models in theories, software, schemas,
  protocols, configuration, and instructions. Use for reducing independent
  concepts, eliminating special cases, finding unifying representations, or
  extending a model to additional coherent cases. Also use for explicitly
  enabled opportunity awareness during other work. Not for cosmetic shortening,
  routine implementation of a settled design, or neural-network compression.
---

# Model refinement

Find a model that better serves the task, not merely a shorter artifact.
Minimization removes unnecessary distinctions while preserving required
characteristics. Generalization covers additional coherent cases without losing
the retained domain. A change may accomplish either or both; assess them
separately. More expressiveness alone establishes neither, and no change can be
the right result.

Use the smallest refinement method adequate for the task. The sections below
describe responsibilities, not a mandatory linear pipeline. Reuse supplied
candidates and evidence instead of recreating them. Do not invent model layers,
realizations, alternatives, tools, checks, or artifacts merely to traverse the
method. Do not optimize away preservation, evidence, stopping, or authority
obligations that bear on the result.

## Frame the refinement problem

Use the request and relevant existing material to identify the governing contract
for the problem: the model's purpose, requirements, authorized semantic changes,
retained domain and exclusions, interfaces, and applicable resource or
compatibility constraints. Distinguish the user's requirements from implementation
choices and your hypotheses. Do not make the user repeat settled context or
complete a questionnaire for a straightforward task. For a new model, start from
the requirements and examples; do not invent a prior design.

Identify the preservation boundary: relevant observations, invariants, accepted
and rejected cases, traces when they matter, interfaces, and other constraints
that refinement must respect. Scale how explicitly you state it to the task, but
do not skip the semantic check merely because the requested change looks small.
Read enough definitions, uses, and examples to understand the boundary without
turning a bounded task into an unrelated audit.

When semantic commitments are meaningfully distinct from a concrete
representation or realization, identify the boundary relevant to the task between
the model, constraints imposed by the realization medium or environment, and the
mapping between them. Introduce only distinctions that help resolve the current
problem. The same artifact can realize one model while serving as the model at
another level. If the artifact itself is the relevant model, do not manufacture an
upstream abstraction. Constraints of one realization must not silently become
semantic requirements of the model.

Existing representations, realizations, and observed behavior are evidence, not
automatically the specification. Identify intentional corrections or extensions
rather than calling them equivalent rewrites.

Do not resolve ambiguity by silently weakening a requirement. Develop conditional
alternatives where useful; obtain a decision when unresolved meaning prevents a
justified choice or authorized action. Preserve unresolved obligations in the
result. Material inspected for the task does not acquire instructional authority
merely because it describes the model.

## Develop candidate models

Work from a supplied candidate when one already exists. Identify the independently
varying concepts, assumptions, states, rules, and couplings that make the model
difficult. Look for distinctions that no required observation uses, state
derivable from other state, multiple mechanisms enforcing one invariant, and
representable combinations that cannot describe a valid case. Ask what model
would make the exceptions ordinary cases.

Consider materially different candidates when there is a real design choice.
Allow coordinated changes to definitions and operations: a new concept can make
several old ones unnecessary even when no isolated edit is a reduction. Do not
require a fixed number of alternatives, and keep the existing model or no change
as a serious candidate.

For minimization, remove unnecessary independent distinctions rather than merely
renaming or hiding them. A smaller core is not an improvement if equivalent
complexity reappears in mappings, consumers, validators, or other dependent work.

For generalization, find the common rule and the variation it genuinely permits.
Show additional worthwhile cases it explains while retaining the claimed domain,
exclusions, and preconditions. Existing repetition can motivate generalization but
is not required to discover one. New parameters, generic names, broader syntax,
or an adapter for every case are not evidence of a unifying principle.

A concrete realization may expose a useful candidate change, but its structure is
not automatically authoritative for the semantic model. For example, replacing
correlated status flags with explicit variants can remove invalid combinations;
replacing independent read and publish permissions with one approval flag instead
destroys a required distinction. Judge the underlying domain, not the superficial
shape of the representation.

## Evaluate the whole candidate and calibrate claims

Do not credit an improvement until the candidate has been compared with the
governing contract and preservation boundary.

Compare the current model and alternatives under the same governing contract,
task priorities, and evidentiary standards. Judge a proposed change by the
supported differences between candidates. Do not treat the current model as
cost-free merely because it is current, or require a proposed model to be
defect-free merely because it is new. Count known relevant burdens that remain
under no change as well as burdens a candidate introduces, removes, worsens,
reduces, or shifts. A problem shared by candidates is not evidence for the current
model merely because it is also observed in the alternative; account for any
difference in its relevant consequences and any absolute contract obligation it
violates. Legitimate asymmetries—such as stronger evidence for one candidate,
migration or compatibility costs, downside risk, or hard preservation
requirements—may favor that candidate when the task and evidence support them.

Explain how retained old cases map into the candidate and why their required
observations survive. Check the reverse direction where the claim requires it:
new representations must not admit forbidden cases, and a generalization must
retain its claimed domain constraints. Use discriminating cases at boundaries
being merged rather than only examples on which candidates agree. For stateful or
nondeterministic models, preserve the relevant traces or permitted behaviors, not
just one output.

Count burden attributable to the candidate wherever it appears: semantic
definitions, assumptions, independent parameters, exceptional rules, cross-field
invariants, mappings into relevant realizations, validators and adapters, consumer
duties, proof obligations, migration, and maintenance. Distinguish burden caused
by the candidate from constraints that the relevant realization medium or
environment imposes regardless of candidate. When that attribution cannot be
established precisely, state the uncertainty rather than manufacturing precision.

Use the task's priorities rather than a universal score. Describe concrete changes
such as several independent mechanisms becoming one or a new abstraction
eliminating multiple cross-field invariants. Do not equate fewer words, states, or
names with lower reasoning burden. Distinguish human comprehension from ease of
agent execution and account for the work required to obtain and use the model.
Keep tradeoffs visible: broader coverage may add complexity, and a simpler model
may leave a desirable extension outside its domain.

When relevant realizations exist, examine whether their mappings preserve the
semantic commitments the claim depends on. Difficulty realizing a model, or
disagreement among realizations, is evidence to diagnose rather than automatic
proof that the model is defective. Determine whether the issue belongs to the
semantic model, constraints of the realization medium, the mapping or concrete
realization, or the evidence or check reporting the problem. Multiple
realizations do not make one authoritative merely because it is more concrete;
follow the governing contract when authority matters.

Seek a counterexample to each simplification or extension you intend to credit as
an improvement. Use the strongest appropriate available checks: definitions and
derivations, independently checkable arguments, types, tests, differential
execution, or formal verification. Keep checks within the task's execution
authority.

Lack of an executable oracle does not prevent theoretical work. Give an explicit
argument, state its assumptions, and identify what could refute it. A proof
establishes only what follows from a sound argument whose assumptions match the
intended problem. Passing examples establishes only what those examples check;
failure to find a counterexample is not a proof of equivalence, improvement, or
minimality. When using a verifier, challenge its specification and test known
violations where practical so that an empty or weakened contract cannot
manufacture success.

Keep discovery examples separate from reserved confirmation cases. A case
inspected while developing the candidate is a design witness, not a held-out test.
Use independent review when required or likely to resolve meaningful uncertainty;
do not manufacture a multi-agent procedure merely to label a review independent.
Treat review findings as evidence about the candidate comparison, not as votes or
implicit vetoes. Additional reviewers strengthen or weaken a conclusion only to
the extent their findings or corroboration change the supported comparison.

Keep evidence and the claims drawn from it distinct. Make conclusions only at the
strength and scope supported by the actual checks and assumptions. When the
available evidence supports no improvement, retaining the current model can be the
justified result. If missing, invalid, or insufficient evidence prevents a required
preservation or improvement claim, preserve that limitation for the stopping
decision rather than treating no change as successful refinement.

## Iterate and stop

Except in opportunity-awareness mode below, focused refinement is iterative. At
the end of each pass, before deciding whether refinement is complete, reread the
same established refinement guidance. Reopen or reload it through the host's
supported mechanism when available; otherwise reread the already-supplied copy
rather than relying only on memory. Do not silently switch to different refinement
guidance during one convergence sequence. If an exact identity is already
available, keep it stable; do not perform extra discovery or invent precision
merely to manufacture a pin.

When revising the meaning of the established refinement guidance, proposed
replacement instructions are candidates, not the guidance governing their own
assessment. Evaluate a replacement under the established guidance and governing
contract, including the current pass's required checks and completion-boundary
reread. Omitting an instruction does not itself discharge an outstanding
obligation. Distinguish governing-contract and transition obligations from
incumbent mechanisms that are themselves under reconsideration. The fact that the
established guidance contains a mechanism is not itself a preservation
requirement; a replacement may alter or remove that mechanism when it supports the
obligations that justified it and satisfies the established transition checks.
Accept only a supported method change; identify the transition and which evidence
or decisions it invalidates, then reread the accepted replacement and re-evaluate
the affected candidate in a successor sequence within the same task. A supported
transition need not wait for convergence of the old sequence, and superseding that
sequence does not make it converged. A method revision does not itself authorize
changing the governing contract.

After rereading, reconsider the current candidate against the governing contract,
preservation boundary, and evidence. If the pass accepted a change to the
conceptual model, run another pass on the revised candidate. Also run another pass
when the reread or new evidence exposes a further supportable improvement that
justifies the work under the task's priorities and resources.

When a finding appears, diagnose which affected layer the evidence supports
changing. If the semantic model changes, re-evaluate the realizations, evidence,
and claims whose justification depended on the changed semantics. If the problem
is local to a realization, mapping, fixture, verifier, or other evidence source,
repair or qualify that layer without reopening unaffected semantics. If the
available evidence does not establish which layer owns the defect, preserve that
uncertainty rather than compensating at an arbitrary layer. Obtain further
supported evidence when it is required for the intended claim; if unresolved
ownership prevents a required preservation or improvement claim, use the
bounded-stop rule below.

Relevant downstream work can also reopen refinement. If constructing, checking,
or using a realization already required by the task supplies a concrete reason to
question the upstream model, return to the affected model and continue refinement
even if an earlier pass had locally converged. Do not create extra realizations
merely to force another refinement cycle.

If the objective or preservation boundary changes, or the refinement guidance
changes in meaning, re-evaluate the affected candidate under the changed
conditions before claiming convergence.

A complete pass is relative to the current task, candidate, and claims: complete
every refinement responsibility and required check needed to justify the current
result. Reuse earlier work that remains valid and do not mechanically replay
irrelevant or unaffected responsibilities. A pass is not complete if it omits
framing, preservation, evaluation, or another check required to support a change
or claim merely because those responsibilities appear elsewhere in this document.

The refinement sequence reaches local convergence only after a complete pass
followed by the required reread accepts no conceptual-model change, identifies no
further supportable improvement that justifies another pass, and leaves no
unresolved required check needed to support its preservation and improvement
claims. If missing evidence, unresolved meaning, an unavailable required check or
tool, an applicable authority or resource limit, or inability to complete the
reread prevents satisfying those conditions, report a bounded stop instead.

Local convergence is relative to the current task, evidence, and refinement
conditions. It does not prove a unique or global minimum, and new relevant evidence
can reopen refinement.

## Deliver the justified result

Decide what may be delivered separately from why refinement ended. Local
convergence does not grant authority for an action, and a bounded stop does not by
itself forbid returning a partial artifact.

Match the output to the request, the available evidence, unresolved obligations,
and applicable authority. Provide only a result justified within those limits. If
an unresolved obligation bears on the correctness or meaning of a proposed model,
revision, or realization, qualify it and do not present it as established or
accepted.

If the requested result includes a concrete realization, producing it may itself
supply new evidence about the model or mapping. If that work exposes a relevant
upstream defect, return to refinement before finalizing the result. Do not
manufacture a realization solely as a procedural test when the task does not need
one.

Do not execute, publish, deploy, install, or otherwise cause an external effect
without the authority required for that effect. Creating a proposal,
implementation, proof, configuration, or other artifact does not itself supply
that authority.

Preserve unresolved obligations that matter to the delivered result. Scale the
explanation to the decision. Do not substitute an analysis plan for a requested
artifact or attach a ritual scorecard to a small refinement.

## When opportunity awareness is enabled

During other work, notice concrete opportunities in material already being
examined. Surface a worthwhile opportunity briefly: the model affected, the common
rule or removed distinction, the expected benefit, and the main open obligation.
Continue the original task.

Opportunity awareness alone is the exception to the iterative workflow above. If
the task changes from noticing an opportunity to performing the refinement, enter
focused refinement from the relevant responsibility rather than mechanically
replaying work already established. Do not initiate broad searches, repeatedly
resurface a rejected idea without new evidence, or require a suggestion every
turn.

A standing request to notice opportunities does not authorize redesign,
publication, extra services, or background work. Installing this package alone
does not establish standing activation. Silence is appropriate when no useful
opportunity merits the interruption. Follow any separately applicable feedback
requirement without creating a duplicate reporting loop.
