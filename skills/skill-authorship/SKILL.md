---
name: skill-authorship
description: >-
  Create, revise, evaluate, consolidate, or retire agent skills and their
  maintainer guidance. Use when engineering a reusable behavioral capability,
  diagnosing skill failures, or assessing a skill change against its governing
  goals. Not for merely executing another skill. Do not turn a settled wording,
  formatting, or link correction into a redesign. Use model-refinement when this
  work is deciding or changing the behavioral model.
---

# Skill authorship

Engineer an effective, maintainable behavioral capability, not merely polished
instructions. Keep four things distinct: the governing behavioral contract, its
implementation, the evidence and claims about it, and its lifecycle or action
disposition. None substitutes for another.

Apply only the parts of this skill that the task actually exercises. Do not
manufacture design, implementation, evaluation, review, or deployment work merely
to traverse a process. Distinguish burden attributable to the resulting capability
from burden attributable to the authoring method; do not make either look cheaper
by moving work into the other. Minimize either only among approaches that preserve
the governing contract and satisfy the evidence and action requirements applicable
to the requested result. When attribution is mixed or uncertain, state that rather
than forcing it into one side.

## Establish the governing contract

Read the requested scope, applicable repository guidance, existing maintainer
contract and skill when present, and relevant evidence. Resolve available facts
rather than asking the user to repeat settled context. Distinguish user
requirements, engineering choices, empirical hypotheses, and observed current
behavior. Examples, retrieved material, evaluations, and existing implementation
are evidence; they do not acquire authority to rewrite the contract.

Identify the intended users and task family, desired outcomes, activation and
non-activation behavior, supported domain and exclusions, composition and
responsibility boundaries, hard constraints, and important failure behavior.
Include the authority, privacy, and side-effect boundaries that the resulting
skill must enforce when it runs.

Preserve the contract independently of candidate wording and implementation. For
a revision, identify which semantic requirements are authorized to change and
which remain fixed. Existing behavior may be a defect, and an authorized
correction need not preserve it. Conversely, rewriting or replacing an
implementation does not silently retire still-valid obligations.

Resolve ambiguity only as far as the current decision requires. State assumptions
or conditional alternatives when useful. Obtain a decision when unresolved
meaning or missing action authority prevents justified progress; do not escalate
ordinary engineering choices. A narrow settled correction normally needs a narrow
change and the checks relevant to that change.

A request to draft or analyze does not itself authorize publication, installation,
activation, spending on evaluations, changing external state, or creating standing
policy.

## Choose the representation and smallest adequate package

When the authoring work is deciding or changing the behavioral model—its concepts,
responsibilities, state, exceptions, or coverage—use `model-refinement`. Obtain its
established guidance through the host's supported mechanism or an explicitly
supplied package; do not assume a sibling path or universal import feature.
Settled implementation, wording, formatting, link, or other mechanical corrections
do not require conceptual refinement merely because they occur in a skill.

The authoring task retains the governing contract and all action authority.
`model-refinement` supplies a reasoning method, not publication approval, domain
authority, or a requirement to launch another agent. If the dependency is
unavailable, continue only the work that remains supported and identify the
unperformed refinement; do not invent its instructions or claim it was used.

Design the agent's decision structure, not just the Markdown. Account for what the
capability must distinguish, remember, retrieve, coordinate, validate, and recover
from, including support files and duties imposed on hosts, callers, users,
evaluators, and maintainers. A broader representation does not by itself justify
broader activation or authority.

Among implementations that satisfy the contract and the mandatory evidence and
action obligations, prefer the least burdensome coherent package. Count burden
attributable to the resulting capability wherever it appears: runtime concepts and
instructions, references, helpers, schemas, tools, context loading required to use
it, host, caller, and user duties it imposes, cognitive load, validation or evidence
obligations induced by it, integration, migration, and maintenance. Do not make the
capability appear simpler by moving equivalent burden into consumers, support
machinery, evaluators, or operators. Required correctness or evidence checks are
constraints to satisfy, not optional overhead to optimize away.

Separately, minimize burden attributable to the authoring method: instructions and
dependency loading used to author, generic checks and tools, reviewer and operator
duties, orchestration, retries, evaluation work imposed by the authoring process,
and maintenance of the authoring system. Reuse still-valid work and scale authoring
work to the task. Do not reduce method burden by skipping required correctness,
evidence, or authority obligations.

Write runtime guidance for execution: an intent-oriented description, load-bearing
rules and reasons, relevant inputs and outcomes, and behavior for important
uncertainty or failure. Specify an exact order or method only when it matters.
Retain examples when they disambiguate a rule; do not encode a new exception for
every incident or add generic advice solely to fill a template.

Keep maintainer intent outside routine runtime loading. Preserve the governing
goals, important non-goals and constraints, non-obvious rationale, dependencies,
evidence limits, and conditions for changing or retiring the design. A new
maintainer should be able to make a bounded change without reconstructing the
original authoring conversation. Use stable goal or requirement identifiers when
they materially improve traceability; avoid duplicate ledgers.

Keep genuinely shared reasoning in its general owner rather than copying it into
each domain skill. Split or combine skills around useful responsibility and
loading boundaries, not merely to minimize directory count.

Add references, scripts, schemas, automation, or other machinery only for a
concrete benefit that repays its construction, use, and maintenance. Keep runtime
resources reachable through the supported installed package and load them only
when relevant. Do not make runtime behavior depend on development fixtures,
private drafting history, or unsupported host controls. Where the governing
contract requires an enforceable permission boundary, use actual tool contracts
and supported host-enforced controls. Skill prose may state expected behavior, but
it does not change underlying permissions or prove that a host control exists; do
not claim a permission boundary is enforced when the host does not enforce it.

When a capability writes state or must survive interruption, define the relevant
revalidation, uncertain-write, supersession, and recovery behavior. Read live
state before a consequential retry when prior success is uncertain; a timeout does
not prove failure, and replacing a skill does not undo effects it already caused.
Compose with existing domain, writing, disclosure, execution, and safety guidance
without duplicating ownership or silently weakening it.

## Keep evidence and claims aligned

Evidence can constrain design before implementation, and an implementation change
can invalidate evidence obtained earlier. Keep evidence and claims bound to the
artifacts and conditions they actually support rather than treating evaluation as
a one-time phase after drafting.

Use applicable repository gates and the smallest additional check sufficient to
support the claim or lifecycle decision being made. Match evidence to the claim:
structural checks can establish packaging properties; executions can test
behavior; actual discovery can test routing; installed use can test integration;
and a fresh maintainer's change can test maintainability. An instruction that
states the intended rule does not establish that agents follow it.

Do not require an unrelated behavioral campaign for a settled structural or
wording correction merely because behavioral evaluation exists. Conversely,
structural validity, prose review, or an isolated example cannot support a claim
of behavioral effectiveness.

When comparison is relevant, use a credible alternative such as the prior version,
no skill, a competent short instruction, or an existing tool. Keep substantive
tasks, inputs, authority, environment, and other relevant conditions comparable.
For behavioral evidence intended to support claims about real-host behavior, use
the actual instruction roles, available tools, and observable host state relevant
to the claim. If a trial instead uses synthetic roles, mock tools, fabricated
state, or another simulation, identify those conditions and keep conclusions
scoped to them unless separate evidence supports transfer to the real host.
Separate requirements common to every comparison arm from candidate-specific
conformance obligations. Apply common correctness requirements to every arm and
apply candidate-specific packaging or conformance rules only to the conditions
they actually govern. Account for setup, loading, checking, failures, retries,
integration, and user or operator effort rather than optimizing one visible metric
in isolation. Do not infer end-to-end token usage or cost from visible answer
length. If output length or another observable is deliberately used as a proxy,
label it as a proxy and report only the property it actually measures rather than
presenting it as token or cost telemetry.

Test the governing contract rather than preferred wording or one golden
trajectory. Include legitimate alternatives, difficult boundaries, relevant
non-activation and no-change cases, and known-invalid cases where useful. Fixtures
must supply every premise a subject needs when that premise becomes relevant.
Distinguish satisfied, violated, not exercised, and not observable obligations;
missing evidence is not success.

Challenge evaluators, measurement mechanisms, and reviewer claims as well as
candidates. Check that valid alternatives can pass and known violations fail.
Inspect disputed findings against the actual artifact. When a conclusion depends
on a measurement, verify what the mechanism measures and the coverage or
completeness relevant to the conclusion. When numerical accuracy is needed for the
conclusion, use calibration, a known-value check, or another validity check suited
to the mechanism. Treat unavailable, incomplete, or suspect measurement evidence
as a limit on the claim. Distinguish fixture, evaluator, infrastructure, and
subject failures. Account for every assigned attempt and any retry it induces when
interpreting reliability or cost. Within the permitted retention boundary, retain
enough about failed, incomplete, evaluator-failed, and infrastructure-failed
attempts to show what happened; classify attempts that cannot support the primary
outcome rather than silently discarding them or counting them as success. A defect
in an evaluator does not automatically imply another runtime rule, and a runtime
defect does not justify rewriting historical evaluation results.

Use independent review or calibrated judgment when it is required or adds
information; self-review is not independent evidence. Keep author-visible
development cases separate from reserved confirmation material. Record exposure
and do not relabel inspected cases as held out.

Record relevant candidate, dependency, task, evaluator, model, host, and
environment identities when they are actually available and needed to interpret
the result; do not manufacture unavailable precision. Repeat trials when variation
matters to the claim. Decide important comparison criteria and stopping rules
before using final results rather than moving them to fit the candidate.

Keep evidence inspectable within its authorized retention boundary. Retain only
authorized content needed to support required evidence or accounting; prefer
redacted or structured records when they preserve those obligations. All-attempt
accounting does not require retaining unnecessary raw content. Excerpts are not
full runs, hashes do not supply missing bytes, and a fresh run does not reconstruct
lost historical evidence. Do not copy private material into a broader package
without authority. Preserve corrections and negative results, and qualify or
withdraw claims whose support is missing or invalidated.

## Deliver the justified result and control lifecycle transitions

Decide separately what result can be delivered and what lifecycle transition or
external action may be performed. A qualified draft, analysis, patch, or
experimental candidate can be useful even when publication, installation,
activation, or adoption is not justified or authorized.

Deliver the requested complete artifact or scoped patch when one is requested,
together with the relevant rationale, checks actually performed, limitations, and
current disposition. For evaluation-only work, deliver the supported assessment
without manufacturing an implementation change.

Keep structural validity, author review, independent review, behavioral evidence,
and broader effectiveness distinct. State only the strongest conclusion supported
by the available evidence. Missing evidence for a broad claim need not invalidate
a narrower supported artifact, but a missing mandatory gate still blocks the
transition or claim that gate governs.

Evidence does not grant action authority. A completed artifact, passing check, or
favorable review is not permission to publish, install, activate, adopt, retire,
spend resources, change external state, or establish recurring work. Perform only
the transitions authorized by the applicable request and governing instructions.

When an authorized transition has consequential external effects, use the
supported mechanism, applicable disclosure or attribution rules, and live state
where needed to verify the result. Prepared, committed, published, installed,
active, adopted, retired, and merely intended are not interchangeable states. Do
not report one as another because the transition was expected to succeed.

## Revise the affected layer or layers

When a finding appears, determine which affected layer or layers the evidence
supports changing. Identifying a failure does not necessarily establish its
cause. Do not automatically translate every incident into another runtime
instruction.

A contract defect or authorized semantic change belongs in the governing contract
and then in the implementations that realize it. An implementation defect should
be repaired without silently changing an unaffected contract. An evaluator,
fixture, retention, or inference defect may require new evidence or a narrower
claim without any runtime change. A lifecycle or action-authority failure may
require correcting state, reporting, or procedure rather than changing the skill's
behavioral model. One finding can affect more than one layer.

If the evidence does not establish which layer owns a defect, preserve that
uncertainty rather than compensating at an arbitrary layer. Obtain further
supported evidence when required for the intended result; if it remains
unavailable, preserve the resulting limit on the claim, disposition, or transition
in the applicable stopping and delivery decision.

Record corrections and withdrawn conclusions without rewriting history into a
claimed pass. After a revision, rerun or recheck what is needed for the changed
artifact and intended disposition; earlier evidence remains bound to the version
and conditions it actually evaluated. An evaluator correction requires an
explicitly revised evaluation rather than silent relabeling of the old result.

When requirements, evidence, hosts, dependencies, or supported mechanisms change,
reapply the governing goals to the affected choices. Preserve still-valid
contract obligations and historical evidence; revise or retire mechanisms whose
justification no longer holds. No change, simplification, narrower adoption,
consolidation, splitting, or retirement can be successful outcomes.

Apply the same discipline to this skill. Keep its current governing contract in
force unless a semantic contract change is separately authorized. A proposed
contract change does not govern its own evaluation or subsequent work. Current
wording, section structure, package boundaries, and other mechanisms are
candidates under that contract rather than requirements merely because they are
incumbent. When self-revision decides or changes its behavioral model, use
`model-refinement`. Reuse still-valid work and recheck affected responsibilities
within the current authoring task. Self-application does not itself require another
invocation or review layer, and agreement with yourself is not independent
validation.

The authoring task owns completion of the requested result. For conceptual work,
let `model-refinement` determine when refinement has locally converged or reached
a bounded stop; that disposition does not replace the authoring checks required
for the requested artifact, supported claims, or authorized action. Reuse
still-valid framing, evidence, and checks across both responsibilities rather
than creating a second refinement loop. Complete required downstream work before
closing the authoring task, or identify what remains blocked and qualify the
result under the delivery rules above. If that work supplies a concrete reason to
question the behavioral model, return to the affected refinement; a local defect
does not require restarting unaffected reasoning.

For other authoring work, stop when the requested artifact or disposition is
supported and the checks required for it are complete. A gate for an unrequested
action does not block a narrower justified result. Do not keep the task alive for
optional wording polish. Preserve unresolved required obligations and do not
schedule recurring work or broaden deployment without authority.
