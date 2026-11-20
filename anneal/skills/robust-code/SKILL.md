---
name: robust-code
description: >-
  Design, implement, refactor, or review code for human comprehension and safe
  evolution. Prefer functional data flow, explicit effects, and representations
  that exclude invalid states; use typestate where it simplifies valid operation
  sequences. Use when these concerns matter to a coding task or when scaffolding
  an agent to produce such code. Not for cosmetic rewrites, mandatory functional
  syntax, or unrelated architecture changes during a bounded fix.
---

# Robust code

Make correct behavior easy to understand and preserve. A future maintainer should
be able to identify the invariant, follow the relevant data and effects, and see
what must change when the requirements change. Prefer designs in which a plausible
mistake is rejected by construction or produces a focused diagnostic, rather than
requiring a reviewer to remember a distant convention.

These are engineering preferences under the task's correctness, compatibility,
resource, and authorization constraints, not a promise of bug freedom. Apply them
to the affected boundary; do not turn a small fix into a framework or a rewrite.

## Establish the behavior and the checks

Read the applicable repository instructions, affected definitions and callers,
and relevant tests. Establish the required observations: accepted and rejected
inputs, outputs, errors, ordering, effects, and compatibility. Existing code and
tests are evidence, not permission to preserve a known defect or change a contract.
Keep uncertain product requirements provisional rather than encoding guesses as
permanent type-level rules.

Identify the important invariants and who can invalidate them. For each invariant
that matters to the change, locate its enforcing representation or boundary and
the check that would expose a violation. Keep this mapping in existing code,
tests, or the task's design note; do not create a parallel ledger by default.

Find the actual build, type-check, lint, and test commands and establish a relevant
baseline. For a substantial API change, test a small type/API skeleton and its
callers before investing in the full implementation. Use feedback as evidence
about the design, not merely as an obstacle to remove.

## Represent valid situations directly

Model alternatives with variants carrying the data each alternative requires,
rather than independent flags, optional fields, or sentinel values whose legal
combinations callers must memorize. Derive redundant state when practical. Keep
independent dimensions independent; do not merge distinct permissions, outcomes,
or responsibilities just to reduce the number of fields or states.

Establish refinements at a controlled boundary and carry the evidence forward:
parse untrusted input into a validated value, use an opaque constructor or module
boundary when callers must not forge it, and accept that value where its invariant
is required. Inspect every construction and mutation path, including deserialization,
FFI, alternate factories, aliases, and test helpers that can escape into production.
A type name or unchecked cast is not validation.

Use typestate when the operations available on a value depend on its lifecycle.
Express a transition as an operation from the old state to the new one. Where the
language's ownership discipline supports it, consume the old capability when reuse
would be invalid. Avoid exposing copying, aliasing, or alternate constructors that
undo this protection. Without that discipline, use an authoritative runtime state
owner when single-use or sequencing matters; phantom types alone do not provide it.

Choose the least complicated representation that preserves the required behavior.
A runtime enum and an exhaustive transition function can be better than a generic
state machine, especially with dynamic states or heterogeneous collections.
Preserve real intermediate, failure, cancellation, and unknown-outcome states.
Eliminating a necessary case is not making an illegal state unrepresentable.

A local type cannot keep an external fact true. A checked path, authorization,
version, lease, or remote resource may become stale. Bind the operation to the
relevant authority with a transaction, compare-and-swap, version check, or other
appropriate protocol when correctness requires it. A separate preflight check is
insufficient when another actor can change the fact before use.

## Prefer functional data flow and explicit effects

Keep decisions and transformations in functions whose dependencies and results
are visible. Prefer immutable values and explicit returns to shared mutable state,
output parameters, hidden caches, or mutation across callbacks. Pass clocks,
randomness, configuration, and other changing inputs explicitly when they affect
the decision. Separate domain decisions from the code that performs I/O.

This is a preference for local reasoning, not for particular syntax. A simple loop
with a private accumulator can be easier to understand than a nested iterator chain
or a clever fold. Local mutation is acceptable when it cannot escape, its lifetime
is clear, and it improves clarity or meets a resource constraint. Do not copy large
structures, build an effect framework, or introduce deep indirection merely to make
code look functional. Explain a consequential tradeoff, not every local variable.

Make effects, their order, and ownership visible at the boundary. Separate a plan
from its execution where that permits useful independent checking, but account for
stale plans and partial execution. Do not move domain policy into a large imperative
shell solely to keep a small helper pure. Preserve atomicity, cleanup, and error
semantics when reorganizing work.

## Make later mistakes conspicuous

Use meaningful domain names, explicit dependencies, and cohesive functions. Keep
an invariant near the operation or owner that enforces it; encapsulate changes that
must happen together. Extract an abstraction when it reduces the concepts callers
must track, not just because it shortens a function or removes similar-looking text.
Comments should explain a non-obvious constraint or design reason rather than
restate the implementation.

Handle a closed set of cases exhaustively so adding a variant exposes the decisions
that need review. Avoid catch-all success, default values, or swallowed errors that
silently assign semantics to a new case. For intentionally open protocols, provide
an explicit unknown-case policy instead of pretending the set is closed.

Define expected failures in the result or the language's established error
mechanism. Prefer operations defined for their declared input domain; establish a
precondition in the input type or handle its absence explicitly. Do not hide partial
operations behind unchecked indexing, assertions, or exceptions labeled impossible
without a supporting invariant. Check arithmetic and resource limits where relevant.

For externally visible effects, distinguish failure from unknown success. Do not
retry a timed-out write as though it certainly did nothing. Use reconciliation,
idempotency, or a transactional protocol as the domain requires. Represent cleanup,
cancellation, and recovery obligations so that an added early return cannot silently
skip them.

## Verify the implementation and its resistance to change

Run the relevant checks against the actual final code. Repair the cause of a failed
check; do not get green results by widening types, inserting casts, disabling rules,
weakening assertions, or removing an inconvenient test. A legitimate contract or
test correction needs its own rationale and evidence, not silent acceptance of the
candidate's behavior.

Test the invariant, not only the example that motivated it. Select checks according
to the risk: compile-fail API tests for forbidden calls, property or model-based
tests for state transitions, differential tests for behavior-preserving changes,
and integration or fault-injection tests for effects and recovery. State what each
check does not cover. A passing compiler does not establish the business contract;
a passing test suite does not establish human comprehension.

For a consequential changed boundary, challenge a plausible small future edit:
add a variant, bypass a constructor, change a boundary comparison, introduce an
alias, or insert an early return. Ask which compiler error, focused test, or local
review obligation catches it. Use a temporary mutation or extension probe when it
adds useful evidence, and remove the probe afterward. Investigate a surviving
violation; do not add brittle tests for changes that preserve the contract merely
to increase a mutation score.

Review the patch from the maintainer's perspective: can they explain why each
state is valid, trace effects and failures, and locate the obligations of a new
case without reconstructing distant assumptions? Simplify the representation or
supply the missing local explanation when they cannot. Do not substitute naming,
line counts, or a readability score for this check.

## Use the surrounding agent scaffold honestly

Prompting is one control, not enforcement. Keep repository guidance short and
specific to facts the agent would otherwise miss. When authorized to configure a
workflow, make the relevant checks runnable, return actionable diagnostics, and
have the host verify completion against actual artifacts rather than the agent's
success statement. Protect required acceptance checks outside the candidate's
unreviewed edit authority when an enforced gate is needed. Do not claim that prose,
a hook the agent can bypass, or a checker it can rewrite enforces that boundary.

After interruption, re-read the live revision, diff, and relevant check results;
a prior success applies only to the artifact and environment it checked. Preserve
other contributors' work. Revalidate uncertain external writes before retrying.
Do not install tools, change repository policy, publish, deploy, or spend on agent
evaluations without the authority required by the task.

Load [design examples](references/design-examples.md) when a representation choice
needs clarification; this reference is not required for every edit. Use
separately available domain, writing, and model-refinement guidance when
applicable; this package does not bundle or automatically activate other skills.

Deliver the requested code or review with the important invariant, consequential
tradeoff, checks actually run, and remaining limits. Keep that explanation as small
as the change permits. Distinguish a proposed guardrail, an implemented guardrail,
a successfully exercised check, and evidence that an agent follows the workflow.
