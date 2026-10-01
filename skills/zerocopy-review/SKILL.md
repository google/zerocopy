---
name: zerocopy-review
description: >-
  Review proposed changes to google/zerocopy's zerocopy crate and derive crate.
  Use for pull-request, patch, or diff review where findings should account for
  zerocopy's correctness, compatibility, testing, maintainability,
  known merge-blocking placeholders and repository-style requirements.
---

# Zerocopy Code Review

Apply the repository-scoped instructions for the `zerocopy/` subtree in
addition to this skill.

## Establish Context

Do not review a diff in isolation when surrounding context can affect the
conclusion. Inspect the relevant definitions, callers, trait bounds, cfg gates,
imports, invariants, tests, and existing utilities as needed to establish each
finding. Do not assume that a function behaves as its name suggests; inspect its
definition or contract when the finding depends on it.

## Review Priorities

Prioritize findings in this order when several concerns compete for attention:

1. Soundness and security.
2. Functional correctness and edge cases.
3. API, compatibility, and configuration behavior.
4. Test adequacy.
5. Maintainability and repository style.

If the review involves unsafe Rust, unsafe APIs or traits, raw pointers, FFI,
layout or validity reasoning, safety comments or `# Safety` documentation,
soundness analysis, or invariant-bearing abstractions, also use the sibling
`unsafe-rust` skill. That skill is authoritative for
unsafe-code review methodology; do not reproduce a separate unsafe checklist
here.

## Correctness and Maintainability

Check the issues that are relevant to the changed behavior, including:

- panics or failures on valid input;
- unjustified `unwrap` or `expect` calls;
- zero-sized-type and boundary behavior;
- missing or incorrect generic bounds;
- configuration or feature-gate mismatches;
- duplicated logic that should use an existing utility or abstraction;
- surprising complexity or compressed code that obscures behavior;
- manual reimplementations of suitable standard-library, existing dependency,
  or established ecosystem functionality.

Before suggesting a new dependency, check `Cargo.toml` and the existing
workspace for an appropriate dependency or utility.

## Specification Meaning

For every specification under review, reconstruct the guarantee a human likely
intends. Ground that interpretation in the specification, surrounding
documentation, callers, reference implementations, and the bug or change that
motivated it. Compare the intended guarantee with what the specification
actually states. A passing proof establishes the written proposition; it does
not establish that the proposition captures the intended behavior.

Look for ways the written guarantee could be weaker than that intention:

- Requirements, ghost parameters, or branch guards exclude intended inputs.
  Inconsistent requirements, a ghost parameter with an empty type, or an
  admission predicate that always returns `false` can make a claim vacuous:
  there are no cases in which the promised behavior must hold.
- Automatic input decoding or type-model invariants restrict the domain beyond
  what a reader would reasonably infer from the function's specification.
- Postconditions omit intended observations, or compare projections that
  discard the information whose correctness matters.
- An equivalence harness checks only successful results or skips comparisons
  on relevant paths, leaving intended failure behavior or other cases unchecked.
- A reference implementation shares the very logic whose correctness the
  equivalence check is meant to establish.
- A partial-correctness contract allows divergence where termination is
  intended, or a proof covers fewer inputs or configurations than claimed.

A total `ensures _ => True` can be sufficient for an assertion harness:
successful termination requires its assertions to pass on admitted inputs.
Inspect the assertions and admission conditions rather than rejecting the
postcondition merely because it is `True`. Concrete admission examples can
expose vacuity, but do not establish coverage of every intended input.

Report substantiated gaps even when the proofs pass. State the intended
guarantee, the weaker written claim, and a distinguishing case when possible.
Keep inferred intention separate from the existing contract. When intention is
unclear, make that uncertainty explicit and seek clarification when needed;
do not silently invent a stronger requirement.

## Findings

Report actionable findings, not private chain-of-thought. For each finding:

- identify the affected code;
- state the concrete defect or risk;
- give enough externally checkable reasoning to establish it;
- state the consequence;
- give enough remediation direction for the author to act.

Use `BLOCKING` for an issue that must be fixed before merge and `NIT` for an
optional improvement. Provide replacement code when it materially clarifies the
fix; an exact snippet is not required when the remedy is already unambiguous.

<!-- TODO-check-disable -->
## TODO Placeholders

`TODO` intentionally blocks merge in this repository. During an in-progress
review, evaluate the surrounding implementation under the assumption that the
`TODO` will be resolved and report another finding only if a problem would
remain after that resolution. When evaluating merge readiness, an unresolved
`TODO` is itself blocking because CI rejects it.
<!-- TODO-check-enable -->
