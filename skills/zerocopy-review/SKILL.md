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
