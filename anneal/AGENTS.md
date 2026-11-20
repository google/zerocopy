<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Agent instructions for Anneal

These instructions apply to the current verifier in `anneal/` and its
build and CI integration. The historical workspaces in [`v1/`](v1/) and
[`v2/`](v2/) use their own instructions. In the rules below, repository-root
paths refer to the current verifier's project root, unless a rule refers to
Git history or a workflow under Zerocopy's root `.github/workflows/`.

Read this file before making changes in this repository. If a subdirectory
contains a more specific `AGENTS.md`, read and follow that file as well.

## Project principles

Before designing, modifying, or reviewing repository artifacts, read and
preserve [`META_PRINCIPLES.md`](META_PRINCIPLES.md),
[`PRINCIPLES.md`](PRINCIPLES.md), and [`THREAT_MODEL.md`](THREAT_MODEL.md),
which define Anneal's governing meta-principles, mission, correctness promise,
threat model, and decision-making principles.

## Standing rules

Apply these rules to work on the current verifier:

- **File headers:** New source, script, workflow, and documentation files must
  begin with the repository's Fuchsia copyright and license header (matching
  [`PRINCIPLES.md`](PRINCIPLES.md) or [`ci/check_todo.sh`](ci/check_todo.sh)
  in the appropriate comment syntax for the file type) using the file's
  creation year. Preserve the original creation year when modifying an existing
  file. Files whose syntax requires leading metadata or forbids comments (such
  as JSON files or `SKILL.md` files with leading YAML frontmatter) are exempt.
<!-- TODO-check-disable -->
- **`TODO` markers:** Do not leave `TODO` markers in code, documentation, or
  commit messages unless you intend to block merging;
  [`./ci/check_todo.sh`](ci/check_todo.sh) rejects `TODO` across the working
  tree and all commits in `origin/main..HEAD`. Use `FIXME` for non-blocking
  follow-up work. Any temporary or exempted `TODO` must cite an issue using
  `TODO(#123):`.
<!-- TODO-check-enable -->
- **Prose and explanations:** Use simple, plain-spoken prose without sacrificing
  precision or accuracy. Apply the writing skills required below.
- **Prose and comment wrapping:** Wrap prose in code comments and Markdown
  files at 80 columns from the left margin when practical, including any
  comment prefix (`//`, `///`, `//!`, `--`, `/--`, `/-!`). Do not wrap Markdown
  tables, ASCII diagrams, long URLs, code blocks, or trailing inline comments
  when wrapping would impair readability. Indent wrapped bullet continuation
  lines by two spaces, and put a blank line between paragraphs and after section
  headings.
- **Pre-commit validation:** Run `./ci/check_todo.sh` (along with any build or
  test checks applicable to the changed files) before finishing a task or
  committing.

## Required skills

The [`skills/`](skills/README.md) directory contains the skills that govern work
in this repository. Whenever your task involves an activity in the table below,
open and read the full `SKILL.md` for every listed skill (plus any
`references/` files it routes you to) before performing that work. Do not infer
a skill's rules from its name or summary. Skills compose: when more than one
applies, follow all of them.

| Activity | Required skills |
| :--- | :--- |
| Reviewing code, commits, or pull requests, or auditing changes for trust-boundary compliance | [`trust-review`](skills/trust-review/SKILL.md) |
| Designing, implementing, refactoring, or reviewing code for human comprehension, invariants, or safe evolution | [`robust-code`](skills/robust-code/SKILL.md) |
| Writing, revising, or reviewing any technical prose (documentation, code comments, commit messages, PR descriptions, or issue bodies) | [`reader-oriented-explanation`](skills/reader-oriented-explanation/SKILL.md), [`williams-style`](skills/williams-style/SKILL.md) |
| Adding, revising, or reviewing explanatory inline (`//`, `--`) or documentation (`///`, `//!`, `/--`, `/-!`) code comments | [`comment-guidelines`](skills/comment-guidelines/SKILL.md), [`reader-oriented-explanation`](skills/reader-oriented-explanation/SKILL.md), [`williams-style`](skills/williams-style/SKILL.md) |
| Structuring commits, drafting or revising commit messages, rebasing or amending commits, or managing branches and pull requests | [`source-control`](skills/source-control/SKILL.md), [`commit-message`](skills/commit-message/SKILL.md), [`authorship-disclosure`](skills/authorship-disclosure/SKILL.md), [`reader-oriented-explanation`](skills/reader-oriented-explanation/SKILL.md), [`williams-style`](skills/williams-style/SKILL.md) |
| Preparing or updating Git commits, pull request descriptions, or other externally visible prose | [`authorship-disclosure`](skills/authorship-disclosure/SKILL.md) |
| Designing or redesigning a system, subsystem, semantic model, protocol, or framework end to end | [`architectural-design`](skills/architectural-design/SKILL.md), [`model-refinement`](skills/model-refinement/SKILL.md), [`swarm-model-refinement`](skills/swarm-model-refinement/SKILL.md), [`reader-oriented-explanation`](skills/reader-oriented-explanation/SKILL.md), [`williams-style`](skills/williams-style/SKILL.md) |
| Designing, simplifying, or generalizing conceptual models, semantic interfaces, schemas, protocols, or instructions | [`model-refinement`](skills/model-refinement/SKILL.md) |
| Coordinating multi-agent conceptual model refinement across theories, software designs, schemas, protocols, or instructions | [`swarm-model-refinement`](skills/swarm-model-refinement/SKILL.md), [`model-refinement`](skills/model-refinement/SKILL.md) |
| Creating, revising, evaluating, or retiring agent skills or maintainer guidance | [`skill-authorship`](skills/skill-authorship/SKILL.md), [`model-refinement`](skills/model-refinement/SKILL.md) |
| Leading or directing ambiguous engineering efforts, recovering requirements, developing or evaluating architecture, or recovering technical understanding after context loss | [`tech-lead`](skills/tech-lead/SKILL.md), [`reader-oriented-explanation`](skills/reader-oriented-explanation/SKILL.md), [`williams-style`](skills/williams-style/SKILL.md) |
| Conducting multi-round technical research and experimentation (for example, on Rust, `rustc`, Lean 4, or verification models), or harvesting expensive-to-recover findings into the reference corpus (with user approval) | [`reference-research`](https://github.com/google/zerocopy/blob/reference/skills/reference-research/SKILL.md) (on `google/zerocopy`'s `reference` branch; see [Technical reference corpus](#technical-reference-corpus)) |

## Architecture and trust boundary

Anneal verifies Rust programs (including unsafe code) by extracting typed
`Runtime(PostCleanup)` MIR and compiler facts via `anneal-rustc-capture` and
checking the crate's `Trusted.CrateTheorem` (`VerificationResult` over every
captured function's `Compiler.Verified` obligations) inside the Lean 4 kernel.

See [`README.md`](README.md) for the correctness policy and `trusted/`
invariant, [`THREAT_MODEL.md`](THREAT_MODEL.md) for the threat model, bounded
human-review surfaces (stated specifications and the TCB audit log), and
explicit assumptions, [`docs/design.md`](docs/design.md) for the overall
design, [`docs/architecture.md`](docs/architecture.md) for the three-stage MIR
pipeline and repository layout, and [`docs/trust-model.md`](docs/trust-model.md)
for how `trusted/` and `trusted/audit/` enforce the trust boundary. Before
placing or modifying code, check whether it belongs inside `trusted/` or
outside it (`theory/`):

- Only primitive semantic and theorem definitions required to state or gate
  `Trusted.CrateTheorem` and `VerificationResult` (`trusted/lean/`) and
  effectful components—the `.olean` kernel-environment inspector
  (`trusted/audit/`), the CLI orchestrator and boundary audit runner
  (`trusted/cargo-anneal/`), and the `rustc` MIR/attribute serializer and pure
  proof-script generator (`trusted/rustc-capture/`)—belong in `trusted/`.
- All code outside `trusted/` (`theory/`) must be pure, effect-free Lean
  definitions and proofs checked by the Lean kernel.

When reviewing code or auditing changes before committing, run a dedicated
[`trust-review`](skills/trust-review/SKILL.md) pass both to verify that code
outside `trusted/`, `ci/`, and `.github/` cannot bypass trust auditing and to
audit any changes inside `trusted/`, `ci/`, `.github/`, or pinned root
manifests.

## Commenting in `trusted/`

Because auditing `trusted/` and its explicit, pinned dependency manifest must
suffice to verify that Anneal upholds
[`META_PRINCIPLES.md`](META_PRINCIPLES.md), [`PRINCIPLES.md`](PRINCIPLES.md),
and [`THREAT_MODEL.md`](THREAT_MODEL.md), all code in `trusted/` will undergo
careful human review. Human understanding is
therefore paramount in `trusted/`: comment liberally using
[`comment-guidelines`](skills/comment-guidelines/SKILL.md) (and its companion
writing skills in the table above) so a human auditor can verify the design
rationale, invariants, assumptions, contracts, and subtle semantic or
implementation choices without reconstructing unstated context.

Any code in `trusted/` that claims to model Rust semantics or extract `rustc`
compiler structures must explain the correspondence in its comments and both
quote and cite the applicable Rust documentation (`rust-lang/reference`) or
compiler source (`rust-lang/rust`) at a pinned commit hash.

## Dependencies in `trusted/`

When implementing or modifying components in `trusted/`:

- **Do not hand-roll standard utilities:** Do not write bespoke argument
  parsers, serializers, cryptographic hashers, or logging machinery to avoid
  adding a dependency. Rely on battle-tested, standard ecosystem crates.
- **Audit economy:** A concise, idiomatic interface built on a standard crate
  is much easier for human reviewers to audit than hundreds of lines of
  hand-rolled plumbing.
- **Dependency discipline:** Keep dependencies in `trusted/` focused and
  conservative. Prefer crates with minimal transitive dependencies and generic,
  well-understood failure modes that do not pose soundness risks specific to
  Anneal.

## Technical reference corpus

The orphan [`reference`](https://github.com/google/zerocopy/tree/reference)
branch of `google/zerocopy` (`refs/heads/reference` in a local `zerocopy`
checkout or worktree, or fetched from `https://github.com/google/zerocopy.git`)
maintains a general-purpose technical reference corpus (`CATALOG.json` and
`reports/<package>/`) covering topics such as Rust operational semantics,
`rustc` MIR stages and internals, Lean 4 kernel and elaboration behavior,
Charon, Aeneas, and Anneal's verification architecture.

- **Consulting existing research:** When designing architecture, modeling
  semantics, or investigating non-obvious system, compiler, or kernel behavior,
  check the `reference` branch (when accessible in your environment) and follow
  its [`AGENTS.md`](https://github.com/google/zerocopy/blob/reference/AGENTS.md)
  before repeating broad source crawls or experiments from scratch:
  - Filter `CATALOG.json` programmatically (rather than reading the full file
    into context) to find relevant packages under `reports/<package>/`.
  - Check each report's subject revisions (`REPORT.json`), `Applicability`, and
    `Boundaries` against the versions Anneal pins. Primary upstream sources
    retain authority and must still be quoted and cited directly in `trusted/`
    comments.
- **Running new `reference-research` (human approval required):** When a design
  or soundness decision depends on non-obvious technical behavior that is not
  in `CATALOG.json` and cannot be resolved by a quick local check—or after an
  engineering task uncovers expensive-to-recover findings worth preserving—
  consider [`skills/reference-research/SKILL.md`](https://github.com/google/zerocopy/blob/reference/skills/reference-research/SKILL.md)
  on `google/zerocopy`'s `reference` branch. Do not launch `reference-research`
  or push to `google/zerocopy` without explicit user approval: state the
  concrete question(s) or findings to harvest and ask the user whether to run
  `reference-research` (and whether to stop after **brainstorm / plan only** or
  run **end-to-end execution and publication**).
