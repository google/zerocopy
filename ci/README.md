<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# CI configuration and local commands

Zerocopy's ordinary build and Miri matrices are planned and executed by typed
Rust code. GitHub Actions remains a small security and scheduling boundary: it
chooses triggers, permissions, runners, actions, setup, artifacts, and required
checks, but it does not independently reconstruct matrix coverage or Cargo
commands.

This guide describes where each kind of fact belongs, how the pieces validate
one another, and how to change coverage deliberately. Anneal has a separate
Nix-backed build path; its temporary v1 example matrix is described at the end.

## Where facts belong

| Source | What it owns |
| --- | --- |
| [Cargo manifests](../zerocopy/Cargo.toml) | Workspace packages and Cargo targets, feature definitions and edges, default features, `rust-version`, pinned stable and nightly versions, `build.rs` compatibility versions, and docs.rs Rustdoc arguments. [`tools/rust-toolchain.toml`](../tools/rust-toolchain.toml) separately pins the compiler used to build repository tools and must match the pinned stable compiler. Policy refers to reviewed package IDs, manifest paths, and the stable feature root, but it does not copy the resolved feature, target, or compiler-version facts. |
| [`ci/zc.toml`](zc.toml) | Deliberate ordinary-CI coverage: exact event classes, package and feature-profile IDs, compilation-target modes and eligibility, target-set expressions, toolchain scopes and version sources, Miri models and scopes, semver coverage and waivers, baseline paths, and GitHub size limits. It cannot grant workflow privileges or invent Cargo facts. |
| [`policy.rs`](../tools/zc/src/policy.rs) | The accepted policy schema and its fail-closed validation: references, set expressions, coverage constraints, safe paths, bounds, and deterministic ordering. Schema changes belong here; repository-specific choices belong in `ci/zc.toml`. |
| [`inventory.rs`](../tools/zc/src/inventory.rs) and [`metadata.rs`](../tools/zc/src/metadata.rs) | Live facts read from Cargo and checked repository files. Inventory resolves packages, feature closure, Cargo targets, compiler versions, and docs.rs arguments, then verifies every policy reference. It also checks the deliberately narrow `build.rs` metadata text contract. |
| [`ci.rs`](../tools/zc/src/ci.rs) | The all-or-nothing checked input boundary. `CiInputs::load` canonicalizes contained inputs and admits no plan until policy, Cargo inventory, workflow jobs, the planned-job and semver adapters, frozen baselines, and execution parity all pass. |
| [`plan.rs`](../tools/zc/src/plan.rs) | Pure, deterministic ordinary-build and Miri membership. A plan contains complete selectors and execution meaning, but no command strings, permissions, runner labels, actions, secrets, or publication choices. |
| [`execution.rs`](../tools/zc/src/execution.rs) | The exact argv vectors and environment for a selected cell, ordinary target behavior, Miri setup and model flags, and parity with the frozen command and logical-work evidence. It executes only a selector that resolves uniquely in a newly checked plan. |
| [`github.rs`](../tools/zc/src/github.rs) | Versioned, deterministic transport from one plan explanation to compact GitHub matrices and a detailed review artifact. It enforces matrix and UTF-16 job-output limits; it does not carry workflow authority. |
| [`workflow_protocol.rs`](../tools/zc/src/workflow_protocol.rs) | Shared spellings used at the CLI, projection, and planned-job workflow boundaries: command names, output names, job names, and selector fields. This private module prevents the Rust implementation from drifting internally; it does not grant workflow authority or choose coverage. |
| [`ci/baselines`](baselines/README.md) | Independent evidence of the behavior that the typed implementation replaced: reduced/full matrix membership, logical and standalone work, and representative commands. These files are expected review data, not planner output. |
| [Workflow YAML](../.github/workflows/ci.yml) | Events, permissions, runners, concurrency, most third-party action references, Docker and tool setup, artifact transfer, static jobs, and the required-check aggregate. [`workflow-jobs.tsv`](workflow-jobs.tsv) gives every live job a reviewed role, and [`workflow.rs`](../tools/zc/src/workflow.rs) rejects unregistered jobs or unsupported declaration syntax. Behavior-bearing workflow bridges receive separate exact Rust audits in [`planned_adapter`](../tools/zc/src/planned_adapter/mod.rs) and [`semver_adapter.rs`](../tools/zc/src/semver_adapter.rs) rather than being trusted because their jobs are registered. The semver action is an explicit exception: its literal YAML is checked against reviewed adapter constants as well as checked inputs. |
| [`githooks/pre-push`](../githooks/pre-push) and check scripts | Local orchestration and repository-wide checks. The hook bootstraps pinned tools, runs checks concurrently, verifies that every check script is included, and rejects lockfile mutation. In particular, [`check_tools.sh`](check_tools.sh) tests the Rust CI implementation and runs `ci audit`; [`check_actions.sh`](check_actions.sh) validates Actions files and the hook; and [`check_job_dependencies.sh`](check_job_dependencies.sh) protects required-check aggregation. |

## Validation and execution flow

1. `CiInputs::load` resolves the repository root and every fixed input without
   allowing a checked-in symlink to redirect planning outside the checkout.
2. Policy parsing, workflow-job inventory, the planned-job workflow audits,
   Cargo inventory, the literal semver adapter audit, and canonical baseline
   parsing each run before a caller can obtain checked inputs.
3. The execution model expands representative reduced and full behavior and
   must match the frozen matrix, logical-work, standalone-work, and command
   evidence exactly. `ci audit` also plans every configured event.
4. `Plan` or `PlanExplanation` selects cells for one exact event. Planning is
   pure after input validation.
5. `GitHubProjection` creates `build_matrix` and `miri_matrix` job outputs plus
   `ci-plan.json` from the same explanation. The workflow expands only the
   compact selectors.
6. Each matrix runner reloads and revalidates the repository, resolves its
   complete selector against a fresh plan, reconstructs typed argv and
   environment values, and executes that one cell in the prebuilt CI image.
   The narrow workflow bridge requires its hosted runner, interpreter, and
   Docker invocation explicitly, clears Bash startup controls, and overrides
   the image entrypoint. The audit rejects an uncoordinated workflow edit to
   the fixed PATH, shell, `runs-on`, Docker command, or image entrypoint. The
   hosted runner and image implementations remain part of the trusted runtime.
   An unknown, excluded, or ambiguous selector fails instead of falling back
   to similar work.

The exact event classification is:

- reduced coverage: `pull_request`;
- full coverage: `merge_group`, `push`, and `workflow_dispatch`.

There is no default class for an unknown event. Miri is currently full-only, so
the pull-request Miri matrix is empty and the workflow skips that job before
matrix expansion. The event names must stay coordinated among the workflow
triggers, `[events]` in `ci/zc.toml`, and the independent event-class list in
[`plan.rs`](../tools/zc/src/plan.rs).

## Making coverage changes

Start with the file that owns the fact, then run `ci audit` to identify typed
control-plane assumptions which must be reviewed. Also run the complete
pre-push checks: `ci audit` does not replace the independent Actions, hook, or
required-check dependency audits. Do not make a second list merely to silence
the first failure.

### Features and packages

- Add, remove, rename, and connect features in the appropriate Cargo manifest.
  The `all` profile naturally uses Cargo's complete feature set. The stable
  profile is the closure of
  `__internal_use_only_features_that_work_on_stable`; every other feature is
  naturally treated as nightly-only. To classify a new stable feature, add the
  correct Cargo feature edge rather than copying its name into `ci/zc.toml`.
- Changes to default features naturally change the `default` profile because
  that profile intentionally passes no feature override.
- A new first-party workspace package fails inventory until it is deliberately
  represented by policy or by the narrowly reviewed support-package exception
  in `inventory.rs`. Add its manifest and meaningful profiles to `ci/zc.toml`,
  then assign toolchain scopes.
- Renaming or removing a package, aggregate feature, or manifest path makes
  inventory fail at the stale policy reference.

### Toolchains

- Update compiler versions in their Cargo-owned source: `rust-version`,
  `[package.metadata.ci]`, or `[package.metadata.build-rs]`. Do not place a
  version literal in `ci/zc.toml`.
- Keep `tools/rust-toolchain.toml` equal to the pinned stable version; the tool
  checks reject a partial roll.
- Add a new descriptor and its package/profile/target scopes in `ci/zc.toml`.
  Build-script descriptors must also satisfy the exact metadata text contract
  parsed by `zerocopy/build.rs`.
- A version or scope change which alters reviewed behavior fails execution or
  baseline parity until its intended effect is independently recorded.

### Compilation targets, events, and workflow jobs

- Declare a compilation target once in `[[targets]]`, including its ordinary
  execution mode and explicit pull-request, Miri, and semver eligibility.
  Broad target sets include future declared targets automatically; explicit
  sets and exclusions remain visible exceptions. The policy validator rejects
  redundant set edits and Miri or semver eligibility gaps.
- Assign target sets through toolchain scopes. If the selected reduced or full
  matrix changes, exact baseline comparison reports the missing and extra
  cells separately.
- Adding an event requires an explicit reduced/full choice in `ci/zc.toml`, a
  workflow trigger, and an update to the independent event classification in
  `plan.rs`. An unknown event is rejected.
- Adding or renaming a workflow file or top-level job fails the workflow audit
  until `workflow-jobs.tsv` assigns a reviewed role. If the job contributes to
  the required result, also add it to `all-jobs-succeed.needs`; the independent
  `check_job_dependencies.sh` audit rejects an unaggregated dependency. A new
  planned job must additionally be represented by the planned-role and exact
  workflow-bridge audits. New syntax in the deliberately narrow `jobs:` or
  top-level job-declaration forms fails until the scanner is reviewed.
- The aggregate's display name, `All checks succeeded (ci.yml)`, is the status
  check selected by GitHub repository rules. A rename must be coordinated with
  those external rules as well as the workflow and local audits, or GitHub can
  wait forever for the old required check.
- The workflow currently consumes one ordinary matrix and one Miri matrix. If
  either needs more than the configured 256 cells, projection fails with an
  instruction to add another workflow shard; it never drops excess cells.

After an intentional behavior change, update the files under `ci/baselines`
using evidence independent of the new planner. Follow
[`ci/baselines/README.md`](baselines/README.md): retain source identity, compare
exact sets rather than only counts, preserve canonical sorting, and review the
logical and command effects. Do not generate expected rows from the code they
are meant to check. Otherwise the same bug could change both the implementation
and its supposed evidence while leaving `ci audit` green.

## Local entry points

Run these commands from the repository root. `cargo.sh` builds the repository
tool with its pinned compiler before routing the `ci` subcommand.

Validate every input and all configured events:

```sh
./zerocopy/cargo.sh ci audit
```

Print selected cells, or explain both selected and excluded candidates:

```sh
./zerocopy/cargo.sh ci plan --event pull_request
./zerocopy/cargo.sh ci explain --event merge_group
```

Create the same compact outputs and detailed artifact used by Actions. The
GitHub-output file must already be a regular file, the artifact must not exist,
and the two paths must not alias:

```sh
plan_dir="$(mktemp -d)"
: > "$plan_dir/github-output"
./zerocopy/cargo.sh ci github-plan \
  --event pull_request \
  --github-output "$plan_dir/github-output" \
  --artifact "$plan_dir/ci-plan.json"
```

Execute one exact ordinary cell selected by the plan:

```sh
./zerocopy/cargo.sh ci execute-build-cell \
  --event pull_request \
  --package zerocopy \
  --toolchain stable \
  --feature-profile stable \
  --target x86_64-unknown-linux-gnu
```

Execute one exact Miri cell selected by a full event:

```sh
./zerocopy/cargo.sh ci execute-miri-cell \
  --event merge_group \
  --package zerocopy \
  --toolchain nightly \
  --feature-profile default \
  --target x86_64-unknown-linux-gnu \
  --miri-model stacked
```

Use `ci plan` to copy a complete selector; the executor requires every field
and will not infer a nearby cell. These execution commands run build or test
processes and may install the selected compiler or target through the wrapper.

For the same validation used by CI, run `./ci/check_tools.sh`. The complete
local gate is `./githooks/pre-push`; it is broader and may take substantially
longer.

## Projection outputs and the semver exception

`github-plan` appends three newline-delimited output records:

- `build_matrix={"include":[...]}` contains package, toolchain,
  feature-profile, and target selectors;
- `miri_matrix={"include":[...]}` adds the Miri model selector;
- `miri_enabled=true` if and only if the Miri matrix is nonempty. The workflow
  uses this same value both to enable the Miri job and to decide whether its
  required-check result must be `success` or `skipped`.

The pretty `ci-plan.json` artifact is versioned review evidence. It includes
the policy schema version, event and class, selected/excluded counts, every
candidate's typed decision and reason, exact compiler versions,
repository-relative manifest paths, feature semantics, ordinary execution
modes, and Miri model flags. It deliberately contains no permissions, runners,
actions, commands, run IDs, timestamps, absolute paths, or other
authority-bearing or nondeterministic fields. The workflow uploads it for 14
days.

GitHub requires `uses:` to be literal YAML, so the typed executor cannot invoke
the `cargo-semver-checks` action. Eligible ordinary cells report that step as
workflow-owned. [`semver_adapter.rs`](../tools/zc/src/semver_adapter.rs) builds
the expected literal step from checked inputs and reviewed adapter constants,
then rejects any unreviewed change to the one literal step in `ci.yml`. An
action revision, feature-group, or warning-flag change must coordinate the Rust
constant, literal workflow step, and independent command golden. The workflow
then runs that audited action after the ordinary cell executor.

## Local execution platform

The two exact-cell executors currently preserve the Linux Actions command
contract and invoke the Unix `./cargo.sh` path. Inspection, explanation, and
projection remain useful on other hosts, but do not treat cell execution as a
portable Windows adapter. Miri additionally requires GNU `nproc` on `PATH`; its
one-line processor count is strictly parsed and checked before doubling, and a
host without that command fails explicitly. Miri execution also assumes
exclusive use of the checkout while it temporarily moves and then restores
`zerocopy/.cargo/config.toml`, so do not run two Miri cells concurrently in one
worktree.

## Temporary Anneal v1 matrix

[`verify_examples` in `anneal.yml`](../.github/workflows/anneal.yml) intentionally
keeps an explicit matrix list for Anneal v1 examples. Anneal v1 is being
replaced, so this temporary adapter is not part of the typed ordinary-CI planner
and is not an inventory of every file under `anneal/v1/examples`.

When adding or removing a covered example, edit the matrix list. If temporary
v1 support requires an expected-failing example, also keep the step's inline
`KNOWN_FAILING` list coordinated. That mechanism deliberately distinguishes
only the command's exit status; do not build a new discovery or diagnostic
classification layer merely to perfect this short-lived matrix.
