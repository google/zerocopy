<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# CI configuration and local commands

Zerocopy's ordinary build, Miri, and semver matrices are planned by typed Rust
code. The ordinary build and Miri commands are also executed by that code;
GitHub requires the semver action invocation to remain literal workflow YAML.
GitHub Actions remains a small security and scheduling boundary: it chooses
triggers, permissions, runners, actions, setup, artifacts, and required checks,
but it does not independently reconstruct matrix coverage or Cargo commands.

This guide describes where each kind of fact belongs, how the pieces validate
one another, and how to change coverage deliberately. Anneal has a separate
Nix-backed build path; its temporary v1 example matrix is described at the end.

## Where facts belong

| Source | What it owns |
| --- | --- |
| [Cargo manifests](../zerocopy/Cargo.toml) | Workspace packages and Cargo targets, feature definitions and edges, default features, `rust-version`, pinned stable and nightly versions, `build.rs` compatibility versions, and docs.rs Rustdoc arguments. [`tools/rust-toolchain.toml`](../tools/rust-toolchain.toml) separately pins the compiler used to build repository tools and must match the pinned stable compiler. Policy refers to reviewed package IDs, manifest paths, and the stable feature root, but it does not copy the resolved feature, target, or compiler-version facts. |
| [`ci/zc.toml`](zc.toml) | Deliberate ordinary-CI coverage: exact event classes, package and feature-profile IDs, compilation-target modes and eligibility, target-set expressions, toolchain scopes and version sources, Miri models and scopes, semver coverage and waivers, baseline paths, and GitHub size limits. It cannot grant workflow privileges or invent Cargo facts. |
| [`policy.rs`](../tools/zc/src/policy.rs) | The accepted policy schema and its fail-closed validation: references, set expressions, coverage constraints, safe paths, bounds, and deterministic ordering. Schema changes belong here; repository-specific choices belong in `ci/zc.toml`. |
| [`inventory.rs`](../tools/zc/src/inventory.rs) and [`metadata.rs`](../tools/zc/src/metadata.rs) | Live facts read from Cargo and checked repository files. Inventory resolves packages, feature closure, Cargo targets, compiler versions, and docs.rs arguments, then verifies every policy reference. It also checks the deliberately narrow `build.rs` metadata text contract and the two-way invariant that every `package.metadata.build-rs` version key has one typed build-rs toolchain descriptor and every such descriptor has a manifest key. Policy separately requires each descriptor to have nonempty scopes. |
| [`ci.rs`](../tools/zc/src/ci.rs) | The all-or-nothing checked input boundary. `CiInputs::load` canonicalizes contained inputs and admits no plan until policy, Cargo inventory, workflow jobs, frozen baselines, and execution parity all pass. Its workflow-boundary checks audit exact planner publication, build and Miri consumers, required-check aggregation, and the complete standalone semver job. |
| [`plan.rs`](../tools/zc/src/plan.rs) | Pure, deterministic ordinary-build, Miri, and semver membership. A plan contains complete selectors and execution meaning, but no command strings, permissions, runner labels, actions, secrets, or publication choices. Semver candidates are derived from the matching ordinary-build slice so reduced-event eligibility cannot drift. |
| [`execution.rs`](../tools/zc/src/execution.rs) | The exact argv vectors and environment for ordinary build and Miri cells, the exact modeled action inputs and environment for semver cells, ordinary target behavior, Miri setup and model flags, and parity with frozen command and logical-work evidence. It executes only a build or Miri selector that resolves uniquely in a newly checked plan; the literal workflow executes semver. At the legacy-evidence boundary, a narrow adapter restores semver's historical `build_test` job label and removes the post-baseline target-specific cache prefix. A separate current-state audit derives every required native build from checked plans, Cargo target kinds, and enabled integration targets, because those corrective operations postdate the immutable baseline. |
| [`github.rs`](../tools/zc/src/github.rs) | Versioned, deterministic transport from one plan explanation to three compact GitHub matrices, two optional-job gates, and a detailed review artifact. It enforces per-matrix and combined UTF-16 job-output limits; it does not carry workflow authority. |
| [`workflow_protocol.rs`](../tools/zc/src/workflow_protocol.rs) | Shared reviewed spellings used at CLI, projection, and workflow boundaries: commands, outputs, jobs, selectors, step and display names, the trusted host shell, and runner/Docker bridges. This private module prevents the Rust implementation and exact source audits from drifting internally; it does not grant workflow authority or choose coverage. |
| [`ci/baselines`](baselines/README.md) | Independent evidence of the behavior that the typed implementation replaced: reduced/full matrix membership, logical and standalone work, and representative commands. These files are expected review data, not planner output. Because they describe one immutable source commit, they intentionally retain rows for historical operations that have since been retired. |
| [Workflow YAML](../.github/workflows/ci.yml) | Events, permissions, runners, concurrency, most third-party action references, Docker and tool setup, artifact transfer, static jobs, and the required-check aggregate. [`workflow-jobs.tsv`](workflow-jobs.tsv) gives every live job a reviewed role, and [`workflow.rs`](../tools/zc/src/workflow.rs) rejects unregistered jobs or unsupported declaration syntax. Behavior-bearing workflow bridges receive separate exact Rust audits in [`planned_adapter`](../tools/zc/src/planned_adapter/mod.rs) and [`semver_adapter.rs`](../tools/zc/src/semver_adapter.rs) rather than being trusted because their jobs are registered. Those audits cover the planner and image producers, build and Miri consumers, exact required-check aggregate, and the complete literal semver job: its header, checkout, preparation step, and action step. The image audit also covers its mutable local actions and isolated Docker context. |
| [`githooks/pre-push`](../githooks/pre-push) and check scripts | Local orchestration and repository-wide checks. The hook bootstraps pinned tools, runs checks concurrently, verifies that every check script is included, and rejects lockfile mutation. In particular, [`check_tools.sh`](check_tools.sh) tests the Rust CI implementation and runs `ci audit`; [`check_actions.sh`](check_actions.sh) validates Actions files and the hook; and [`check_job_dependencies.sh`](check_job_dependencies.sh) protects required-check aggregation. |

## Validation and execution flow

1. `CiInputs::load` resolves the repository root and every fixed input without
   allowing a checked-in symlink to redirect planning outside the checkout.
2. Policy parsing, workflow-job inventory, Cargo inventory, and canonical
   baseline parsing each run before a caller can obtain checked inputs. The
   planned-job audit checks the exact planner and image producers, build and
   Miri consumers, and required-check aggregate. The semver audit checks its
   complete standalone job, including the exact header, checkout, preparation,
   and literal action.
3. The execution model expands representative reduced and full behavior and
   must match the frozen matrix, logical-work, standalone-work, and command
   evidence exactly. This includes modeled semver action inputs for every
   planned target. It separately exact-compares every required native build
   with an expected command derived from checked plans and Cargo inventory.
   `ci audit` also plans every configured event.
4. `Plan` or `PlanExplanation` selects cells for one exact event. Planning is
   pure after input validation.
5. `GitHubProjection` creates three matrix outputs, two optional-job gates, and
   `ci-plan.json` from the same explanation. The workflow expands only compact
   selectors. In particular, each semver matrix cell carries only a target;
   the adapter audits its one policy-owned package, toolchain, profile, and
   static action inputs independently.
6. Before matrix fan-out, the `build_docker_env` audit requires the image
   producer's exact job fields, permissions, output, and five exact steps. It
   compares both mutable local actions, the Dockerfile, and `.dockerignore`
   with independent complete source snapshots. All live and snapshot paths
   must be distinct ordinary files with distinct file identities; symbolic
   links and hard links cannot make a one-sided edit change both copies. The
   `.github/ci-image` build context must contain exactly `Dockerfile` and
   `.dockerignore`, and the latter's only active pattern is `*`. The Dockerfile
   therefore cannot receive other checkout files through `COPY`, `ADD`, a
   context mount, or a future base-image trigger. It does not execute checkout
   code; it directly installs the three commonly used toolchains, whose
   argument defaults must match the validated Cargo inventory. This is a
   repository-source proof against accidental or incomplete changes, not
   cryptographic attestation against a hostile checkout or mutable external
   image content. A coordinated authority change can pass the audit, but must
   make the live source, independent snapshot, and Rust contract visibly change
   together for review.

   Each ordinary build or Miri runner then reloads and revalidates the
   repository, resolves its complete selector against a fresh plan,
   reconstructs typed argv and environment values, and executes that one cell
   in the prebuilt CI image. Before either executor, the workflow audit requires
   the exact pinned checkout, artifact download, image load, and
   checkout-integrity sequence. The repository-owned download action must
   match its independent complete source snapshot. The integrity gate
   reconstructs fresh Git metadata from the expected commit so setup cannot
   hide a changed checkout in its mutable index, config, or attributes. The
   narrow workflow bridge also requires its hosted runner, interpreter, and
   Docker invocation explicitly, clears Bash startup controls, and overrides
   the image entrypoint. The audit rejects an uncoordinated workflow edit to
   the fixed PATH, shell, `runs-on`, Docker command, or image entrypoint. The
   hosted runner and image implementations remain part of the trusted runtime.
   An unknown, excluded, or ambiguous selector fails instead of falling back
   to similar work.
7. Each selected semver target runs in a separate, fresh hosted runner which
   depends only on the planner. The exact audited checkout, preparation step,
   and literal action consume that target. Semver can therefore begin while
   the Docker image and ordinary matrix are still being prepared, and neither
   build setup nor code run by the action can leave state for the other job.
8. The required-check aggregate runs even after failures or skips. It rejects
   cancellation and missing or invalid planner outputs. It requires Miri and
   semver independently to be `skipped` exactly when their corresponding
   planner gate is `false`, and to succeed when its gate is `true`; every other
   dependency must succeed.

The exact event classification is:

- reduced coverage: `pull_request`;
- full coverage: `merge_group`, `push`, and `workflow_dispatch`.

There is no default class for an unknown event. Miri is currently full-only, so
the pull-request Miri matrix is empty and the workflow skips that job before
matrix expansion. Current semver policy selects three target-only cells for a
pull request and all nine target-only cells for a full event. Those cells
inherit reduced-event eligibility from the corresponding ordinary-build
targets; the package, toolchain, and profile remain checked typed semantics
rather than extra matrix axes. The event names must stay coordinated among the
workflow triggers, `[events]` in `ci/zc.toml`, and the independent event-class
list in [`plan.rs`](../tools/zc/src/plan.rs).

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
- Keep the three cache-seeding argument defaults in
  `.github/ci-image/Dockerfile` equal to the validated MSRV, stable, and nightly
  versions. `ci audit` rejects a partial roll. Because the workflow passes no
  mutable toolchain build arguments, these checked defaults are the only
  repository-derived toolchain-version values used while the image installs
  toolchains.
- Add a new descriptor and its package/profile/target scopes in `ci/zc.toml`.
  Every `package.metadata.build-rs` key must have exactly one build-rs policy
  descriptor, every such descriptor must have a manifest key, and every
  descriptor must have nonempty scopes. Build-script descriptors must also
  satisfy the exact metadata text contract parsed by `zerocopy/build.rs`.
- A version or scope change which alters reviewed behavior fails execution or
  baseline parity until its intended effect is independently recorded.

The old `zerocopy/ci/check_all_toolchains_tested.sh` check was intentionally
retired. The typed two-way invariant landed first; the old YAML parser was then
deleted atomically with the switch to generated `fromJSON` matrices. Do not
recreate a parser for those matrix expressions. The frozen baseline still
contains the historical hosted and pre-push operations from its source commit;
removing those rows would weaken replacement-parity evidence, not remove a live
obligation.

### Native build and test coverage

Native ordinary-library cells use one `cargo test` command instead of a
separate build and test only when Cargo inventory reports an integration
target enabled by that cell's feature selection. Cargo then compiles the
ordinary library artifact as an integration-test dependency. If no enabled
integration target exists, the executor automatically retains a separate
build; unit tests alone do not prove the normal library artifact. The root
manifest may not define a test profile or a non-unwind dev panic strategy, and
CI rejects equivalent Cargo configuration, command-line selectors, and
environment overrides. Local execution remains permissive so personal Cargo
configuration still works.

Proc macros are different on the oldest supported Cargo: their test build does
not produce the dev-profile artifact. `zerocopy-derive` also enables `syn`'s
`visit` feature only through a dev-dependency, so its test graph is not its
production graph. `execution.rs` therefore derives a separate native build for
every proc-macro package from Cargo's audited target kind, regardless of its
integration tests. These builds and the ordinary-library fallback were added
after the frozen baseline. A separate current-state audit constructs their
complete expected commands directly from the reduced and full plans and
exact-compares them with the live model; never add them to the immutable legacy
TSVs.

Dev-dependency feature unification is not inherently limited to proc macros.
For every consolidated profile and native target, the `zc` test suite asks
`cargo tree` for its production and test views and requires every shared
package to retain its reported production feature set. Cargo documents these
views as approximations, not exact compilation plans, so this is a smoke test
and review reminder rather than a proof. Multiple feature sets reported for
one package fail as ambiguous instead of being merged. The repository-wide
`check_tools` job owns this centralized check so matrix runners do not repeat
those resolutions. If a dependency change makes the views diverge, retain a
separate native build or deliberately strengthen the check before updating
the reminder. Keep it coordinated with `execution::build_operations` and
`ci/check_tools.sh`; profile guards do not prove dependency-feature
equivalence.

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
  the required result, also add it to `all-jobs-succeed.needs`.
  `check_job_dependencies.sh` owns the complete inventory of those
  dependencies. The Rust aggregate audit independently requires the minimum
  direct typed path from `plan_ci`, `build_test`, `miri`, `semver`, and
  `check-job-dependencies`, while permitting the other dependencies owned by
  the shell audit. A new planned job must additionally be represented by the
  planned-role and exact workflow-bridge audits. New syntax in the deliberately
  narrow `jobs:` or top-level job-declaration forms fails until the scanner is
  reviewed.
- A deliberate change to the image producer, its repository-owned Docker-setup
  or artifact-upload action, the Dockerfile, or `.dockerignore` must update its
  complete snapshot under `tools/zc/testdata` and the exact contract in
  `planned_adapter/image.rs` as applicable. The artifact-download action used
  by consumers has its separate snapshot and exact contract in
  `planned_adapter/matrix.rs`. Job, output, or step-ID spelling changes must
  also move with `workflow_protocol.rs`. This duplication is intentional: a
  one-sided edit must fail before the changed source can feed matrix jobs. Keep
  the Docker context isolated to its two current files unless a reviewed design
  expands that authority boundary; expanding the source set must also update
  the reviewed-source inventory, `.gitattributes` LF rules, and the LF
  invariant in `ci.rs`.
- The aggregate's display name, `All checks succeeded (ci.yml)`, is the status
  check selected by GitHub repository rules. A rename must be coordinated with
  those external rules as well as the workflow and local audits, or GitHub can
  wait forever for the old required check. The source audit also keeps this job
  on `always()`, gives it no permissions, and checks its exact ordered
  cancellation, planner-output, and conclusion steps. Those steps use the
  trusted shell and an absolute `/usr/bin/jq` path so missing planned work
  cannot silently become a successful required check.
- Keep all three limits in `[limits]` coordinated with their Rust validation
  and projection behavior. `max_plan_cells` (currently 4,096) bounds the total
  selected ordinary, Miri, and semver cells before projection.
  `max_matrix_cells` (currently 256) bounds each of the three projected
  matrices independently; the workflow currently has one consumer shard for
  each, so exceeding that limit in any one matrix fails with an instruction to
  add a shard instead of dropping cells. `max_job_output_utf16_bytes`
  (currently 900,000) bounds GitHub's UTF-16 estimate for the five output
  records together. Increasing one limit does not relax either of the others.

After an intentional change to behavior owned by frozen evidence, update the
files under `ci/baselines` using evidence independent of the new planner. Do
not put a post-baseline correction into those immutable records; give it a
separate current-state audit like the required native builds above. Follow
[`ci/baselines/README.md`](baselines/README.md): retain source identity, compare
exact sets rather than only counts, preserve canonical sorting, and review the
logical and command effects. Do not generate expected rows from the code they
are meant to check. Otherwise the same bug could change both the implementation
and its supposed evidence while leaving `ci audit` green.

## Local entry points

Run these commands from the repository root. `cargo.sh` builds the repository
tool with its pinned compiler before routing the `ci` subcommand. The examples
in this section use POSIX shell syntax, including temporary-file setup,
redirection, variables, and line continuations. On Windows, run them from a
POSIX-compatible shell such as Git Bash and replace the
`./zerocopy/cargo.sh` prefix with `./zerocopy/win-cargo.bat`; subcommands and
options are unchanged. An execution selector still names real target work, so
it must be usable on the local host. The execution examples below deliberately
select a Windows target and therefore remain usable after that prefix change.
These are not Command Prompt or PowerShell snippets.

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
  --target x86_64-pc-windows-msvc
```

Execute one exact Miri cell selected by a full event:

```sh
./zerocopy/cargo.sh ci execute-miri-cell \
  --event merge_group \
  --package zerocopy \
  --toolchain nightly \
  --feature-profile default \
  --target x86_64-pc-windows-msvc \
  --miri-model stacked
```

Use `ci plan` to copy a complete selector; the executor requires every field
and will not infer a nearby cell. Choose a selected cell whose target is usable
on the local host; changing only the platform-specific entry point cannot make
a native Linux cell run on Windows. These execution commands run build or test
processes and may install the selected compiler or target through the
repository's Cargo entry point.

For the same validation used by CI, run `./ci/check_tools.sh`. The complete
local gate is `./githooks/pre-push`; it is broader and may take substantially
longer.

## Projection outputs and the literal semver boundary

`github-plan` appends five newline-delimited output records, in one checked
UTF-16 size budget:

- `build_matrix={"include":[...]}` contains package, toolchain,
  feature-profile, and target selectors;
- `miri_matrix={"include":[...]}` adds the Miri model selector;
- `miri_enabled=true` if and only if the Miri matrix is nonempty;
- `semver_matrix={"include":[...]}` contains target selectors only; and
- `semver_enabled=true` if and only if the semver matrix is nonempty.

The workflow uses each optional-job gate twice: once to enable its matrix job,
and again to require that job's result to be `success` when enabled or
`skipped` when disabled. The required-check aggregate also requires all five
records to be present and both gates to be canonical booleans. Keep the output
constants in `workflow_protocol.rs`, the planner job's output mapping, the
three `fromJSON` consumers, both job conditions, and the aggregate audit
coordinated.

The pretty `ci-plan.json` artifact is versioned review evidence. It includes
the policy schema version, event and class, selected/excluded counts for all
three kinds of work, every candidate's typed decision and reason, exact
compiler versions, repository-relative manifest paths, feature semantics,
ordinary execution modes, Miri model flags, and semver targets. It deliberately
contains no permissions, runners, actions, commands, run IDs, timestamps,
absolute paths, or other authority-bearing or nondeterministic fields. The
workflow uploads it for 14 days.

Current policy produces three semver targets for reduced pull-request events
and nine for full events. Each compact semver cell transports only its target.
[`plan.rs`](../tools/zc/src/plan.rs) derives the package, stable toolchain,
stable feature profile, target set, and reduced-event eligibility from checked
policy and the corresponding ordinary-build candidates. The one package,
toolchain, profile, and other static action inputs therefore do not become
handwritten matrix axes which could drift from that plan.

GitHub requires `uses:` to be literal YAML, so the typed executor cannot invoke
the `cargo-semver-checks` action. The `semver` job is the narrow literal action
boundary. It depends only on `plan_ci`, not on Docker image production, so its
three or nine runners can start as soon as planning finishes and continue in
parallel with Docker preparation and the ordinary matrix. A fresh runner also
isolates the jobs in both directions: ordinary build setup cannot alter
semver's checkout or process environment, and repository code compiled by the
semver action cannot leave checkout, file-command, or runner state for an
ordinary build.

[`SemverAdapterSpec`](../tools/zc/src/semver_adapter.rs) derives the expected
static action fields from checked policy, Cargo inventory, and reviewed
constants. The source audit recognizes the complete canonical job header and
exactly three steps: pinned checkout, preparation, and the literal action. It
also requires the job gate and target-only matrix from the typed projection;
the action's `rust-target` input is exactly `matrix.target`.

The preparation audit checks the step's name, ID, order, trusted shell, working
directory, environment, and exact script. It runs for every selected semver
cell, before the action, and cannot be replaced by an extra producer through
`GITHUB_ENV` or `GITHUB_PATH`. Pull requests inspect the exact head SHA; other
events inspect `HEAD`. The step publishes its commit-message run/skip decision
only through the named `prepare_semver.outputs.run` value. The action's only
condition consumes `steps.prepare_semver.outputs.run == 'true'`; the audit
rejects an ambient `ZC_SKIP_CARGO_SEMVER_CHECKS` anywhere in the workflow.

The action audit checks its `uses` revision, environment, inputs, and condition.
Its compiler is an exact literal derived from Cargo's pinned-stable metadata;
package, manifest, and stable feature root come from Cargo inventory and
policy; target membership and waivers come from policy. The action's automatic
baseline-rustdoc cache key does not include the Rust target, so `prefix-key`
uses that same typed target to keep concurrent matrix cells out of one cache.
Expected values are unquoted YAML scalars, so the adapter accepts only a
conservative canonical scalar grammar and an exact three-component Rust
version. Supporting a broader spelling requires reviewed quoting and parsing
support before changing the YAML.

Frozen evidence predates both the separate semver job and its target-specific
cache prefix. It therefore names `build_test` as the operation's source and has
no `prefix-key` action input. `execution.rs` first constructs and validates the
complete live operation, then restores only those two historical differences
immediately before legacy comparison. Every historical selector, action input,
environment value, condition, step, and occurrence count remains subject to
exact parity. Keep this narrow normalization at the evidence boundary; do not
teach the live plan or workflow audit to accept the historical job layout or
an unpartitioned cache.

Keep `ci/zc.toml`, `zerocopy/Cargo.toml`, `plan.rs`, `github.rs`,
`SemverAdapterSpec`, the complete literal workflow job,
`workflow_protocol::TRUSTED_SHELL`, and the execution command
goldens/constants coordinated. An action revision, feature group, warning
flag, cache prefix, selector, skip rule, compiler, matrix, or job-boundary
change fails the exact audits until all affected owners are updated
deliberately.

## Local execution platform

Canonical typed commands and frozen baselines retain the public `./cargo.sh`
spelling. At the real host boundary, Windows translates only that exact program
to the equivalent `./win-cargo.bat` entry point while preserving argument,
environment, and working-directory boundaries. Unrelated programs such as
`cargo` and `nproc` are not translated. This lets ordinary and Miri Cargo
wrapper invocations cross the Unix/Windows boundary without duplicating every
planned command.

GitHub matrix execution remains Ubuntu/Docker. Linux Miri execution additionally
requires GNU `nproc` on `PATH`; its one-line output is strictly parsed and
checked before doubling, and missing or invalid output fails explicitly.
Windows and other non-Linux hosts instead use
`std::thread::available_parallelism`; query, zero, and overflow failures are
reported explicitly. Every host still requires compatible tools and targets.

Miri execution does not move or edit `zerocopy/.cargo/config.toml`. For the
exact nightly Miri command, the executor adds
`--manifest-path zerocopy/Cargo.toml` and a private root context.
`cargo-zerocopy` validates and consumes that context, runs Cargo and package-ID
children from the repository root so they do not discover the crate-local
configuration, preserves the historical target directory, and strips the
private value from child environments. The aarch64 workaround still runs
`cargo clean` before Miri; do not run that cell concurrently with commands
which share its Cargo target directory.

## Temporary Anneal v1 matrix

The [`verify_examples`](../.github/workflows/anneal.yml) job in `anneal.yml`
intentionally keeps an explicit matrix list for Anneal v1 examples. Anneal v1
is being replaced, so this temporary adapter is not part of the typed
ordinary-CI planner and is not an inventory of every file under
`anneal/v1/examples`.

When adding or removing a covered example, edit the matrix list. If temporary
v1 support requires an expected-failing example, also keep the step's inline
`KNOWN_FAILING` list coordinated. That mechanism deliberately distinguishes
only the command's exit status; do not build a new discovery or diagnostic
classification layer merely to perfect this short-lived matrix.
