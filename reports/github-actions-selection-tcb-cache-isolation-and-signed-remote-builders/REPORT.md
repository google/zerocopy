# GitHub Actions Selection TCB, Cache Isolation, and Signed Nix Remote Builders

## Summary

- **Selection TCB cannot rely on `pull_request` workflows alone:** `on: pull_request` loads `.github/workflows/*.yml` from `refs/pull/<n>/merge`, allowing an untrusted PR to edit the workflow, bypass a base-ref checkout, or spoof a required check. Pinning a reusable workflow by SHA inside a PR-editable caller workflow does not close this hole.
- **GitHub Rulesets Required Workflows are strictly Enterprise-only and org/enterprise-scoped:** Unlike general repository rulesets (which are available on GitHub Free for public repositories), the *"Require workflows to pass before merging"* (`workflows`) rule is gated to GitHub Enterprise Cloud (`ghec`) and GitHub Enterprise Server (`ghes >= 3.12`; enterprise-level configuration `ghes >= 3.18`), configured only at the organization or enterprise level, ignores all event filters, and requires an explicit `merge_group` trigger to avoid stalling merge queues.
- **GitHub Actions Cache cannot compose PR caches into `merge_group`, and `merge_group` writes thrash the 10 GB cap:** `actions/cache` enforces a default 10 GB per-repository cap, 7-day unused eviction, and LRU replacement. Writes on `pull_request` are isolated to `refs/pull/<n>/merge`, while `merge_group` runs on `refs/heads/gh-readonly-queue/<base_branch>/pr-<prNumber>-<base_sha>` and cannot write to `refs/heads/main`. Leaving `actions/cache` in default write mode during `merge_group` writes unreachable ephemeral-ref entries that evict warm `main` caches unless `cache-mode: read` or `actions/cache/restore` is used.
- **GitHub Merge Queue fast-forwards `main` to the exact `merge_group` commit SHA and tree (`HEAD^{tree}`):** Across merge-commit and squash-and-merge queues (single PR and multi-PR batches, verified live), GitHub creates the final commit(s) on `gh-readonly-queue/...` and fast-forwards `<base_branch>` to `head_sha`, yielding identical commit SHA and `HEAD^{tree}` between `merge_group` and `push` to `main` (and 100% derivation reuse on external signed Nix caches, vs. 0% on `actions/cache`). Queue entry requires write/maintain/admin access (blocking external fork authors), while plan-based concurrent-job limits (Free 20 / Pro 40 / Team 60 / GHEC 500 standard; macOS 5/50 shared across standard + larger) apply identically to public and private repos.
- **Dynamic matrices require a fixed-name aggregator gate job:** GitHub Actions caps matrices at 256 jobs per workflow run and job outputs at 1 MB per job (50 MB per run). Because Required Status Checks match exact check-run names and workflow-level skips stay permanently `Pending`, dynamic matrices require a single fixed-name aggregator gate job (`if: always()`).
- **Nix `.narinfo` Ed25519 signatures sign full sorted reference paths, and CA paths bypass signature checks:** Nix signs `1;<StorePath>;<Nix32-NarHash>;<NarSize>;<comma-sorted-full-store-path-References>` (using full `/nix/store/...` paths even though `.narinfo` `References:` stores space-separated basenames). Content-addressed (CA) store paths bypass signature checks (`isContentAddressed()` returns `maxSigs`), whereas input-addressed (IA) derivations require a trusted key under `require-sigs = true`.
- **Magic Nix Cache bypasses Nix signature verification via `?trusted=1`:** It appends a local daemon substituter with `?trusted=1` to `nix.conf` (requiring the runner user to be in `trusted-users`), relying entirely on GitHub Actions Cache scoping rather than Ed25519 signatures.
- **Default Linux Nix sandboxing is not an adversarial security boundary:** Because Nix builds share the host Linux kernel (with an allow-by-default seccomp filter and optional `/dev/kvm` bind-mount), untrusted-PR remote builders require hardware virtualization (Firecracker, Cloud Hypervisor, or ephemeral cloud VMs) with Ed25519 signing keys kept strictly outside the build VM and immutable/write-once cache policies.

## Applicability

This report characterizes the interaction among four groups of subjects listed in `REPORT.json`:

1. **GitHub Actions & Rulesets control plane** (`github/docs@d7487f5debb5a5a2a6e65e6f9fa539266f5f8db6`, `github/rest-api-description@c9c95fe34ced05fe076001f5c55704742bc8e7f8`): Applies to repositories using GitHub Actions (`pull_request`, `pull_request_target`, `merge_group`, `push`), `actions/cache`, dynamic `strategy.matrix` planning, Required Status Checks, Merge Queues, and GitHub Rulesets. Plan-gated ruleset behavior distinguishes GitHub Free / Pro / Team from GitHub Enterprise Cloud (`ghec`) and GitHub Enterprise Server (`ghes`).
2. **Nix store verification and Linux sandboxing** (`NixOS/nix@3705f35ddcdca8d777c1d75b939eb6a3a4ac9ebb` inspected in source; `Determinate Nix 3.17.0` / `Nix 2.33.3` on `x86_64-linux` executed in empirical probes): Applies to Nix binary cache `.narinfo` signing/verification (`require-sigs = true`, default) and Linux sandboxed derivation builds (`sandbox = true`). Behavior on non-Linux hosts (macOS Seatbelt, Windows) is out of scope here.
3. **Nix binary cache backends** (`DeterminateSystems/magic-nix-cache@12fb09b6126680552ebf1918102d65d832554057`, `DeterminateSystems/magic-nix-cache-action@8941f279e15828abcd2fc8fbb7cd282ab00972a7`, `zhaofengli/attic@7a19204df10d606c5070e6bb72615c3461900c05`, `cachix/cachix@8231a10ca573fc5cbdd844d2a2802d6c7765f288`, plus raw S3/GCS/R2 `s3://` stores): Compared for cryptographic trust, fork-PR write isolation, retention limits, and cross-PR to `merge_group` reuse.
4. **Untrusted-PR remote builder isolation tiers** (`firecracker-microvm/firecracker@58cf1b2cdca407f2323d1b0b25ebb95dfe5b4bcb`, `cloud-hypervisor/cloud-hypervisor@8d5dd53b7ce7ff49249496cdb29a144b3ef2e19c`, `google/gvisor@9d60518521ac1fd54989ec0482570cd18c70d885`, and ephemeral cloud VMs): Compared as execution boundaries for adversarial fork PRs building Nix derivations (especially compile-heavy Rust/Cargo/LLVM workloads).

All architectural comparisons synthesize these subjects together; specific source-level invariants apply to the exact pinned revisions above and should be re-checked across major upstream releases.

## Findings

### 1. GitHub Actions Event Semantics, Cache Isolation, and Dynamic Matrix Limits

#### 1.1 Workflow Source, Refs, and Secret Boundaries by Event

Basis: documentation

- **`pull_request`:** Loads `.github/workflows/*.yml` from the PR's synthetic merge commit (`refs/pull/<prNumber>/merge`), setting `GITHUB_REF=refs/pull/<prNumber>/merge` and `GITHUB_SHA` to that merge commit. For pull requests from **public forks**, GitHub restricts `GITHUB_TOKEN` to **read-only** and withholds all **repository secrets** (other than `GITHUB_TOKEN`). Same-repository PRs receive normal configured permissions and secrets.
- **`pull_request_target`:** Loads `.github/workflows/*.yml` from the **target (base) branch**, setting `GITHUB_REF` to the base branch ref (e.g., `refs/heads/main`) and `GITHUB_SHA` to the latest commit on the base branch. Runs with **access to repository secrets** and a **read/write `GITHUB_TOKEN`** even for fork PRs.
- **`merge_group`:** Triggered (default activity type `checks_requested`) when a PR enters a GitHub Merge Queue on a temporary read-only branch created inside the base repository. Live runner logs and Actions Cache API responses establish that `GITHUB_REF` is **`refs/heads/gh-readonly-queue/<base_branch>/pr-<prNumber>-<base_sha>`** (not `refs/merge-group/...`) and `GITHUB_SHA` is the merge-group commit (`head_sha`) combining the current queue tip and the queued PR. Because `merge_group` executes on a base-repository branch rather than a forked `pull_request` event, workflows receive full repository/organization secrets, non-downgraded `GITHUB_TOKEN` permissions (`workflow-syntax.md:366`), and `id-token: write` OIDC minting (default `sub`: `repo:<owner>/<repo>:ref:refs/heads/gh-readonly-queue/<base_branch>/pr-<n>-<base_sha>`, or immutable `OWNER@ID/REPO@ID` format for repos created after July 15, 2026), even when the queued PR originated from a public fork.
  - **Environment protection & `File.fnmatch` pitfall:** Environment deployment rules match `GITHUB_REF` using Ruby `File.fnmatch` where `*` does **not** cross `/` (`deployments-and-environments.md:62`). Consequently, *"Protected branches only"* blocks `merge_group`, and *"Selected branches and tags"* requires `gh-readonly-queue/main/*` (not `gh-readonly-queue/*`). Environments with manual required reviewers stall `merge_group` until timeout.
  - **Queue entry & auto-merge preconditions:** Merge queues are available on org-owned public repos, org-owned private repos on GHEC, and org-owned repos on GHES (`merge-queue.md:1-5`). Enqueueing a PR (`Merge when ready`, `gh pr merge`, or `enqueuePullRequest`) requires **write/maintain/admin** access (`merge-queue-overview.md:7`); external fork authors cannot enqueue or arm auto-merge. All branch-protection/ruleset requirements must pass before queue entry. Clicking *Merge when ready* before requirements pass arms auto-merge even when repository-level *"Allow auto-merge"* is disabled (`merging-a-pull-request-with-a-merge-queue.md:43`); auto-merge is automatically disabled if a user *without* write permissions pushes commits or changes the base branch (`automatically-merging-a-pull-request.md:25`), but remains armed on pushes by write users unless stale-review dismissal blocks re-entry. Enqueueing an unreviewed fork PR therefore remains a secret-exfiltration vector unless required reviews + stale-review dismissal are enforced.
- **`push`:** Loads workflow YAML from the pushed commit (`GITHUB_SHA`) on `GITHUB_REF=refs/heads/<branch>` or `refs/tags/<tag>`, with full configured permissions and repository secrets.

#### 1.2 GitHub Actions Cache (`actions/cache`) Limits and Isolation

Basis: documentation + derived

- **Storage quota and eviction:** Default combined storage cap is **10 GB per repository** (expandable on paid plans). Cache entries unused for **more than 7 days** are automatically deleted regardless of total usage. When the cap is reached, GitHub evicts entries via **Least Recently Used (LRU)**.
- **Branch and fork scoping:** Workflow runs may restore caches created on the current branch, the base branch (for PRs), or the default branch. Caches written during a `pull_request` run are scoped to `refs/pull/<prNumber>/merge`; they are readable only by subsequent runs of that same PR and **cannot** overwrite or pollute caches on the default branch, base branch, or sibling PRs.
- **No compositional `merge_group` reuse and unreachable-write cache thrashing (documentation + execution + derived):**
  - `merge_group` runs on ephemeral `refs/heads/gh-readonly-queue/<base_branch>/pr-<n>-<base_sha>`. It can restore caches from the default branch (`refs/heads/main`), **cannot** read caches written in `refs/pull/<n>/merge`, and **cannot** write to `refs/heads/main` (both because writes target the run's own `GITHUB_REF` and because `dependency-caching.md:264-283` restricts default-branch cache writes to 7 triggers excluding `merge_group`).
  - **Cache-thrashing trap (live execution on `google/zerocopy`):** Because `merge_group` runs on its own ephemeral ref, GitHub Actions defaults it to `Cache mode: write`. Every `actions/cache` save writes entries scoped to `refs/heads/gh-readonly-queue/...` that **no future run can ever read** (neither `push` to `main`, nor the next sibling `merge_group` entry, nor `pull_request`), burning the 10 GB repository cap and accelerating LRU eviction of warm `refs/heads/main` caches. Setting `cache-mode: read` (`dependency-caching.md:287-318`) or using `actions/cache/restore` on `merge_group` prevents this waste.

#### 1.2a Merge Queue Commit/Tree Identity (`HEAD^{tree}`) and Post-Merge Cache Reuse

Basis: documentation (`managing-a-merge-queue.md`, `pull-request-merges.md`) + execution (live GitHub API probes across `google/zerocopy`, `bytecodealliance/wasmtime`, `rust-lang/cargo`, `rust-lang/rust-analyzer`, `NixOS/nix`) + derived

| Merge Queue Strategy | Temporary `merge_group` Commit Construction | Resulting `<base_branch>` Update | Commit SHA Identical? (`head_sha` == landed `main`) | Tree SHA Identical? (`HEAD^{tree}`) | Basis |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Merge commit** | 2-parent merge commit `[queue_tip, pr_head]` on `gh-readonly-queue/...` | Fast-forwards `<base_branch>` to `head_sha` | **Yes** | **Yes** | execution + documentation |
| **Squash and merge** (single PR) | 1-parent squash commit on `queue_tip` | Fast-forwards `<base_branch>` to `head_sha` | **Yes** | **Yes** | execution + documentation |
| **Squash and merge** (multi-PR batch) | Chained 1-parent squash commits `base` ← `squash(PR1)` ← `squash(PR2)` (each queued PR still runs its own `merge_group` check) | Atomically fast-forwards `<base_branch>` to final group commit | **Yes** (each PR's `merge_commit_sha` == its `merge_group` `head_sha`) | **Yes** | execution + documentation |
| **Rebase and merge** | Server-side rebases PR commits onto `queue_tip` (new SHAs vs. `pr.head.sha`) | Fast-forwards `<base_branch>` to rebased `head_sha` | **Yes** (relative to `merge_group` `head_sha`) | **Yes** | documentation + derived |

- **Post-merge `push` to `main` reuse:** With `actions/cache` or Magic Nix Cache, reuse from `merge_group` to `push` to `main` is **0%** (ephemeral ref isolation). With an external signed Nix binary cache (Attic, Cachix, S3), reuse is **100%**—both for pure tree-addressed derivations (which hash source NARs, not commit metadata) and even for derivations injecting `self.rev`/`self.lastModified`, because GitHub fast-forwards `main` to `merge_group`'s exact `head_sha`. Tree-keyed (`HEAD^{tree}`) or derivation-addressed keys strictly dominate `github.sha` keys whenever queue jumps or dequeues force GitHub to recreate downstream `gh-readonly-queue` commits with new commit SHAs/timestamps. (`.gitattributes` `ident` / `$Id$` expands to the Git blob SHA and stays tree-invariant; `export-subst` runs only on `git archive`.)

#### 1.2b Documented GitHub Actions Concurrent-Job Limits Across Plans

Basis: documentation (`github/docs@d7487f5debb5a5a2a6e65e6f9fa539266f5f8db6`: `limits.md:31-77`, `github-hosted-runners.md:53-77`, `larger-runners.md:76-81`, `supported-github-runners.md:1-186`, `getting-started-with-github-actions-for-github-enterprise-server.md:32-48`)

| Runner Type | GitHub Plan | Total Concurrent Jobs (All OSes) | Max Concurrent macOS Jobs | Max Concurrent GPU Jobs |
| :--- | :--- | ---: | ---: | ---: |
| **Standard GitHub-hosted** | **Free** | **20** | **5** | N/A |
| **Standard GitHub-hosted** | **Pro** | **40** | **5** | N/A |
| **Standard GitHub-hosted** | **Team** | **60** | **5** | N/A |
| **Standard GitHub-hosted** | **Enterprise (GHEC)** | **500** | **50** | N/A |
| **Larger runner** | **Team** | **1,000** | **5** (shared with standard) | **100** |
| **Larger runner** | **Enterprise (GHEC)** | **1,000** | **50** (shared with standard) | **100** |

- **Public vs. private repositories:** Concurrency caps are **strictly plan-based** (identical for public and private repos) and apply at the account/org/enterprise level; excess jobs queue. Public repositories differ only in receiving unlimited free standard compute minutes and double standard Linux/Windows specs (**4 vCPU / 16 GB RAM / 14 GB SSD** vs. **2 vCPU / 8 GB RAM / 14 GB SSD** on private repos; macOS specs are identical).
- **OS pools, timeouts, and merge-queue interaction:** Linux (`x64`, `arm64`, `ubuntu-slim`) and Windows (`x64`, `arm64`) share the Total pool (`ubuntu-slim` has a 15-min timeout vs. 6 h for standard/larger runners); macOS is capped at 5 (Free/Pro/Team) or 50 (GHEC) **shared across standard and larger runners**. Setting merge-queue `build_concurrency > 1` multiplies matrix demand across simultaneous `merge_group` runs and can saturate the 20/60-job or 5-macOS cap, causing spurious merge-queue status-check timeouts.
- **Self-hosted runners & GHES:** GHES does not support GitHub-hosted runners. Self-hosted runners have no plan-based concurrency cap (limits: 10,000 runners/group, 1,500 registrations/5 min, 5-day job timeout with 24-hour `GITHUB_TOKEN` refresh cap, 24-hour queue timeout). GHES documents instance-sized **Maximum Connected Runners**: `8 vCPU/64 GB → 740`, `32 vCPU/160 GB → 2,700`, `96 vCPU/384 GB → 7,000`.

#### 1.3 Dynamic Matrix Limits and Required Status Checks Gate-Job Invariant

Basis: documentation + derived

- **256-job matrix cap:** `strategy.matrix` (including dynamic `fromJSON(...)` matrices) can generate at most **256 jobs per workflow run** on both GitHub-hosted and self-hosted runners.
- **Job output limits (`GITHUB_OUTPUT` / `jobs.<id>.outputs`):** Maximum **1 MB per job** and **50 MB combined per workflow run** (measured approximately in UTF-16), bounding the serialized JSON matrix payload a planner job can emit.
- **Workflow-level vs. job-level skips:**
  - **Workflow-level skips** (`paths`, `paths-ignore`, `branches`, or commit-message skip filters) prevent the workflow from starting; any Required Status Check belonging to that workflow remains permanently **Pending** and blocks merging.
  - **Job-level skips** (`if:` on a job inside a running workflow) report a `skipped` conclusion, which GitHub treats as **satisfying** a Required Status Check.
- **Mandatory fixed-name aggregator/gate job (derived):** Dynamic matrix legs produce check names such as `check (linux-x86_64-msrv)`. Because Required Status Checks match exact check-run names and do not understand dynamic matrix expansion, requiring an individual matrix leg hangs PRs where the planner omits that leg, while omitting dynamic legs leaves them unrequired. A single fixed-name **aggregator/gate job** (`needs: [plan, run-matrix]`, `if: always()`) that inspects `needs.plan.result` and `needs.run-matrix.result`—failing on `failure` or `cancelled`, and permitting `skipped` only when the planner explicitly emitted an empty matrix—must be the sole required check.
- **Exceeding 256 checks (derived):** When a Nix check graph exceeds 256 legs (e.g., cross-products of toolchains, features, and targets), grouping fine-grained Nix check derivations into coarse runner shards (e.g., 8–32 shards, each invoking `nix build` over a batch of derivations) avoids both the 256-job cap and the 1 MB `GITHUB_OUTPUT` limit while preserving derivation-level caching.

---

### 2. Preventing Candidate PRs from Weakening the Selection TCB

#### 2.1 Why PR-Editable Workflows Cannot Protect the Selection TCB

Basis: documentation + derived

- **Checking out `base` inside `pull_request` fails:** Because `on: pull_request` parses `.github/workflows/*.yml` from `refs/pull/<n>/merge`, an untrusted PR can edit the workflow YAML to remove the base-ref checkout, replace the gate job with `exit 0`, or drop matrix legs. Required Status Checks verify only that a check run with the expected name reported `success`, not that the workflow originated from the base branch.
- **SHA-pinned reusable workflows called from PR workflows fail:** Pinning `uses: org/repo/.github/workflows/ci.yml@<40-hex-sha>` protects against upstream drift of the *callee*, not against a PR editing the *caller* `.github/workflows/*.yml` to remove or alter the `uses:` call. Reusable workflows become part of a tamper-proof Selection TCB only when invoked directly by a Ruleset Required Workflow rather than a PR-editable caller.

#### 2.2 GitHub Rulesets — "Require workflows to pass before merging" (`workflows` Rule)

Basis: normative (OpenAPI schema) + source (`github/docs`) + documentation

- **Strictly Enterprise-only (do not conflate with general rulesets):** General repository rulesets are available on GitHub Free (user/org) for public repositories, and on Pro, Team, and GitHub Enterprise Cloud (`ghec`) for public and private repositories. By contrast, the *"Require workflows to pass before merging"* (`workflows`) rule is feature-flag gated by `repo-rules-required-workflows` strictly to **`ghec: '*'`** and **`ghes: '>=3.12'`**. It is **not** available on GitHub Free, Pro, or Team plans—even for public repositories.
- **Organization / Enterprise level only:** Ruleset workflows can be configured only at the **organization** or **enterprise** level (enterprise-level configuration is gated to `ghec: '*'` and `ghes: '>= 3.18'` via `enterprise-ruleset-workflow-rule`). Standalone repository-level rulesets do not expose the `workflows` rule.
- **Source-repository visibility and access:** The required workflow file must live in `.github/workflows` of a source repository whose visibility is equal to or less restrictive than the target repositories (`public` → any org repo; `internal` → internal and private; `private` → private only), and internal/private source repositories must enable Actions access from organization repositories.
- **Pinned workflow resolution:** In the GHEC REST API schema (`repository-rule-workflows`), `parameters.workflows[]` items (`repository-rule-params-workflow-file-reference`) take required `repository_id` (integer) and `path` (string), optional `ref` (branch or tag) and `sha` (commit SHA), and optional `do_not_enforce_on_create` (boolean). Workflow YAML is therefore resolved from the configured source repository + `ref`/`sha`, independent of the PR head commit.
- **Supported triggers and ignored filters:** Only `pull_request` (`opened`, `synchronize`, `reopened`), `pull_request_target` (`opened`, `synchronize`, `reopened`), and `merge_group` (`checks_requested`) are supported. **All event filters (`branches`, `branches-ignore`, `paths`, `paths-ignore`, `types`, etc.) are ignored**; the workflow always triggers on the default activity types of the listed events.
- **Fork PR semantics:** Branch and tag rulesets are not inherited by external forks (only push rulesets propagate to fork networks). For PRs opened from forks targeting a protected branch, the workflow definition is loaded from the ruleset's pinned source repo/`ref`/`sha`, while runtime `GITHUB_TOKEN` and secret permissions follow the workflow's declared trigger (`pull_request` vs. `pull_request_target`).
- **Explicit `merge_group` opt-in:** In repositories with a merge queue, required workflows do **not** run on merge queue batches unless the workflow YAML explicitly lists `merge_group` under `on:`. Omitting `merge_group` causes queue checks to never run and merges to stall.
- **Operational constraints and limits:**
  - Blocks direct pushes to targeted branches (avoid targeting all branches; optionally set `do_not_enforce_on_create` so branch/repo initialization is not blocked).
  - Does not trigger on events generated by `GITHUB_TOKEN`, and does not retroactively run on already-open PRs when the rule is added.
  - Must **not** use `cancel-in-progress` concurrency.
  - Cannot invoke CodeQL actions (`github/codeql-action/init`, `analyze`) except `github/codeql-action/upload-sarif`.
  - GitHub documents up to **75 rulesets per repository** and **75 organization-wide rulesets**, with no separate documented `maxItems` limit on the `workflows[]` array inside a single `workflows` rule.

#### 2.3 `pull_request_target` Coordinator and External GitHub App Alternatives

Basis: documentation + derived

- **`pull_request_target` Coordinator + Untrusted Worker / Remote Builder:**
  - Loads workflow YAML strictly from the base branch, preventing PR tampering with the coordinator.
  - **`pwn-request` attack vectors:**
    1. Checking out PR head (`ref: ${{ github.event.pull_request.head.sha }}`) and executing any PR-controlled code—including `nix eval` with Import From Derivation (IFD), Nix plugins, or custom builtins, `build.rs`, proc-macros, `Makefile`, `cargo metadata` with untrusted `.cargo/config.toml` or `rust-toolchain.toml`, or test scripts—inside the privileged runner enables immediate secret exfiltration and write-`GITHUB_TOKEN` abuse.
    2. Shell/script injection via untrusted PR metadata (`github.event.pull_request.title`, `body`, `head.ref`) interpolated directly via `${{ ... }}` into `run:` scripts instead of passed through `env:`.
    3. `workflow_run` artifact poisoning if a privileged `workflow_run` downloads untrusted `pull_request` artifacts and executes them or unpacks tarballs with path traversal or symlinks.
  - **Required safety invariants:**
    1. Hold **zero secrets** and minimal `GITHUB_TOKEN` permissions (`contents: read` plus `statuses: write` or `checks: write` only, or dispatch to an isolated remote builder using a scoped non-admin token).
    2. **Never execute PR code** on the privileged runner: either run a base-ref diff planner (using `git diff`/`git show` with safe config, avoiding hooks and `.gitattributes` smudge filters) evaluating only base-ref Nix expressions or restricted pure-eval (`--option allow-import-from-derivation false --option allow-unsafe-native-code-during-evaluation false --option restrict-eval true`), or offload PR evaluation and realization to an isolated untrusted-PR remote builder holding zero repo secrets and zero cache signing keys.
- **External GitHub App / Remote Control Plane:**
  - Receives signed `pull_request` and `merge_group` webhooks off-PR, computes required checks from base-ref policy and PR diff, dispatches isolated remote builds, and posts Check Runs / Commit Statuses via a GitHub App installation token.
  - Rulesets and branch protection can pin Required Status Checks to that specific GitHub App's integration ID, preventing check spoofing by PR-editable workflows.

#### 2.4 Selection TCB Architecture Comparison

Basis: normative + source + documentation + derived

| Architecture | Tamper-Proof Against PR Editing `.github/workflows/`? | Fork PR Secret Exposure Risk | Works with `merge_group`? | Plan / Operational Prerequisites | Key Trade-off |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`pull_request` checking out `base`** | **No** (YAML loaded from PR merge commit) | None (fork PRs receive no secrets) | Yes | Built-in (all plans) | **Broken TCB**: PR can edit workflow to bypass planner or spoof green check. |
| **SHA-pinned reusable workflow called from PR workflow** | **No** (PR can edit caller workflow) | None | Yes | Built-in (all plans) | Protects against callee drift only, not caller tampering. |
| **Rulesets: *"Require workflows to pass before merging"*** (`workflows` rule) | **Yes** (ruleset invokes pinned `repository_id` + `path` + `ref`/`sha` off-PR) | Low when trigger is `pull_request` (no fork secrets); high if `pull_request_target` is misused | Yes, **only** if workflow explicitly declares `merge_group` | **Strictly GitHub Enterprise Cloud (`ghec`) or GHES ≥ 3.12**; **org/enterprise-level rulesets only** (unavailable on Free/Pro/Team or standalone repo rulesets) | Cleanest native GitHub TCB where Enterprise org rulesets are available; ignores event filters and forbids `cancel-in-progress`. |
| **`pull_request_target` Coordinator + Untrusted Worker / Remote Builder** | **Yes** (YAML loaded from base branch) | **High if misconfigured** (`pwn-request` if any PR code or unsafe metadata runs in coordinator) | Requires separate `merge_group` trigger/workflow | Built-in (all plans) | Available on all plans, but demands strict discipline: zero secrets on planner and zero PR code execution on coordinator. |
| **External GitHub App / Remote Control Plane** | **Yes** (webhook evaluated off-PR; Check Run pinned to App integration ID) | **Minimal** (secrets stay in control plane, never on untrusted runners) | Yes (native `merge_group` webhook) | Must host and operate external webhook service + GitHub App | Strongest TCB across all plans and pairs naturally with untrusted-PR remote builders; highest operational footprint. |

---

### 3. Nix Binary Cache Signing, Trust Models, and Backends

#### 3.1 Exact `.narinfo` Format and Ed25519 Fingerprint Specification

Basis: source + execution

- A `.narinfo` document consists of newline-delimited `Key: Value` headers (`StorePath`, `URL`, `Compression`, `FileHash`, `FileSize`, `NarHash`, `NarSize`, `References`, optional `Deriver`, optional `CA`, and zero or more `Sig: <key-name>:<base64-ed25519-sig>` lines).
- In `NixOS/nix@3705f35ddcdca8d777c1d75b939eb6a3a4ac9ebb`, `ValidPathInfo::fingerprint()` (`src/libstore/path-info.cc:50-57`) constructs the exact UTF-8 byte string signed by Ed25519 as:
  ```text
  1;<StorePath>;<Nix32-NarHash>;<NarSize>;<comma-sorted-full-store-path-References>
  ```
- **Critical serialization difference:** Although the `.narinfo` `References:` header stores **space-separated basenames** (e.g., `qvrk...-probe-ref-a.txt xy5v...-probe-ref-b.txt`), the signed fingerprint uses **comma-separated, lexicographically sorted full store paths** (e.g., `/nix/store/qvrk...-probe-ref-a.txt,/nix/store/xy5v...-probe-ref-b.txt`) and `NarHash` encoded in **Nix base32** with prefix (`sha256:...`, not SRI).
- **Excluded transport metadata:** `Deriver`, `URL`, `Compression`, `FileHash`, and `FileSize` are **not** included in the fingerprint; caches and proxies may recompress NARs without invalidating signatures.
- **Content-Addressed (CA) vs. Input-Addressed (IA) signature enforcement:** In `ValidPathInfo::checkSignatures()` (`src/libstore/path-info.cc:126-136`), if `isContentAddressed(store)` is true, Nix immediately returns `maxSigs` because the store path is cryptographically bound to the content hash and verified against the NAR. For standard **input-addressed (IA)** derivations (`Deriver: ...drv`, no `CA:`), `require-sigs = true` (default) requires at least one valid Ed25519 signature matching `trusted-public-keys`.
- **Empirical confirmation (`Determinate Nix 3.17.0` / `Nix 2.33.3` on `x86_64-linux`):**
  - *CA path with two references:* Independent Python `cryptography` `Ed25519PublicKey.verify()` succeeded on the full-path comma-sorted fingerprint and failed with `InvalidSignature` on basename-only references. `nix store verify --sigs-needed 1 --option trusted-public-keys ""` exited `0` on the CA path (`CA: text:sha256:...`), confirming `isContentAddressed()` bypasses signature checks.
  - *IA derivation:* `nix store verify --sigs-needed 1` exited `0` with the signing key in `trusted-public-keys`, and exited `2` (`path '/nix/store/26z3kx8ig6j2srqyq2a0r2iwrhzz20w6-probe-ia-drv' is untrusted`) when `trusted-public-keys` was empty.

#### 3.2 Binary Cache Backend Trust Models

Basis: source + documentation + derived

- **Magic Nix Cache (`DeterminateSystems/magic-nix-cache@12fb09b6126680552ebf1918102d65d832554057`, `magic-nix-cache-action@8941f279e15828abcd2fc8fbb7cd282ab00972a7`):**
  - Does **not** sign `.narinfo` files with Ed25519. Instead, `magic-nix-cache/src/main.rs:438` appends `extra-substituters = http://127.0.0.1:37515?trusted=1&compression=zstd&parallel-compression=true&priority=1` to `~/.config/nix/nix.conf`.
  - `?trusted=1` instructs Nix to **bypass signature verification** for paths served by the local daemon from GitHub Actions Cache, which requires the runner user to be listed in Nix's `trusted-users` (checked in `magic-nix-cache-action/src/index.ts:136`; hardened runners that remove the CI user from `trusted-users` silently disable Magic Nix Cache).
  - Fork-to-`main` isolation depends entirely on GitHub Actions Cache scoping (`refs/pull/<n>/merge`), requiring zero secrets (`id-token: write` is only for optional FlakeHub Cache, `src/helpers.ts:63`). It inherits GHA Cache's 10 GB cap, 7-day eviction, lack of external developer/builder consumption, and lack of cross-PR to `merge_group` reuse.
- **Attic (`zhaofengli/attic@7a19204df10d606c5070e6bb72615c3461900c05`):**
  - Self-hostable multi-tenant binary cache backed by S3-compatible object storage (S3, R2, MinIO, GCS S3-compat) and PostgreSQL/SQLite.
  - Performs server-side **FastCDC content-defined chunking** (`server/src/api/v1/upload_path.rs:259-343`) for global cross-cache deduplication, authenticates uploads via cache-scoped **JWTs** (`permission.require_push()`), and signs `.narinfo` server-side so object-store credentials and signing keys never touch CI runners.
  - Supports separate logical caches (e.g., `trusted-main` and `pr-scratch`) sharing one deduplicated chunk store.
- **Cachix (`cachix/cachix@8231a10ca573fc5cbdd844d2a2802d6c7765f288`):**
  - Separates API authorization (`CACHIX_AUTH_TOKEN`) from cryptographic verification (`trusted-public-keys`), supporting server-managed signing (default) or client-side self-signing. Any holder of a write-enabled token can push arbitrary store paths, so write tokens must not be exposed to untrusted fork PRs.
- **Raw S3 / GCS / R2 (`s3://` / `https://`):**
  - Direct upload via `nix copy --to s3://...?secret-key=...` requires exposing both bucket write credentials and the Ed25519 private signing key to the uploader unless mediated by an upload proxy.

| Backend | Cryptographic Signing (`require-sigs`) | Fork PR Write Safety | Storage / Retention Limits | Cross-PR → `merge_group` Reuse? | External Dev / Remote Builder Consumption? |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Magic Nix Cache (GHA Cache)** | **None** (`?trusted=1` bypasses sig checks; requires `trusted-users`) | Safe via GHA Cache PR scoping (zero secrets) | **10 GB/repo** default; **7-day** unused eviction; LRU | **No** (PR caches isolated in `refs/pull/<n>/merge`) | **No** (GHA-only) |
| **Cachix** | Ed25519 (server-managed default or self-signed) | **Unsafe** if write token exposed to fork PRs; safe via trusted builder / `main` pushes | Plan-dependent storage + LRU GC | **Yes** (if populated by trusted remote builder or `main`) | **Yes** |
| **Attic (Self-Hosted)** | Ed25519 server-side signing + cache-scoped JWT | **Safe** with separate logical caches (`trusted` vs. `pr`) + FastCDC shared dedup | Bucket-bound (S3/R2/GCS); configurable GC | **Yes** (with cross-cache chunk deduplication) | **Yes** |
| **Raw S3 / GCS / R2** | Client-side Ed25519 (`?secret-key=...`) | **Unsafe** on untrusted runners (needs bucket write creds + private key) | Bucket-bound | **Yes** (from trusted builders only) | **Yes** |

---

### 4. Untrusted-PR Remote Builders, Isolation Tiers, and Out-of-VM Signing

#### 4.1 Limits of the Default Linux Nix Sandbox

Basis: source + documentation

- In `NixOS/nix@3705f35ddcdca8d777c1d75b939eb6a3a4ac9ebb`, `src/libstore/linux/build/linux-derivation-builder.cc:596-600` isolates Linux builds via `clone()` with `CLONE_NEWPID | CLONE_NEWNS | CLONE_NEWIPC | CLONE_NEWUTS | CLONE_NEWNET` (plus `CLONE_NEWUSER` when unprivileged and `CLONE_NEWCGROUP` when cgroups are enabled), `pivot_root`, `NO_NEW_PRIVS`, and an **allow-by-default** seccomp-BPF filter (`seccomp_init(SCMP_ACT_ALLOW)` at line 90, blocking only selected xattr/setuid-class operations). When `kvm` is present in `system-features`, `/dev/kvm` is bind-mounted into the sandbox (lines 776-778).
- **Not an adversarial security boundary:** All builds share the **host Linux kernel**, so any kernel LPE (`io_uring`, netfilter, KVM, etc.) escapes to host root and compromises `nix-daemon`, signing keys, and `/nix/store`. `nix-daemon` runs as `root` and dispatches builds under a fixed pool of `nixbld*` UIDs, where impure derivations or network-enabled Fixed-Output Derivations (FODs) can also leak or smuggle state if build-user pools or temporary directories are not scrubbed.

#### 4.2 Strong Isolation Tiers

Basis: documentation + derived

| Isolation Tier | Security Boundary | Kernel Isolation? | Requires `/dev/kvm`? | Compile Overhead (Rust/Nix) | Signing Key Placement |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Default Linux Nix Sandbox** (`unshare` + `pivot_root` + allow-default seccomp) | Hermeticity / build purity **only** (not adversarial security) | **No** (shared host kernel; `/dev/kvm` exposed if enabled) | No | Baseline (near-zero) | **Unsafe** on same host as untrusted builds |
| **gVisor (`runsc`)** | User-space application kernel (Sentry) | Partial (emulated syscall surface) | No | **High** (heavy syscall/VFS churn on `rustc`/`lld`/`cargo`) | Outside container on trusted host |
| **Firecracker / Cloud Hypervisor MicroVM** | Hardware virtualization (KVM) + dedicated guest kernel (+ Firecracker `jailer`) | **Yes** | Yes (bare-metal or nested KVM) | **Low** (near-native CPU; ~0.1–2s snapshot boot) | **Strictly outside microVM** on host control plane |
| **Ephemeral Per-Job Cloud VMs** | Cloud hypervisor + clean VM teardown per job | **Yes** | No (provider-managed) | **Low** (native CPU; ~20–60s cold boot) | **Strictly outside VM** (trusted signer / Attic server after build attestation) |

#### 4.3 Out-of-VM Signing, Trust Laundering Prevention, and Compositional `merge_group` Reuse

Basis: derived (from Nix input-addressing and out-of-VM signing boundaries)

- **Signing-key placement invariant:** The Ed25519 cache signing key must **never** reside inside an untrusted build VM or sandbox.
- **Trusted host signer and namespace separation:** The host control plane outside the microVM collects realized store paths from the ephemeral VM, verifies that they resulted from a pure sandboxed realization of the requested derivation, and signs them under either:
  - a **`pr-untrusted` key/namespace** (for PR-modified derivations—consumable by PRs or developers who opt in, never trusted by release builds unless rebuilt or content-addressed), or
  - a **`trusted-ci` key/namespace** only when the `.drv` hash matches a trusted/base-equivalent derivation (e.g., toolchains, dependencies, unmodified crates) or after `merge_group`/`main` realization.
- **Mitigating non-determinism and trust laundering:** For pure input-addressed derivations, modifying any input changes the `.drv` hash and output store path. However, if a derivation is non-deterministic and a PR build is allowed to overwrite an already-cached output for an unmodified `.drv` built on `main`, a PR could poison a shared store path. Mitigation requires **immutable / write-once cache semantics** (never overwrite an existing store path) and refusing to sign PR-built FODs or pre-existing store paths under the `main` signing key.
- **Compositional `merge_group(A+B)` reuse:** Because Nix derivations are input-addressed by the transitive closure of their inputs, when PR A modifies check `X` and PR B modifies check `Y`, every check derivation in `merge_group(A+B)` whose inputs are unchanged relative to `main`, PR A, or PR B has the identical `.drv` and output store path. When a trusted isolated remote builder signs pure realized outputs outside the microVM into a shared remote cache (Attic, Cachix, or S3), `merge_group(A+B)` substitutes unaffected derivations directly rather than rebuilding A+B from scratch.

## Boundaries

- **GitHub Enterprise org-policy availability on any specific repository (`not examined`):** Whether a particular organization has GitHub Enterprise Cloud enabled, permits org-level `workflows` rulesets, or enables Actions access across internal/private workflow repositories is repository- and org-configuration-dependent and was not audited against any live org.
- **Exact numeric cap on `workflows[]` entries per Ruleset (`unknown`):** Neither `github/docs@d7487f5debb5a5a2a6e65e6f9fa539266f5f8db6` (`available-rules-for-rulesets.md`, `troubleshooting-rules.md`) nor `github/rest-api-description@c9c95fe34ced05fe076001f5c55704742bc8e7f8` (`descriptions/ghec/ghec.yaml:134300-134306`, no `maxItems`) documents a numeric maximum on the number of workflows inside a single `workflows` rule (distinct from the documented 75-ruleset limit).
- **Rulesets `workflows` rule on GitHub Free / Pro / Team or standalone repository rulesets (`unsupported`):** Primary-source feature flags (`repo-rules-required-workflows.yml`) and docs explicitly restrict the `workflows` rule to `ghec` and `ghes >= 3.12` at organization/enterprise scope; general repository ruleset availability on Free/Pro/Team is **known not to apply** to the `workflows` rule.
- **Non-Linux Nix sandboxing (`not examined` here):** Linux `clone()`/`pivot_root`/seccomp findings are **known not to apply** to macOS (Seatbelt `sandbox_init_with_parameters`) or Windows (no sandbox).
- **Stability of `ca-derivations` for Rust/Cargo CI (`not examined`):** Empirical Probe 1 verified only Nix's signature-bypass behavior for CA store paths (`builtins.toFile`), not end-to-end stability or early-cutoff behavior of experimental `ca-derivations` on Rust/Cargo builds.
- **Quantitative Rust/Nix compile latency benchmarks across Firecracker, Cloud Hypervisor, and gVisor (`not examined`):** Overhead characterizations in Section 4.2 are qualitative (`documentation` + `derived`), not measured wall-clock benchmarks on these pinned VMM commits.
- **Live execution probe for `Rebase and merge` merge queues (`not examined`):** Live GitHub API commit-object equality (`merge_group` `head_sha` == landed `main` SHA and identical `HEAD^{tree}`) was empirically verified for `Squash and merge` (single PR and multi-PR batch) and `Merge commit` queues; `Rebase and merge` fast-forward equivalence is derived from GitHub documentation and commit mechanics without a live rebase-only repository probe.
- **Stronger conclusions not established:** Out-of-VM signing of PR-built derivations does *not* make arbitrary PR-authored build outputs trustworthy for release signing; it attests only that a trusted isolated builder realized that specific `.drv`, and remains vulnerable to non-deterministic output collisions unless write-once cache semantics and namespace separation are enforced.

## Evidence

All evidence was gathered or executed on `2026-11-21`.

### 1. GitHub Actions & Rulesets Primary Sources

- **GitHub Docs (`github/docs@d7487f5debb5a5a2a6e65e6f9fa539266f5f8db6`):**
  - `data/features/repo-rules-required-workflows.yml` (L1–5): gates `workflows` rule to `ghec: '*'` and `ghes: '>=3.12'`.
  - `data/features/enterprise-ruleset-workflow-rule.yml` (L1–5): gates enterprise-level workflow rulesets to `ghec: '*'` and `ghes: '>= 3.18'`.
  - `data/reusables/gated-features/repo-rules.md` (L1–3): general repository ruleset plan availability (Free public, Pro/Team/GHEC public+private).
  - `data/reusables/repositories/rulest-workflows-intro-paragraph.md` (L1): org/enterprise-level scope of ruleset workflows.
  - `data/reusables/repositories/ruleset-workflow-event-triggers.md` (L1–9): supported events (`pull_request`, `pull_request_target`, `merge_group`) and ignored event filters.
  - `data/reusables/actions/merge-group-event-with-required-checks.md` (L1): explicit `merge_group` opt-in requirement.
  - `content/repositories/configuring-branches-and-merges-in-your-repository/managing-rulesets/available-rules-for-rulesets.md` (L279–316): source-repo visibility rules, direct-push blocking, operational constraints.
  - `content/repositories/configuring-branches-and-merges-in-your-repository/managing-rulesets/troubleshooting-rules.md` (L49–122): fork PR permissions (L63), source-repo Actions access (L91, L100–108), `merge_group` stall behavior (L96–98), `cancel-in-progress` prohibition (L118–120).
  - `content/repositories/configuring-branches-and-merges-in-your-repository/managing-rulesets/about-rulesets.md` (L17–25): 75 repo / 75 org ruleset caps.
  - `content/organizations/managing-organization-settings/creating-rulesets-for-repositories-in-your-organization.md` (L16–22): branch/tag rulesets not inherited by external forks.
  - `content/actions/reference/workflows-and-actions/events-that-trigger-workflows.md` (L436–438), `workflow-syntax.md` (L366), `dependency-caching.md` (L240–318), `deployments-and-environments.md` (L26, L50–65, L108), `content/actions/reference/security/secrets.md` (L29–41), `oidc.md` (L27–29, L89–96, L123–182), `content/actions/reference/limits.md` (L31–77), `github-hosted-runners.md` (L53–77), `larger-runners.md` (L76–81), `data/reusables/actions/supported-github-runners.md` (L1–186), `data/reusables/gated-features/merge-queue.md` (L1–5), `data/reusables/pull_requests/merge-queue-overview.md` (L7), `content/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue.md` (L26, L57–129), `merging-a-pull-request-with-a-merge-queue.md` (L43, L53–55), `automatically-merging-a-pull-request.md` (L23–37): exact `merge_group` trust/cache/queue-entry semantics and concurrent-job limits.
- **Live GitHub API & Runner-Log Probes (`2026-11-21`):**
  - `google/zerocopy` `merge_group` run `44848919560` (job `136675357822`) & `GET /repos/google/zerocopy/actions/caches`: confirmed `GITHUB_REF=refs/heads/gh-readonly-queue/main/pr-4019-3e9bdb5def4bc91fb1b14d6475285820675677df`, `Cache mode: write`, 9 `semver-*` cache entries written to that ephemeral ref before `push` to `main` rewrote them to `refs/heads/main`.
  - Squash-and-merge commit/tree SHA equality: `google/zerocopy` PR `#4019` (`385a099849b344812c00f8e6054e106005ff0e2b`, tree `95451d1d9e67b2e5f434506db747251cfba44256`) and multi-PR atomic batch PR `#4010` + `#3997` (`15498e0a70a535ecdeffbcb5be006f09d7026446` -> `88a13ae26ef3fe4623daf37347cfe0d7dea41698`, merged `2026-11-21T01:18:27Z`); `bytecodealliance/wasmtime` PR `#15401`.
  - Merge-commit SHA/tree equality: `rust-lang/cargo` PR `#17782` (`be13e5e9129a6ba5208ccfa5e2b36bb7f06837a3`, tree `cc55910b7df8bc4a5cf003534dee309288530760`), `rust-lang/rust-analyzer` PR `#22211` (`a9a08a23cbf507eb8ceeb2d7443b67fd7a25ddbb`), `NixOS/nix` PR `#16853` (`3705f35ddcdca8d777c1d75b939eb6a3a4ac9ebb`, tree `0161481cb18cc157ed97be6feec32d715583cf25`).
- **GitHub REST API OpenAPI Schema (`github/rest-api-description@c9c95fe34ced05fe076001f5c55704742bc8e7f8`):**
  - `descriptions/ghec/ghec.yaml` (L134261–134306): `repository-rule-workflows` and `repository-rule-params-workflow-file-reference` schema (`repository_id`, `path`, optional `ref`, `sha`, `do_not_enforce_on_create`; no `maxItems`).
- **Canonical GitHub Docs & Security Lab Pages (verified `200 OK` on `2026-11-21`):**
  - Events: `https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows`
  - Dependency caching: `https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching`
  - Limits: `https://docs.github.com/en/actions/reference/limits`
  - Merge queue: `https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue`
  - Required status checks: `https://docs.github.com/en/pull-requests/how-tos/merge-and-close-pull-requests/troubleshooting-required-status-checks`
  - GitHub Security Lab (*Preventing pwn requests*): `https://securitylab.github.com/resources/github-actions-preventing-pwn-requests/`

### 2. Nix, Binary Cache, and Isolation Source References

- **`NixOS/nix@3705f35ddcdca8d777c1d75b939eb6a3a4ac9ebb`:**
  - `src/libstore/path-info.cc` (L50–57): `ValidPathInfo::fingerprint()` format (`1;<StorePath>;<NarHash>;<NarSize>;<comma-sorted-full-store-path-References>`).
  - `src/libstore/path-info.cc` (L126–136): `ValidPathInfo::checkSignatures()` returning `maxSigs` when `isContentAddressed(store)` is true.
  - `src/libstore/nar-info.cc` (L83–87, L133–136): `.narinfo` `References:` space-separated basename serialization/parsing.
  - `src/libstore/linux/build/linux-derivation-builder.cc` (L90–176, L596–600, L776–778, L913–933): allow-default seccomp (`SCMP_ACT_ALLOW`), `clone()` namespaces, `/dev/kvm` bind-mount when `kvm` in `system-features`, `pivot_root` and `NO_NEW_PRIVS`.
- **`DeterminateSystems/magic-nix-cache@12fb09b6126680552ebf1918102d65d832554057`:**
  - `magic-nix-cache/src/main.rs` (L438): appends `extra-substituters = http://127.0.0.1:37515?trusted=1&compression=zstd&parallel-compression=true&priority=1`.
  - `magic-nix-cache/src/binary_cache.rs` (L17–30): unsigned `.narinfo` serving path.
- **`DeterminateSystems/magic-nix-cache-action@8941f279e15828abcd2fc8fbb7cd282ab00972a7`:**
  - `src/index.ts` (L136): `trusted-users` prerequisite check.
  - `src/helpers.ts` (L61–63): `id-token: write` used only for optional FlakeHub Cache.
- **`zhaofengli/attic@7a19204df10d606c5070e6bb72615c3461900c05`:**
  - `server/src/api/v1/upload_path.rs` (L259–343): server-side FastCDC chunking, `permission.require_push()` JWT check, and server-side signing.
- **`cachix/cachix@8231a10ca573fc5cbdd844d2a2802d6c7765f288`**, **`firecracker-microvm/firecracker@58cf1b2cdca407f2323d1b0b25ebb95dfe5b4bcb`**, **`cloud-hypervisor/cloud-hypervisor@8d5dd53b7ce7ff49249496cdb29a144b3ef2e19c`**, **`google/gvisor@9d60518521ac1fd54989ec0482570cd18c70d885`**: pinned default-branch HEADs verified on `2026-11-21` for architectural capability characterization.

### 3. Empirical Execution Probes (`Determinate Nix 3.17.0` / `Nix 2.33.3`, `x86_64-linux`)

- **Probe 1 (`.narinfo` Ed25519 fingerprint and CA bypass):**
  - Generated ephemeral keypair (`nix key generate-secret --key-name probe-test-1` / `nix key convert-secret-to-public`), created `probe-main.txt` referencing `probe-ref-a.txt` and `probe-ref-b.txt` via `builtins.toFile`, exported with `nix copy --to file://<tmp-cache>?secret-key=<sec>`, and inspected `pppnm3i25rk5ga5vbrp154vmfi6dbb6c.narinfo`:
    ```text
    StorePath: /nix/store/pppnm3i25rk5ga5vbrp154vmfi6dbb6c-probe-main.txt
    NarHash: sha256:0w34fy7867l6wzqnl3y9z315vqp355y97d78q3f1j9bdv6nrnlqa
    NarSize: 248
    References: qvrkrrrhb3yj3iy7gvdq02cpls4qn3dq-probe-ref-a.txt xy5v7iv1fvrxbgbnfdw81zk1ld44jqbc-probe-ref-b.txt
    Sig: probe-test-1:4NE2H79Z6qYx7FrcZWlFeStSazngrtVvOB6GDcCksoq2EvbcHDNupwhngbfbTEoJKjqQhbivqgDxNuHkVNJCCg==
    CA: text:sha256:0lm6ph0wimik6ib4572j8f372b1d6gaba83j78625py7v712w58a
    ```
  - Python `cryptography` `Ed25519PublicKey.verify()` output:
    - **Pass** on `1;/nix/store/pppnm3i25rk5ga5vbrp154vmfi6dbb6c-probe-main.txt;sha256:0w34fy7867l6wzqnl3y9z315vqp355y97d78q3f1j9bdv6nrnlqa;248;/nix/store/qvrkrrrhb3yj3iy7gvdq02cpls4qn3dq-probe-ref-a.txt,/nix/store/xy5v7iv1fvrxbgbnfdw81zk1ld44jqbc-probe-ref-b.txt`.
    - **Fail (`InvalidSignature`)** on basename-only references (`qvrkrrrhb3yj3iy7gvdq02cpls4qn3dq-probe-ref-a.txt,xy5v7iv1fvrxbgbnfdw81zk1ld44jqbc-probe-ref-b.txt`).
  - `nix store verify --sigs-needed 1 --option trusted-public-keys ""` exited `0` on this CA path.
- **Probe 2 (Input-Addressed derivation trust enforcement):**
  - Built minimal input-addressed derivation `probe-ia-drv.drv` producing `/nix/store/26z3kx8ig6j2srqyq2a0r2iwrhzz20w6-probe-ia-drv` (`Deriver:` present, no `CA:`), signed with `probe-ia-1` into a temporary `file://` cache.
  - `nix store verify --sigs-needed 1 --option trusted-public-keys <probe-ia-1-pub>` exited `0`.
  - `nix store verify --sigs-needed 1 --option trusted-public-keys ""` exited `2` with `path '/nix/store/26z3kx8ig6j2srqyq2a0r2iwrhzz20w6-probe-ia-drv' is untrusted`.

## Revalidation

1. **GitHub Rulesets `workflows` plan gating and schema:** Diff `data/features/repo-rules-required-workflows.yml`, `data/reusables/repositories/ruleset-workflow-event-triggers.md`, and `data/reusables/actions/merge-group-event-with-required-checks.md` in `github/docs` against `d7487f5debb5a5a2a6e65e6f9fa539266f5f8db6`, and check `repository-rule-workflows` in `github/rest-api-description` `descriptions/ghec/ghec.yaml` (and whether it appears in `descriptions/fpt/fpt.yaml` for Free/Pro/Team).
2. **GitHub Actions limits and cache scoping:** Re-check the canonical GitHub Docs pages for *Limits* (256-job matrix cap, 1 MB / 50 MB outputs, plan-based concurrency table) and *Dependency caching* (10 GB cap, 7-day retention, `refs/pull/<n>/merge` vs. `refs/heads/gh-readonly-queue/...` scoping and `cache-mode: read`).
3. **Nix `.narinfo` fingerprint and CA/IA verification:** Re-run Probes 1 and 2 on a target Nix version using an ephemeral directory (`/tmp/...`) with `nix key generate-secret`, `nix copy --to file://...?secret-key=...`, Python `Ed25519PublicKey.verify()`, and `nix store verify --sigs-needed 1 --option trusted-public-keys ""`, or diff `src/libstore/path-info.cc` (`ValidPathInfo::fingerprint`, `ValidPathInfo::checkSignatures`) in `NixOS/nix`.
4. **Magic Nix Cache `?trusted=1` behavior:** Inspect `extra-substituters` construction in `DeterminateSystems/magic-nix-cache` (`magic-nix-cache/src/main.rs`) and `trusted-users` enforcement in `DeterminateSystems/magic-nix-cache-action` (`src/index.ts`).
5. **Linux Nix sandbox isolation:** Diff `src/libstore/linux/build/linux-derivation-builder.cc` in `NixOS/nix` for `clone()` flags, `seccomp_init`, and `/dev/kvm` bind-mounting.
