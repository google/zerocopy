# GHerrit Multi-Remote Ancestry Resolution and GraphQL Batch Mutation Idempotency on Large Pull Request Stacks

## Summary

Synchronizing stacked pull requests through `joshlf/gherrit` (`0.1.0-alpha`,
inspected across commits `147340c2041654cba8cfc57a3e5c3115b4902ec3`,
`86179afb27feabd50ddd7d2dc2493892885db8ba`, and
`2dbcbb6174ac3cf75dd7fcd0ab15cb27027b405d`) exhibits two independent failure
mechanisms when developers push large commit stacks or work across multiple Git
remotes:

1. **Unqualified local base-branch lookup in `collect_commits`:** Although
   `Repo::default_remote_name` (`src/util/repository.rs:72-78`) honors
   `gherrit.remote` (defaulting to `"origin"`) and `Repo::find_default_branches`
   (`src/util/repository.rs:87-125`) resolves the default branch name from
   `refs/remotes/{remote_name}/HEAD`, `collect_commits`
   (`src/pre_push/mod.rs:146-162`) resolves the stack's base commit Oid by
   looking up `refs/heads/{default_branch}` (`refs/heads/main`) instead of
   `refs/remotes/{remote_name}/{default_branch}`. In multi-remote workflows (for
   example, when an `origin` remote tracks a primary upstream repository and a
   secondary remote configured via `gherrit.remote` hosts stacked pull
   requests), any divergence between local `refs/heads/main` and
   `refs/remotes/{remote}/main` breaks stack collection in two ways:
   - **False non-ancestor rejection:** When local `refs/heads/main` advances
     past or diverges from the stack base $B$ while `refs/remotes/{remote}/main`
     still points to $B$, `repo.commits_between(base, head)` checks
     `merge_base(refs/heads/main, HEAD) == refs/heads/main`, fails with
     `CommitsBetweenError::NotAncestor`, and aborts `gherrit pre-push` with
     `Failed to collect commits: The branch '<branch>' is not based on 'main'`.
   - **Extra ancestor commits swept into the pull request stack:** When the
     resolved base ref lags behind the intended stack base $B$ at an older
     ancestor $A < B$, `commits_between(A, HEAD)` walks the entire range
     $(A..\text{HEAD}]$ and collects the $(A..B]$ ancestor commits into the
     pushed pull request stack (or, if `refs/heads/main` is at $B$ while the
     target remote's `main` branch remains at $A$, pushes the bottom pull
     request with base `"main"` against remote commit $A$ until the remote's
     `main` branch is fast-forwarded to $B$).
2. **Non-idempotent GraphQL batch-halving retry after partial
   `createPullRequest` execution:** In `src/pre_push/batching.rs:5-93` and
   `src/pre_push/mod.rs:397-557, 635-786`, `sync_prs` classifies all $N$ pushed
   commits once at startup into `PrResolution::Existing` (`UpdatePullRequest`)
   and `PrResolution::ToCreate` (`CreatePullRequest`) via `batch_fetch_prs`. It
   then packs up to `INITIAL_GRAPHQL_BATCH_LEN = 64` mutations into a single
   aliased GraphQL mutation request (`mutation { op0: createPullRequest(...)
   op1: createPullRequest(...) ... }`). Per Section 6.2.1 (*Serial Execution*)
   of the GraphQL Specification, the server executes top-level mutation fields
   serially in document order without cross-field transactional rollback. When a
   49-commit stack of new pull requests is submitted in a single 49-field
   `createPullRequest` mutation, GitHub's GraphQL server commits the first
   $K \approx 16$ pull requests on the server before exhausting its per-request
   mutation resource budget (`RESOURCE_LIMITS_EXCEEDED`). In-process recovery
   then fails along both server response shapes:
   - **Partial `data` + `RESOURCE_LIMITS_EXCEEDED`:** When GitHub returns the
     committed prefix `data: { op0: {...}, ..., op15: {...}, op16: null, ... }`
     alongside `errors: [{ extensions: { code: "RESOURCE_LIMITS_EXCEEDED" } }]`,
     `classify_response` (`src/pre_push/batching.rs:64-93`) requires
     `has_no_data = response.get("data").is_none_or(Value::is_null)` to return
     `ResponseDisposition::RetryLimit`. Because `data` is a non-null JSON
     object, `classify_response` classifies the response as
     `ResponseDisposition::Fatal` and aborts immediately without retrying.
   - **`data: null` + `RESOURCE_LIMITS_EXCEEDED`:** When the response triggers
     `ResponseDisposition::RetryLimit`, `BatchPlan::reject`
     (`src/pre_push/batching.rs:40-53`) halves the batch window from `0..49` to
     `0..24` (`49 -> 24 -> 12 -> 6 -> 3 -> 1`) without advancing `self.cursor`
     past the 16 pull requests already created on the server and without
     re-querying open pull requests. The first retry slice `0..24` re-sends
     `createPullRequest` for `op0..op15`, and GitHub immediately rejects `op0`
     with `GraphQL error: A pull request already exists for
     <owner>:gherrit/<change-id>` (`UNPROCESSABLE`, classified as `Fatal`).
   - **Why a shell-level `git push` retry loop succeeds in 3 passes (`0 -> 16 ->
     32 -> 49`):** Each fresh `git push` starts a new `gherrit pre-push`
     process that runs `batch_fetch_prs` (`repository.pullRequests(headRefName:
     ...)`) at startup. That startup query discovers the 16 pull requests
     created during the previous failed invocation and reclassifies them from
     `PrResolution::ToCreate` (`createPullRequest`) into
     `PrResolution::Existing` (`updatePullRequest`), shrinking the remaining
     `to_create` queue from $49 \to 33 \to 17 \to 1 \to 0$ across three passes
     (or four passes when $K = 16$ and the final pass creates the 49th pull
     request).

We reproduce both mechanisms in self-contained probes under `support/`
([`reproduce_multi_remote_ancestry.py`](support/reproduce_multi_remote_ancestry.py)
and
[`simulate_graphql_batch_retry.py`](support/simulate_graphql_batch_retry.py))
and provide a verified Rust patch
([`gherrit-fixes.patch`](support/gherrit-fixes.patch)) against `joshlf/gherrit`
commit `2dbcbb6174ac3cf75dd7fcd0ab15cb27027b405d` (`cargo test --lib`: 92
passed, 0 failed) that resolves `refs/remotes/{remote}/{default_branch}`
consistently, caps initial `CreatePullRequest` batches to
`INITIAL_CREATE_PR_BATCH_LEN = 12`, advances `BatchPlan` past committed partial
prefixes via `decode_partial_batch_prefix` and `BatchPlan::reject_after`, and
reconciles server state via `batch_fetch_prs` when a `CreatePullRequest` batch
fails without usable `data`.

## Applicability

These findings apply to:

- **`joshlf/gherrit` (`0.1.0-alpha`):** Specifically the pre-push hook workflow
  (`gherrit pre-push`), repository remote and default-branch resolution, and
  batched GraphQL synchronization across three inspected revisions:
  - `2dbcbb6174ac3cf75dd7fcd0ab15cb27027b405d` (current `refs/heads/main` tip:
    `src/util/repository.rs`, `src/pre_push/mod.rs`, `src/pre_push/batching.rs`,
    `src/pre_push/github.rs`, `src/pre_push/autosquash.rs`);
  - `86179afb27feabd50ddd7d2dc2493892885db8ba` (Cargo-installed revision:
    `src/util.rs`, `src/pre_push/mod.rs`, `src/pre_push/batching.rs`,
    `src/pre_push/github.rs`);
  - `147340c2041654cba8cfc57a3e5c3115b4902ec3` (earlier single-file
    `src/pre_push.rs` and `src/util.rs` baseline prior to GraphQL batching).
- **Git (`git-push` and `githooks(5)`):** Any local Git working tree configured
  with `gherrit` hooks (`core.hooksPath`) and one or more remotes (`origin` plus
  an optional secondary remote selected via `git config gherrit.remote
  <remote>`).
- **GitHub GraphQL API v4 (`POST /graphql`):** Specifically aliased multi-field
  `Mutation.createPullRequest` and `Mutation.updatePullRequest` requests,
  GraphQL serial mutation execution (GraphQL Specification, October 2021
  Edition, Section 6.2.1), and GitHub's GraphQL resource and rate limits
  (`RESOURCE_LIMITS_EXCEEDED`, `RATE_LIMITED`, HTTP 502/504).

## Findings

### 1. Multi-remote base-branch resolution vs. local `refs/heads/main` ancestry mismatch in `collect_commits`

Basis: source + execution.

#### Source mechanism across `joshlf/gherrit` revisions

In `joshlf/gherrit` at commit `2dbcbb6174ac3cf75dd7fcd0ab15cb27027b405d` (and
identically in `src/util.rs:178-231` at commit
`86179afb27feabd50ddd7d2dc2493892885db8ba`), `Repo` resolves the target remote
and default branch in `src/util/repository.rs:72-125`:

```rust
pub fn default_remote_name(&self) -> Result<String,eyre::Error> {
    Ok(self
        .config_snapshot()
        .string("gherrit.remote")
        .map(|s| s.to_string())
        .unwrap_or_else(|| "origin".to_string()))
}

pub fn find_default_branches(&self, remote_name: &str) -> Result<Vec<String>, eyre::Error> {
    let mut branches = Vec::new();
    let remote_head_ref = format!("refs/remotes/{}/HEAD", remote_name);
    if let Ok(mut reference) = self.find_reference(&remote_head_ref)
        && let Ok(resolved) = reference.peel_to_id()
        && let Some(target_name) = reference.target().try_name()
    {
        let prefix = format!("refs/remotes/{}/", remote_name);
        let target_str = target_name.to_string();
        if let Some(branch) = target_str.strip_prefix(&prefix) {
            let _ = resolved;
            branches.push(branch.to_string());
        }
    }
    // Falls back to init.defaultBranch, refs/heads/{main,master,trunk}, then "main".
```

Notice that `find_default_branches` strips the `refs/remotes/{remote_name}/`
prefix and returns an unqualified branch name such as `"main"`. When
`gherrit pre-push` runs (`src/pre_push/mod.rs:341-376`), `run_for_branch` calls
`repo.find_default_branch_on_default_remote()` (`src/pre_push/mod.rs:351`) and
passes that unqualified `default_branch` string (`"main"`) into
`collect_commits(&repo, &default_branch, local_oid, &branch_name)`
(`src/pre_push/mod.rs:373`).

Inside `collect_commits` (`src/pre_push/mod.rs:146-162` at `2dbcbb6174ac`,
`src/pre_push/mod.rs:127-142` at `86179afb27fe`), however, `gherrit` hardcodes
`refs/heads/{default_branch}` instead of resolving the remote-tracking ref on
the configured remote:

```rust
fn collect_commits<'a>(
    repo: &'a Repo,
    default_branch: &str,
    head: Oid,
    branch_name: &str,
) -> Result<Vec<Commit<'a>>, eyre::Error> {
    let base = repo.rev_parse_single(format!("refs/heads/{}", default_branch).as_str())?;
    let oids = repo.commits_between(base, head).map_err(|e| match e {
        CommitsBetweenError::NotAncestor => {
            eyre!("The branch '{}' is not based on '{}'", branch_name, default_branch)
        }
        CommitsBetweenError::Other(err) => err,
    })?;
```

In the earlier commit `147340c2041654cba8cfc57a3e5c3115b4902ec3`
(`src/pre_push.rs:70`), `collect_commits` similarly called
`repo.rev_parse_single(&*default_branch)?`, which `gix` resolves to
`refs/heads/main` before `refs/remotes/<remote>/main`. By contrast,
`PendingAutosquash` (`src/pre_push/autosquash.rs:15-26` at `2dbcbb6174ac`)
explicitly pairs `(remote, default_branch)` to suggest
`git rebase -i --autosquash {remote}/{default_branch}`, confirming that the
intended stack base is the target remote's default branch rather than the local
`refs/heads/main` branch.

Subsequently, `repo.commits_between(ancestor, descendant)`
(`src/util/repository.rs:168-194`) verifies strict linear ancestry via
`self.merge_base(ancestor, descendant)`:

```rust
match self.merge_base(ancestor, descendant) {
    Ok(mb) if mb == ancestor => {}
    Ok(_) | Err(_) => return Err(CommitsBetweenError::NotAncestor),
}
```

#### Two concrete failure modes in multi-remote repositories

Consider a repository with an `origin` remote and a secondary remote `secondary`
configured via `git config gherrit.remote secondary`, where a 3-commit stack
$S_1 \to S_2 \to S_3$ (`HEAD` $= S_3$) is rooted at stack base commit $B$:

| Scenario | Local `refs/heads/main` | Remote `refs/remotes/secondary/main` | Unpatched `collect_commits` (`refs/heads/main`) | Patched `collect_commits` (`refs/remotes/secondary/main`) |
| :--- | :--- | :--- | :--- | :--- |
| **Failure Mode 1:** Local `main` advanced ($B \to U_1 \to U_2$) while `secondary/main` $= B$ | $U_2$ (`3c0f8ef3...`) | $B$ (`4275b5df...`) | **Fails:** `merge_base(U_2, S_3) = B != U_2` $\implies$ `Failed to collect commits: The branch 'feature-stack' is not based on 'main'` | **Succeeds:** collects exact 3 stack commits $[S_1, S_2, S_3]$ |
| **Failure Mode 2a:** Resolved base ref lags at ancestor $A < B$ ($A \to E_1 \to B$) | $A$ (`684fc6a0...`) | $B$ (`4275b5df...`) | **Over-collects:** walks $(A..S_3]$ and sweeps extra ancestor commits $[E_1, B, S_1, S_2, S_3]$ (5 commits) into the PR stack | **Succeeds:** walks $(B..S_3]$ and collects exact 3 stack commits $[S_1, S_2, S_3]$ |
| **Failure Mode 2b:** Both local `main` and `secondary/main` lag at $A < B$ until `secondary/main` is fast-forwarded to $B$ | $A$ (`684fc6a0...`) | $A$ (`684fc6a0...`) before fast-forward; $B$ (`4275b5df...`) after `git push secondary B:refs/heads/main` | Sweeps 5 commits $[E_1, B, S_1, S_2, S_3]$ unless local `refs/heads/main` is also mutated | After fast-forwarding `secondary/main` to $B$, collects exact 3 stack commits $[S_1, S_2, S_3]$ without touching local `refs/heads/main` |

Our self-contained Git reproducer
([`support/reproduce_multi_remote_ancestry.py`](support/reproduce_multi_remote_ancestry.py),
recorded output in
[`support/multi_remote_ancestry_results.json`](support/multi_remote_ancestry_results.json))
constructs this exact commit DAG ($A \to E_1 \to B$, upstream branch
$B \to U_1 \to U_2$, and feature stack $B \to S_1 \to S_2 \to S_3$) and verifies
all three cases against Git `2.53.0.473.g4a7958ca14-goog`.

---

### 2. GitHub GraphQL batch `createPullRequest` resource limits and non-idempotent batch-halving retry on 49-commit stacks

Basis: source + specification + execution.

#### How `gherrit` batches GraphQL mutations and halves batch sizes

At `2dbcbb6174ac3cf75dd7fcd0ab15cb27027b405d` and
`86179afb27feabd50ddd7d2dc2493892885db8ba`, `sync_prs`
(`src/pre_push/mod.rs:635-786`) synchronizes pull requests in three stages:

1. **One-shot startup classification (`batch_fetch_prs`):** `sync_prs` runs
   `batch_fetch_prs` (`src/pre_push/mod.rs:397-460`), which batches
   `FindPullRequest` queries (`repository(owner, name) {
   pullRequests(headRefName: "gherrit/<change_id>", first: 1, states: [OPEN]) {
   nodes { id number baseRefName headRefName body } } }`). Each commit in
   `commits` (ordered newest-first from `HEAD` down to the stack base) is
   classified once into `resolutions`: either `PrResolution::Existing { node_id,
   number, ... }` or `PrResolution::ToCreate { change_id, title }`.
2. **Batch update and batch creation queues:** Commits with
   `PrResolution::Existing` are placed in `to_update` and sent via
   `batch_update_prs`. Commits with `PrResolution::ToCreate` are placed in
   `to_create` and sent via `batch_create_prs` (`src/pre_push/mod.rs:514-557`).
3. **Aliased single-document GraphQL batching (`run_batched_graphql`):** Both
   functions delegate to `run_batched_graphql` (`src/pre_push/mod.rs:462-512`),
   which initializes `BatchPlan::new(operations.len(),
   INITIAL_GRAPHQL_BATCH_LEN, MAX_GRAPHQL_QUERY_BYTES)` with
   `INITIAL_GRAPHQL_BATCH_LEN = 64` and `MAX_GRAPHQL_QUERY_BYTES = 262_144`
   (`src/pre_push/batching.rs:5-6`). For a 49-commit stack of new commits,
   `plan.current()` initially selects the entire range `0..49` and builds a
   single GraphQL mutation document (`src/pre_push/github.rs:69-87`):

   ```graphql
   mutation(
     $op0_repo_id: ID!, $op0_base: String!, $op0_head: String!, $op0_title: String!, $op0_body: String!,
     ...
     $op48_repo_id: ID!, $op48_base: String!, $op48_head: String!, $op48_title: String!, $op48_body: String!
   ) {
     op0: createPullRequest(input: { repositoryId: $op0_repo_id, baseRefName: $op0_base, headRefName: $op0_head, title: $op0_title, body: $op0_body }) { pullRequest { id number } }
     ...
     op48: createPullRequest(input: { repositoryId: $op48_repo_id, baseRefName: $op48_base, headRefName: $op48_head, title: $op48_title, body: $op48_body }) { pullRequest { id number } }
   }
   ```

#### Why a 49-commit `createPullRequest` batch triggers partial server execution

Per Section 6.2.1 (*Serial Execution*) of the GraphQL Specification, top-level
fields in a `mutation` operation execute serially in the order they appear in
the document, and GraphQL defines no multi-field transaction rollback when a
later field fails or exceeds server execution budgets. Unlike
`updatePullRequest` (which updates metadata columns on an existing pull request
row), each `createPullRequest` field validates `baseRefName` and `headRefName`
refs, computes merge-base and diff statistics between the two branches,
allocates a repository-scoped pull request number, inserts pull request and
timeline records, and triggers webhook/notification pipelines. When 49
`createPullRequest` fields are packed into one GraphQL request, GitHub's
GraphQL execution engine completes the first $K \approx 16$ mutations (`op0`
through `op15`, which remain permanently committed on GitHub) and aborts the
remainder of the request with `RESOURCE_LIMITS_EXCEEDED` (`"Wait a few minutes
before you try again"` / `"Exceeded ..."`).

#### Dual failure paths in `classify_response` and `BatchPlan::reject`

When that 49-mutation request fails after committing $K = 16$ pull requests on
the server, `gherrit`'s error recovery in `src/pre_push/batching.rs:40-93` and
`src/pre_push/mod.rs:479-509` fails under both possible server response shapes:

1. **Failure Path A (Partial `data` object returned alongside
   `RESOURCE_LIMITS_EXCEEDED`):** Inspect `classify_response` in
   `src/pre_push/batching.rs:64-93`:

   ```rust
   pub(super) fn classify_response(status: u16, response: &Value) -> ResponseDisposition {
       if matches!(status, 502 | 504) {
           return ResponseDisposition::RetryLimit;
       }
       let Some(errors) = response.get("errors").and_then(Value::as_array) else {
           return ResponseDisposition::Ok;
       };
       if errors.is_empty() {
           return ResponseDisposition::Ok;
       }
       let has_no_data = response.get("data").is_none_or(Value::is_null);
       let all_resource_limits = errors.iter().all(|error| {
           let code = error.get("extensions").and_then(|ext| ext.get("code")).and_then(Value::as_str);
           let ty = error.get("type").and_then(Value::as_str);
           let message = error.get("message").and_then(Value::as_str).unwrap_or("");
           matches!(code, Some("RESOURCE_LIMITS_EXCEEDED" | "RATE_LIMITED"))
               || matches!(ty, Some("RESOURCE_LIMITS_EXCEEDED" | "RATE_LIMITED"))
               || message.contains("RESOURCE_LIMITS_EXCEEDED")
               || message.contains("RATE_LIMITED")
       });
       if has_no_data && all_resource_limits {
           ResponseDisposition::RetryLimit
       } else {
           ResponseDisposition::Fatal
       }
   }
   ```

   Because GraphQL returns `data: { "op0": { "pullRequest": { ... } }, ...,
   "op15": { "pullRequest": { ... } }, "op16": null, ... }` when `op0..op15`
   succeed before `op16` hits `RESOURCE_LIMITS_EXCEEDED`, `response.get("data")`
   is a non-null JSON `Object`. Consequently `has_no_data` evaluates to `false`,
   `classify_response` returns `ResponseDisposition::Fatal`, and
   `run_batched_graphql` immediately exits with an error without attempting any
   batch-halving retry.

2. **Failure Path B (`data: null` returned with `RESOURCE_LIMITS_EXCEEDED`,
   triggering non-idempotent batch halving):** When the server returns `data:
   null` (or HTTP 502/504) after committing the first $K = 16$ pull requests,
   `classify_response` returns `ResponseDisposition::RetryLimit`, and
   `run_batched_graphql` calls `plan.reject()`
   (`src/pre_push/batching.rs:40-53`):

   ```rust
   pub fn reject(&mut self) -> Result<Backoff, ItemTooLarge> {
       let range = self.current().expect("cannot reject a completed batch plan");
       let attempted = range.len();
       if attempted == 1 {
           return Err(ItemTooLarge { index: range.start });
       }
       let retry = NonZeroUsize::new(attempted / 2).expect("rejected batch has multiple items");
       self.batch_len = retry;
       Ok(Backoff { attempted, retry: retry.get() })
   }
   ```

   Notice that `self.cursor` remains `0` while `self.batch_len` is halved from
   `49` to `49 / 2 = 24` (the planned halving sequence `49 -> 24 -> 12 -> 6 ->
   3 -> 1`). On the next iteration of the `while let Some(range) =
   plan.current()` loop (`src/pre_push/mod.rs:469`), `run_batched_graphql`
   slices `&operations[0..24]` from the immutable `operations:
   &[CreatePullRequest]` slice and re-submits `createPullRequest` for
   `op0..op23`. Because `op0..op15` were already created on GitHub during the
   `0..49` attempt, GitHub immediately rejects `op0`..`op15` with:

   ```text
   GraphQL error: A pull request already exists for <owner>:gherrit/<change-id>
   ```

   (`type: "UNPROCESSABLE"`). `classify_response` sees `all_resource_limits ==
   false`, returns `ResponseDisposition::Fatal`, and aborts `gherrit pre-push`
   on the very first retry slice `0..24`.

#### Why re-running `git push` from the shell succeeds across multiple invocations

When a user or wrapper script re-runs `git push` from scratch after a failed
push on a 49-commit stack (with $K = 16$ pull requests committed per
`createPullRequest` batch before hitting `RESOURCE_LIMITS_EXCEEDED`):

1. **Invocation 1:** `batch_fetch_prs` finds 0 existing pull requests
   (`to_create = 49`). `batch_create_prs` sends `0..49`, commits 16 pull
   requests (`0..16`) on GitHub, and aborts. Server state: **16 open PRs**.
2. **Invocation 2:** `batch_fetch_prs` queries GitHub at startup, discovers
   those 16 open pull requests, and classifies them as `PrResolution::Existing`
   (`to_update = 16`, `to_create = 33`). `batch_update_prs` updates the 16
   existing pull requests; `batch_create_prs` sends `0..33`, commits 16 more
   pull requests (`16..32`), and aborts. Server state: **32 open PRs**.
3. **Invocation 3:** `batch_fetch_prs` discovers 32 open pull requests
   (`to_update = 32`, `to_create = 17`). `batch_create_prs` sends `0..17`; if
   the per-batch cap is $K = 17$, all 17 remaining pull requests succeed in
   Invocation 3 (**49 open PRs in 3 passes**: `0 -> 16 -> 32 -> 49`). If the
   server cap is strictly $K = 16$, Invocation 3 commits 16 pull requests
   (`32..48`) and a 4th `git push` creates the final 49th pull request (`0 -> 16
   -> 32 -> 48 -> 49`).

---

### 3. Code-level fixes for single-pass idempotent synchronization in `joshlf/gherrit`

Basis: source + execution.

We implemented and tested a complete three-part fix in
[`support/gherrit-fixes.patch`](support/gherrit-fixes.patch) against
`joshlf/gherrit` commit `2dbcbb6174ac3cf75dd7fcd0ab15cb27027b405d`:

1. **Remote-qualified base-branch resolution (`resolve_base_branch_oid` in
   `src/pre_push/mod.rs`):** Pass `remote_name` (from
   `repo.default_remote_name()`) into `collect_commits` and resolve
   `refs/remotes/{remote_name}/{default_branch}` first, falling back to
   `refs/heads/{default_branch}` only when the remote-tracking ref does not
   exist (preserving unit tests that operate on remote-less local repositories):

   ```rust
   fn resolve_base_branch_oid(
       repo: &Repo,
       remote_name: &str,
       default_branch: &str,
   ) -> Result<Oid, eyre::Error> {
       let remote_ref = format!("refs/remotes/{remote_name}/{default_branch}");
       if let Ok(oid) = repo.rev_parse_single(remote_ref.as_str()) {
           return Ok(oid);
       }
       let local_ref = format!("refs/heads/{default_branch}");
       repo.rev_parse_single(local_ref.as_str())
   }
   ```

2. **Proactive `CreatePullRequest` batch size cap
   (`INITIAL_CREATE_PR_BATCH_LEN = 12` in `src/pre_push/batching.rs`):** Keep
   `INITIAL_GRAPHQL_BATCH_LEN = 64` for lightweight `FindPullRequest` and
   `UpdatePullRequest` batches, while capping `batch_create_prs` to
   `INITIAL_CREATE_PR_BATCH_LEN = 12` so that normal pushes stay below GitHub's
   per-request `createPullRequest` mutation budget ($12 < 16$).

3. **Stateful partial-prefix advancement and `batch_fetch_prs` state
   reconciliation during `batch_create_prs` retry (`src/pre_push/batching.rs`,
   `src/pre_push/github.rs`, `src/pre_push/mod.rs`):**
   - Relax `classify_response` so that `all_resource_limits` returns
     `ResponseDisposition::RetryLimit` even when `response.get("data")` contains
     a partial JSON object alongside `RESOURCE_LIMITS_EXCEEDED` /
     `RATE_LIMITED`.
   - Add `decode_partial_batch_prefix` (`src/pre_push/github.rs`), which
     extracts the contiguous leading non-null `op0..op{m-1}` entries from
     `response["data"]`, and `BatchPlan::reject_after(&mut self,
     committed_prefix: usize)` (`src/pre_push/batching.rs`), which advances
     `self.cursor += committed_prefix` before halving the batch window on the
     remaining uncommitted suffix.
   - In `batch_create_prs`, if a `CreatePullRequest` batch fails with `data:
     null` (or if a retry encounters `"A pull request already exists"`),
     re-query the remaining slice via `batch_fetch_prs`, populate any newly
     discovered PRs into `created_prs`, and call `batch_update_prs` to ensure
     their titles, bodies, and `baseRefName` links match the desired state
     before retrying the remaining uncreated suffix.

#### Simulation comparison across a 49-commit stack ($K = 16$ server limit)

The table below summarizes the deterministic execution of
[`support/simulate_graphql_batch_retry.py`](support/simulate_graphql_batch_retry.py)
(full JSON trace in
[`support/graphql_batch_retry_results.json`](support/graphql_batch_retry_results.json)):

| Strategy | Initial Batch Size | `git push` Invocations | GraphQL Requests | Final Open PRs | Outcome |
| :--- | ---: | ---: | ---: | ---: | :--- |
| Unpatched `gherrit` (Server Variant A: partial `data` + `RESOURCE_LIMITS_EXCEEDED`) | 64 (sends 49) | 1 | 2 (1 fetch + 1 create) | 16 / 49 | **Fails immediately:** `classify_response` sees `has_no_data == false` $\implies$ `ResponseDisposition::Fatal` |
| Unpatched `gherrit` (Server Variant B: `data: null` + `RESOURCE_LIMITS_EXCEEDED`) | 64 (sends 49) | 1 | 3 (1 fetch + `0..49` + `0..24`) | 16 / 49 | **Fails on first retry `0..24`:** `op0` returns `A pull request already exists` (`UNPROCESSABLE`, `Fatal`) |
| Unpatched `gherrit` re-invoked in a shell `git push` loop ($K = 16$) | 64 | 4 (or 3 if $K = 17$) | 11 | 49 / 49 | **Succeeds across multiple process invocations** (`0 -> 16 -> 32 -> 48 -> 49`) because each fresh startup runs `batch_fetch_prs` |
| **Patched Fix 3a:** Partial `data` prefix decoding + `BatchPlan::reject_after` (initial cap 64) | 64 (sends 49) | **1** | 5 (1 fetch + 4 create slices: `0..49`, `16..40`, `32..44`, `44..49`) | **49 / 49** | **Succeeds in 1 `git push`:** advances cursor `0 -> 16 -> 32 -> 44 -> 49` |
| **Patched Fix 3b:** `data: null` fallback via `batch_fetch_prs` reconciliation (initial cap 64) | 64 (sends 49) | **1** | 9 (1 fetch + create/re-fetch/update recovery) | **49 / 49** | **Succeeds in 1 `git push`:** reclassifies committed `0..16` and `16..32` prefixes via `batch_fetch_prs` |
| **Patched Combined Fix (Fixes 2 + 3):** `INITIAL_CREATE_PR_BATCH_LEN = 12` + stateful retry | 12 | **1** | 6 (1 fetch + 5 create batches of $12, 12, 12, 12, 1$) | **49 / 49** | **Succeeds in 1 `git push` with zero GraphQL errors** |

## Boundaries

- **Live GitHub GraphQL API rate-limit variance:** GitHub's per-request and
  secondary rate-limit thresholds (`RESOURCE_LIMITS_EXCEEDED`, `RATE_LIMITED`,
  and CPU time caps on `POST /graphql`) vary with repository size, diff size,
  and server load. The $K = 16$ partial-commit threshold modeled in
  [`simulate_graphql_batch_retry.py`](support/simulate_graphql_batch_retry.py)
  captures the observed 49-commit failure mode; because
  `BatchPlan::reject_after` and `batch_fetch_prs` reconciliation are
  parameterized over the actual server response rather than a hardcoded $K$, the
  patched retry loop remains sound for any $K \ge 1$.
- **Remote-tracking ref freshness:** Resolving
  `refs/remotes/{remote_name}/{default_branch}` in `collect_commits` uses the
  local repository's remote-tracking ref for `{remote_name}`. When the target
  remote's `main` branch is itself behind the stack base $B$ (Failure Mode 2b),
  the developer or release script must still fast-forward `{remote_name}/main`
  to $B$ (`git push <remote> <B>:refs/heads/main`) before pushing the stack so
  that GitHub computes pull request diffs against $B$.

## Evidence

- **`joshlf/gherrit` source revisions inspected:**
  - Commit `2dbcbb6174ac3cf75dd7fcd0ab15cb27027b405d` (`refs/heads/main`):
    - `src/util/repository.rs:72-125, 168-194` (`default_remote_name`,
      `find_default_branches`, `find_default_branch_on_default_remote`,
      `commits_between`);
    - `src/pre_push/mod.rs:146-162, 341-557, 635-786` (`collect_commits`,
      `run_for_branch`, `batch_fetch_prs`, `run_batched_graphql`,
      `batch_create_prs`, `batch_update_prs`, `sync_prs`);
    - `src/pre_push/batching.rs:5-93` (`INITIAL_GRAPHQL_BATCH_LEN`,
      `MAX_GRAPHQL_QUERY_BYTES`, `BatchPlan`, `classify_response`);
    - `src/pre_push/github.rs:45-87, 138-381` (`BatchedOperation`,
      `batch_document`, `decode_batch_response`, `FindPullRequest`,
      `CreatePullRequest`, `UpdatePullRequest`);
    - `src/pre_push/autosquash.rs:15-26` (`PendingAutosquash` remote-qualified
      rebase hint).
  - Commit `86179afb27feabd50ddd7d2dc2493892885db8ba` (`0.1.0-alpha` Cargo
    install revision): `src/util.rs:178-231, 274-300`,
    `src/pre_push/mod.rs:127-142, 377-537, 615-766`,
    `src/pre_push/batching.rs:5-93`, `src/pre_push/github.rs:45-87, 138-370`.
  - Commit `147340c2041654cba8cfc57a3e5c3115b4902ec3`: `src/pre_push.rs:70`,
    `src/util.rs:185-218`.
- **Self-contained reproducer and simulation artifacts in `support/`:**
  - [`reproduce_multi_remote_ancestry.py`](support/reproduce_multi_remote_ancestry.py)
    (SHA-256
    `003e9a57ec1ba0d0672354a29f794fa2ce67f9cde7088e270714e783e823ac5c`) and
    [`multi_remote_ancestry_results.json`](support/multi_remote_ancestry_results.json)
    (SHA-256
    `48dec98a4367b5ef8e835b40a87d5ae18e2946c34aff1c46e635a941153ccbe9`):
    reproduces Failure Modes 1, 2a, and 2b in a temporary multi-remote Git
    repository and verifies the `refs/remotes/{remote}/{default_branch}` fix.
  - [`simulate_graphql_batch_retry.py`](support/simulate_graphql_batch_retry.py)
    (SHA-256
    `51f6be70001fa525a9cb25178219f3e1e92a96c1fc9e927bb86c07a701b5bf2a`) and
    [`graphql_batch_retry_results.json`](support/graphql_batch_retry_results.json)
    (SHA-256
    `fa21e18db4e00bb508030829d645859151b2a434b337c9dedd3e77e3700f201e`):
    models GitHub's serial GraphQL mutation execution with $K = 16$ commits per
    batch on a 49-commit stack across all five unpatched and patched retry
    strategies.
  - [`gherrit-fixes.patch`](support/gherrit-fixes.patch) (SHA-256
    `49cb283abea7c01012813ccb710df1dde7455d738bc45bd6d36fba2bbcaf66d6`):
    unified `git diff` against `joshlf/gherrit` commit
    `2dbcbb6174ac3cf75dd7fcd0ab15cb27027b405d` implementing Fixes 1, 2, and 3
    along with 6 new unit tests (`cargo test --lib`: 92 passed, 0 failed).

## Revalidation

Run both self-contained Python reproducer probes from the report package root:

```bash
python3 support/reproduce_multi_remote_ancestry.py
python3 support/simulate_graphql_batch_retry.py
```

Both scripts require only Python 3 and `git`
(`reproduce_multi_remote_ancestry.py` creates and cleans up a temporary
directory automatically), verify all assertions, and exit with status `0`. To
validate the Rust patch against `joshlf/gherrit`, check out
`2dbcbb6174ac3cf75dd7fcd0ab15cb27027b405d`, apply `git apply
support/gherrit-fixes.patch`, and run `cargo test --lib`.
