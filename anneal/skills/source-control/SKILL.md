---
name: source-control
description: >-
  Manage Git commits, commit messages, delegated-worker quarantine, branches,
  stacked pull requests, bottom-up prefix locking, and upward rebasing in
  Anneal. Not permission to rewrite history, push, publish, or merge. Use when
  structuring commits, formatting messages, integrating worker commits, or
  managing PR stacks. Do not use for review orchestration (`change-review`) or
  TCB checklists (`trust-review`).
---

# Source control

Compose this skill with
[`commit-message`](../../../skills/commit-message/SKILL.md),
[`authorship-disclosure`](../../../skills/authorship-disclosure/SKILL.md),
[`reader-oriented-explanation`](../../../skills/reader-oriented-explanation/SKILL.md),
and [`clear-writing`](../../../skills/clear-writing/SKILL.md). This skill
grants no authority to rewrite published history, push branches, open, update,
merge, or close pull requests, or waive merge gates; act only when authorized.

## Structure and size commits for review

Inspect the current branch before changing history (whether to work on it or
create a separate branch is a case-by-case decision), preserve prior review
history, and size commits so each unit is coherent and independently
reviewable:

1. **One logical change per commit:** Separate refactoring, mechanical renames,
   formatting adjustments, semantic changes, and policy edits into distinct
   commits (and keep policy edits in dedicated policy-only PRs where possible
   so Gate 2 reviewers do not evaluate product code under unreviewed modified
   rules). Never fold an unrelated cleanup into a `trusted/` soundness fix.
2. **Cohesive PR sizing:** Keep each PR focused on one reviewable unit; split
   large multi-subsystem work into a stack when independent layers review more
   clearly bottom-up, without fragmenting so finely that reviewers must hold
   many commits in mind at once.
3. **Self-contained commits:** Every commit builds, passes applicable tests,
   and keeps tracked derived artifacts synchronized with its tree.
4. **Bottom-up stack self-containment:** Earlier commits and their docs must
   stand on their own without hardcoding unsettled upper-stack counts, line
   numbers, or unmerged implementation details.

## Format commit messages to repository conventions

Follow [`commit-message`](../../../skills/commit-message/SKILL.md) and these
Anneal rules. Commit messages must be concise and self-contained: explain
rationale and necessary context in the commit message itself rather than relying
on an issue link (Git history is more durable than issue-tracker history), and
avoid superfluous details or session narrative.

- **Subject line and body layout:**
  1. **Subsystem prefix:** When a commit affects a specific subsystem, prefix
     the subject with `[subsystem]` in square brackets, omitting any `anneal`
     prefix (for example `[ci]`, `[audit]`, `[capture]`, `[agents]`, `[docs]`,
     `[theory]`, `[trusted]`).
  2. **Imperative, capitalized subject:** Imperative mood, capitalize the first
     word after any `[subsystem]` prefix, no trailing period, <=50 characters
     when practical (<=72 hard limit).
  3. **Blank line and 72-column body:** Separate the body with one blank line;
     omit the body when the subject is genuinely self-explanatory (such as a
     typo fix). Wrap body prose at 72 columns (except long URLs, code spans, or
     trailers), explaining *what* changed, *why*, and any intentional rule
     relaxation or tightening.
- **Issue references:** Include GitHub issue references (`#123`) on their own
  line in the body or footer: `Closes #123`, `Fixes #123`, or `Resolves #123`
  when completely resolving an issue; `Makes progress on #123` when advancing
  without resolving.
- **Prohibited references and task markers:** Commit messages must never
  reference:
  1. **Relative moments in time** ("currently", "today", "recently", "soon");
  2. **Individuals** by name or handle outside standard Git attribution
     trailers;
  3. **Hosted code reviews or pull request URLs** (cite commits in this repo by
     SHA-1 hash, and commits in other repos by public commit URL);
  4. **Other ephemeral entities** that may not make sense to future readers.
  <!-- TODO-check-disable -->
  Never include `TODO` markers or their disable/enable directives in commit
  messages (`./ci/check_todo.sh` rejects un-disabled `TODO` markers across
  `origin/main..HEAD`; verify the absence of disable/enable directives
  manually).
  <!-- TODO-check-enable -->
- **Authorship disclosure and privacy:** Include the `Agent-authored-by:`
  trailer per
  [`authorship-disclosure`](../../../skills/authorship-disclosure/SKILL.md)
  whenever an agent contributed (literal `AI agent acting on <user>'s behalf`,
  never a vendor or model name), and follow the privacy rule in
  [`AGENTS.md`](../../AGENTS.md#standing-rules).
- **Post-amend accuracy:** After any amend or rebase, re-verify the commit
  message against `git diff <parent>..HEAD` so counts, file lists, and claims
  stay accurate.

## Integrate delegated worker commits

This section is the sole canonical procedure for integrating commits from
isolated worker agents or bundles.

### Isolation boundary

- **Untrusted workers require host-enforced filesystem and write isolation:**
  Under the same OS account or shared filesystem, a separate clone alone does
  not isolate writes—an untrusted worker can modify the coordinator worktree,
  its `.git` directory, or global Git configuration before returning a bundle,
  bypassing commit-only quarantine. Run untrusted workers inside host-enforced
  filesystem/write isolation (such as an OS sandbox, container, VM, or separate
  OS user that cannot write coordinator state or global Git config) with a
  separate clone inside that boundary, and return commits via
  `git bundle create <file> HEAD` (preferred, so the bundle contains `HEAD`) or
  a read-only separate repository path.
- **Cooperative parallel workers still require separate clones (not shared
  `.git` worktrees):** Local `git worktree` checkouts share `.git/config`,
  hooks, and object storage, so even cooperative parallel workers must use
  separate clones to prevent accidental or faulty `.git` writes from affecting
  the coordinator; never treat a clone-only setup without host-enforced write
  isolation as a security boundary for untrusted workers.
- **Pure object-store inspection before checkout:** Never check out, merge,
  cherry-pick, or run builds or Lean elaboration on worker commits until every
  object-store quarantine check below passes.

### Mandatory fail-closed quarantine sequence

Run this exact sequence as a **standalone `bash` script** (never `source` it
inside a shell conditional such as `if`, `&&`, or `||`, which disables `set -e`
across the entire script) from the coordinator repository (replace variables
with the task values; set `ALLOWED_PREFIXES` to the worker's explicit non-root
assigned path prefix allowlist—never `.`; pass any authorized per-run
exceptions only via `--allow-exec <path>` or `--allow-policy <path>` flags):

```bash
set -euo pipefail
: "${task:?}" "${base:?}" "${expected_worker_sha:?}" "${bundle:?}"
: "${ALLOWED_PREFIXES:?}"
# Always reset inherited allowlists so prior runs cannot leak privileges; pass
# per-run exceptions only via --allow-exec / --allow-policy flags.
ALLOW_EXEC_PATHS=""
ALLOW_POLICY_PATHS=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --allow-exec)
      [ "$#" -ge 2 ] && [ -n "$2" ] && [[ "$2" != *:* ]] \
        || { echo "quarantine failed: invalid arg for $1" >&2; exit 1; }
      ALLOW_EXEC_PATHS="${ALLOW_EXEC_PATHS:+$ALLOW_EXEC_PATHS:}$2"; shift 2 ;;
    --allow-policy)
      [ "$#" -ge 2 ] && [ -n "$2" ] && [[ "$2" != *:* ]] \
        || { echo "quarantine failed: invalid arg for $1" >&2; exit 1; }
      ALLOW_POLICY_PATHS="${ALLOW_POLICY_PATHS:+$ALLOW_POLICY_PATHS:}$2"; shift 2 ;;
    *) echo "quarantine failed: unknown argument: $1" >&2; exit 1 ;;
  esac
done
export ALLOWED_PREFIXES ALLOW_EXEC_PATHS ALLOW_POLICY_PATHS

qgit() {
  git -c core.hooksPath=/dev/null \
      -c core.fsmonitor=false \
      -c transfer.fsckObjects=true \
      -c fetch.fsckObjects=true "$@"
}

quarantine_keep=0
cleanup_quarantine() {
  if [ "$quarantine_keep" -ne 1 ]; then
    qgit update-ref -d "refs/quarantine/$task" >/dev/null 2>&1 || true
  fi
}
trap cleanup_quarantine EXIT
fail() { echo "quarantine failed: $*" >&2; exit 1; }

base="$(qgit rev-parse --verify "${base}^{commit}")" \
  || fail "invalid base commit"

# 1. Import into a quarantine ref without touching the working tree.
# Preferred transport: git bundle created with `git bundle create <file> HEAD`.
qgit bundle verify "$bundle" >/dev/null || fail "bundle verify failed"
qgit fetch --no-tags --no-write-fetch-head --no-recurse-submodules "$bundle" \
  "+HEAD:refs/quarantine/$task" || fail "quarantine fetch failed"

# Fallback transport (separate local clone; neutralize target repo config):
# qgit fetch --no-tags --no-write-fetch-head --no-recurse-submodules \
#   --upload-pack='git -c core.hooksPath=/dev/null -c core.fsmonitor=false '\
# 'upload-pack' \
#   "$worker_repo" "+$worker_ref:refs/quarantine/$task" \
#   || fail "quarantine fetch failed"

head="$(qgit rev-parse --verify "refs/quarantine/$task^{commit}")" \
  || fail "missing quarantine commit"
if [ "$head" != "$expected_worker_sha" ]; then fail "unexpected SHA"; fi
if ! qgit merge-base --is-ancestor "$base" "$head"; then
  fail "worker head does not descend from base"
fi
if [ "$base" = "$head" ]; then fail "worker produced no new commits"; fi
merges="$(qgit rev-list --count --min-parents=2 "$base..$head")" \
  || fail "merge-commit count failed"
if [ "$merges" -ne 0 ]; then fail "merge commit in worker range"; fi

# Mechanically audit EVERY commit in base..head (catches add-then-delete,
# forbidden modes, out-of-scope, hidden dot-directories/dotfiles, policy/config
# paths, non-ASCII/homoglyph/bidi/control characters) plus full-tree path and
# directory-prefix casefold/NFC collisions.
# Env vars: ALLOWED_PREFIXES (required, colon-separated, never '.'); per-run
# --allow-exec / --allow-policy flags populate ALLOW_EXEC_PATHS / ALLOW_POLICY_PATHS.
qgit rev-list --reverse "$base..$head" | qgit diff-tree --stdin -r -z \
  --no-commit-id --no-renames -m --root | python3 -B -c '
import os, pathlib, sys, unicodedata
allowed = [p.rstrip("/") for p in os.environ.get("ALLOWED_PREFIXES", "").split(":") if p]
if not allowed or any(a in ("", ".", "..") or a.startswith("/") for a in allowed):
    sys.exit("ALLOWED_PREFIXES must list explicit non-root prefixes")
allow_exec = {p for p in os.environ.get("ALLOW_EXEC_PATHS", "").split(":") if p}
allow_pol = {p for p in os.environ.get("ALLOW_POLICY_PATHS", "").split(":") if p}
forbid_names = {
    "agent.md", "agents.md", "agents.override.md", "claude.md", "gemini.md",
    "skill.md", "meta_principles.md", "principles.md", "threat_model.md",
    "build.rs", "makefile", "gnumakefile", "justfile", "cargo.toml",
    "cargo.lock", "flake.nix", "flake.lock", "lean-toolchain",
    "lake-manifest.json", "foundation-lock.json", "root-manifest.sha256",
}
forbid_paths = {
    "docs/codex-review.md", "docs/review-policy-design.md",
    "docs/trust-model.md",
}
forbid_top_dirs = {"ci", "skills", "trusted"}
forbid_build_exts = (
    ".olean", ".olean.server", ".olean.private", ".ilean", ".ir", ".ir.sig",
)
forbid_exts = forbid_build_exts + (".nix", ".sh", ".bash", ".zsh", ".py")
bad_cats = {"Cc", "Cf", "Zl", "Zp"}
def decode_utf8(raw):
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError:
        sys.exit(f"non-UTF-8 path: {raw!r}")
def in_scope(path):
    return any(path == a or path.startswith(a + "/") for a in allowed)
toks = sys.stdin.buffer.read().split(b"\0")
i = 0
while i < len(toks):
    if not toks[i]:
        i += 1; continue
    meta = decode_utf8(toks[i])
    parts = meta[1:].split() if meta.startswith(":") else []
    if len(parts) < 5 or i + 1 >= len(toks):
        sys.exit(f"unexpected diff-tree token: {meta!r}")
    new_mode, path = parts[1], decode_utf8(toks[i + 1])
    i += 2
    if new_mode not in ("000000", "100644"):
        if not (new_mode == "100755" and path in allow_exec):
            sys.exit(f"forbidden mode {new_mode}: {path!r}")
    if (not path.isascii()
            or any(ord(c) < 0x20 or ord(c) >= 0x7f for c in path)
            or any(unicodedata.category(c) in bad_cats for c in path)):
        sys.exit(f"non-ASCII/control/bidi char in path: {path!r}")
    raw_segs = path.split("/")
    if not path or path.startswith("/") or any(s in ("", ".", "..") for s in raw_segs):
        sys.exit(f"invalid path segment: {path!r}")
    segs = pathlib.PurePosixPath(path).parts
    if not in_scope(path):
        sys.exit(f"out of allowed scope: {path!r}")
    path_l = path.lower()
    segs_l = [s.lower() for s in segs]
    base_l = segs_l[-1]
    if (base_l == "agents.override.md"
            or any(s in (".git", ".cargo", ".lake", "target") for s in segs_l)
            or segs_l[0].startswith("result")
            or base_l.startswith((".git", "rust-toolchain"))
            or base_l == ".envrc"
            or (base_l == "lean-toolchain" and path != "trusted/lean/lean-toolchain")
            or base_l.endswith(forbid_build_exts)):
        sys.exit(f"unconditionally forbidden path: {path!r}")
    if path in allow_pol:
        continue
    if (any(s.startswith(".") for s in segs_l)
            or base_l in forbid_names
            or path_l in forbid_paths
            or base_l.startswith("lakefile")
            or segs_l[0] in forbid_top_dirs
            or base_l.endswith(forbid_exts)
            or (base_l.endswith(".lean") and segs[0] != "theory")):
        sys.exit(f"forbidden path: {path!r}")
' || fail "per-commit path/mode audit failed"

commits="$(qgit rev-list --reverse "$base..$head")" \
  || fail "failed to enumerate worker commits"
for commit in $commits; do
  qgit ls-tree -r -z --full-tree --name-only "$commit" | python3 -B -c '
import pathlib, sys, unicodedata
bad_cats = {"Cc", "Cf", "Zl", "Zp"}
seen = {}
for raw in sys.stdin.buffer.read().split(b"\0"):
    if not raw:
        continue
    try:
        p = raw.decode("utf-8")
    except UnicodeDecodeError:
        sys.exit(f"non-UTF-8 tree path: {raw!r}")
    if any(unicodedata.category(c) in bad_cats for c in p):
        sys.exit(f"control/bidi char in tree: {p!r}")
    raw_segs = p.split("/")
    if not p or p.startswith("/") or any(s in ("", ".", "..") for s in raw_segs):
        sys.exit(f"invalid tree path segment: {p!r}")
    cur = ""
    for seg in pathlib.PurePosixPath(p).parts:
        cur = f"{cur}/{seg}" if cur else seg
        k = unicodedata.normalize("NFC", cur).casefold()
        if k in seen and seen[k] != cur:
            sys.exit(f"case/NFC collision: {seen[k]!r} vs {cur!r}")
        seen[k] = cur
' || fail "tree collision/encoding audit failed on $commit"
done
quarantine_keep=1
```

On any failure (including unset variables), the `EXIT` trap removes
`refs/quarantine/$task` automatically and rejects the worker result. The script
always clears any inherited `ALLOW_EXEC_PATHS` and `ALLOW_POLICY_PATHS`
environment variables; only when a worker's assigned scope explicitly
authorizes an executable script (`100755`) or a TCB, CI, governing-doc,
dot-prefixed, or policy path may the coordinator pass that exact path per run
via `--allow-exec <path>` or `--allow-policy <path>` (note that an executable
script inside a forbidden directory or extension—such as a `.sh` or `.py` file
under `ci/` or `trusted/`—must be passed to **both** `--allow-exec` and
`--allow-policy`; neither ever bypasses mode, ASCII, scope, `.git` / `.git*`,
`.cargo`, `rust-toolchain*`, `.envrc`, non-TCB `lean-toolchain`,
`AGENTS.override.md`, or build-artifact (`target`, `.lake`, `/result*`,
`.olean`/`.ilean`/`.ir*`) checks)—and must then route the integrated result to
[`trust-review`](../trust-review/SKILL.md) (converging local Pass 2 or Pass 1
trust review across `main..<head>` before any push per
[`change-review`](../change-review/SKILL.md#schedule-by-data-dependency)).

Only after every check passes may the coordinator integrate the commits (via
fast-forward when linear history permits, or `git -c core.hooksPath=/dev/null
-c core.fsmonitor=false -c core.symlinks=false cherry-pick "$base..$head"`,
passing `-c user.name=... -c user.email=...` if your committer identity is not
configured locally in the coordinator repo), delete `refs/quarantine/$task`,
run non-elaborating syntactic audits before any OS-sandboxed build or Lean
elaboration on untrusted worker code, and route the integrated result into
[`trust-review`](../trust-review/SKILL.md).

## Publish branches and stacked pull requests

Push branches (`git push`, passing `--set-upstream origin <branch>` when no
upstream is configured) or open, update, merge, or close pull requests (`gh pr`
or `gh stack`; see `gh pr --help` and `gh stack --help`) **only when
authorized**.

- **Stack organization:** For multi-part changes on same-repository branches,
  consider organizing pull requests as a stack with
  [`gh stack`](https://gh.io/stacks) (see the
  [`gh-stack` skill](https://github.com/github/gh-stack/tree/main/skills/gh-stack))
  when it aids review, or use a single pull request when simpler—leave the
  choice to the developer.
- **PR descriptions:** Reuse commit prose verbatim rather than authoring a
  second summary or review report:
  - *Single-commit PRs:* Use the commit subject as the PR title and copy the
    commit body verbatim as the PR description, mechanically unwrapping
    72-column hard line breaks for GitHub Flavored Markdown (while preserving
    blank lines, code blocks, lists, blockquotes, tables, explicit hard breaks,
    and issue-reference lines) and converting the trailing `Agent-authored-by:`
    trailer into the prose notice per
    [`authorship-disclosure`](../../../skills/authorship-disclosure/SKILL.md).
  - *Multi-commit PRs:* Draft a squash-style commit message describing the net
    change against the target base under
    [Format commit messages to repository conventions](#format-commit-messages-to-repository-conventions)
    and use its subject and unwrapped body verbatim as the PR title and
    description.
  - *No extra PR sections:* Never add `## Summary`, `## Motivation`,
    `## Verification`, before/after tables, per-file catalogs, or `Human review
    surface` blocks to the PR description; put `Human review surface`, `Gate 2
    finding dispositions` (legacy `Codex finding dispositions`), and receipts in
    the Review Receipt comment per
    [`change-review`](../change-review/SKILL.md#record-the-receipt-and-converge).
- **Non-interactive stacked publication with prepared bodies:** Do not use bare
  `gh stack submit` (prompts interactively and can hang under a PTY) or
  `gh stack submit --auto` (publishes PRs with auto-generated titles before
  prepared commit-derived PR descriptions with
  [`authorship-disclosure`](../../../skills/authorship-disclosure/SKILL.md) are
  attached). Instead, push only branches whose
  cumulative `main..<head>` diff satisfies the pre-push CI-executed-surface
  gate in
  [`change-review`](../change-review/SKILL.md#schedule-by-data-dependency)
  (use `git push --set-upstream origin <branch>` for converged lower prefixes,
  and run `gh stack push` only when every branch in the stack clears that
  cumulative gate), create each PR with its explicit head branch, title, and
  body
  (`gh pr create --draft --base <previous-branch> --head <branch> --title "<title>" --body-file <file>`),
  and link the stack bottom-to-top using only non-mutating metadata linkage
  (`gh stack link --base main <branch-or-pr>...`—always pass `--base main`
  or the explicit trunk branch because omitting `--base` resolves against
  `origin/HEAD`, which can retarget and permanently auto-close the bottom PR
  when `origin/HEAD` points elsewhere; do not run `gh stack sync` after freezing
  heads or receipts, because it can fetch, cascade-rebase, and push branches
  without re-running affected pre-push gates—if a stack needs syncing, do so
  before freezing and re-run every affected gate on the new SHAs). If
  `git push` succeeds but `gh pr create` or `gh pr edit` fails or times out,
  inspect live GitHub PR state (`gh pr list --head <branch>`) before retrying
  to avoid duplicate PRs, preserve the prepared receipt, and report the
  already-published branch/SHA without claiming the PR write succeeded.
- **Draft-PR pipelining and readiness:** Complete static Pass 1 hygiene and
  deterministic preflight before any push—and satisfy the cumulative
  `main..<head>` CI-executed-surface gate in
  [`change-review`](../change-review/SKILL.md#schedule-by-data-dependency)
  before pushing any branch. When authorized to push early for parallel CI and
  Gate 2 review, push the frozen candidate to a **draft** PR (drafts skip
  `current_anneal`; add `run-ci` for full PR CI), verify the remote head
  matches it, and mark the PR ready for human review (`gh pr ready`) only after
  Gate 1 (local review) converges and the Review Receipt PR comment (including
  its complete `Human review surface` block) is posted (unless the user
  explicitly requests a visibly incomplete handoff).
- **Stack merge guard:** Land stacked PRs bottom-up and never run
  `gh stack merge` unless every PR it would merge satisfies the merge gates in
  [`docs/codex-review.md`](../../docs/codex-review.md#merge-gates).

## Lock and rebase a stack

- **Bottom-up prefix locking:** Once a lower PR prefix converges, treat it as
  locked against cosmetic or convenience churn from upper PRs. Reopen a locked
  lower PR only for a blocking soundness, trust, interface, or Gate 1 (local
  review) defect.
- **Upward rebase cascade:** Whenever a lower PR changes or merges, rebase
  every upper PR locally onto the updated lower head (or onto `origin/main` via
  `git rebase --onto <new-base> <old-lower-head>` when the lower PR was
  squash-merged into `main`) so `merge_base == target_base`; do not run
  `gh stack sync` before post-rebase checks and pre-push gates pass, because
  `gh stack sync` also pushes rebased branches. When authorized to push rebased
  branches, use `--force-with-lease` (never bare `--force`). Rebasing a
  one-commit PR onto its lower PR's squash commit, whose tree equals the lower
  PR's reviewed head tree, leaves the upper PR's identity—and its review
  evidence—unchanged per
  `main`); only its preflight and CI rerun. To avoid O(n²) Gate 2 re-reviews
  during a stack landing cascade when identities do change, defer pushing
  rebased upper branches until each reaches the bottom of the stack (or its base
  settles on `main`).
- **Mandatory post-rebase checks:** After every rebase, run:
  1. `git range-diff <old-base>..<old-head> <new-base>..<new-head>` to verify
     whether patch diffs or upstream interfaces changed;
  2. An audit for stale parent-dependent counts, docstrings, or commit-message
     claims against `git diff <new-base>..HEAD`;
  3. Scoped or full re-verification per
     [`change-review`](../change-review/SKILL.md#key-every-result-to-its-inputs)
     (including deterministic preflight, plus fresh Gate 2 review whenever the
     identity changed and CI before merge on the new `head`).
