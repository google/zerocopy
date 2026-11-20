#!/usr/bin/env bash
# Commit-history counts used by the report. Requires an authenticated `gh` CLI.
# Prints 12-character abbreviated SHAs only.
set -euo pipefail
echo "## mathlib4 commits touching lean-toolchain, 2025-11-20..2026-11-20, reachable from the pinned commit"
gh api --paginate "repos/leanprover-community/mathlib4/commits?path=lean-toolchain&sha=5fc503cdd50c2c198f54ccc97121ec82919e2930&since=2025-11-20T00:00:00Z&until=2026-11-20T23:59:59Z&per_page=100" \
  --jq '.[] | .sha[0:12] + " " + .commit.committer.date + " " + (.commit.message | split("\n")[0])'
echo "## rocq commits touching dev/ci/user-overlays, 2025-11-20..2026-11-20, per month"
gh api --paginate "repos/rocq-prover/rocq/commits?path=dev/ci/user-overlays&sha=ddb69e5c5cff459fc2b0dfe3ec4ed0c968720c76&since=2025-11-20T00:00:00Z&until=2026-11-20T23:59:59Z&per_page=100" \
  --jq '.[] | .commit.committer.date[0:7]' | sort | uniq -c
