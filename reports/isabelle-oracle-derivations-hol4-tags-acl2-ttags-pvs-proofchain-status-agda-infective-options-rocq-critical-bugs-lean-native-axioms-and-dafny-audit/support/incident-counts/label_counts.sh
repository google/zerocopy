#!/usr/bin/env bash
# Count GitHub issues/PRs carrying a label via the authenticated search API.
# Usage: label_counts.sh   (requires `gh` authenticated; read-only GET requests)
set -u
q() { # $1 = query string
  local n
  n=$(gh api -X GET search/issues -f q="$1" -f per_page=1 --jq '.total_count' 2>&1)
  printf '%s\t%s\t%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$n" "$1"
}
for spec in 'agda/agda|false' 'leanprover/lean4|soundness' 'leanprover/lean4|runtime-soundness' 'rocq-prover/rocq|kind: inconsistency'; do
  repo=${spec%%|*}; label=${spec#*|}
  q "repo:$repo label:\"$label\""
  q "repo:$repo label:\"$label\" is:issue"
  q "repo:$repo label:\"$label\" is:issue is:open"
  q "repo:$repo label:\"$label\" is:issue is:closed"
  q "repo:$repo label:\"$label\" is:pr"
done
