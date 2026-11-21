#!/bin/sh
# Census of test-harness usage in one simulation framework at a pinned commit.
# Usage: moose_test_census.sh <owner/repo> <40-hex commit> <empty work dir>
# Needs: an authenticated `gh` CLI (read-only GET), curl, python3.
# Lists every blob (descending into subtrees when the recursive tree API
# truncates), downloads every test-spec file named `tests` and every *.py file
# under a `/tests/` path, then counts tester declarations and slope assertions.
set -eu
REPO=$1; SHA=$2; W=$3
mkdir -p "$W/specs" "$W/testpy"
python3 "$(dirname "$0")/list_tree.py" "$REPO" "$SHA" > "$W/paths.tsv"
echo "blob paths: $(wc -l < "$W/paths.tsv")"
awk -F'\t' '{n=split($1,a,"/"); if (a[n]=="tests") print $1}' "$W/paths.tsv" > "$W/specs.txt"
awk -F'\t' '$1 ~ /\/tests\// && $1 ~ /\.py$/ {print $1}' "$W/paths.tsv" > "$W/testpy.txt"
echo "spec files: $(wc -l < "$W/specs.txt"); python files under /tests/: $(wc -l < "$W/testpy.txt")"
fetch() { xargs -P 32 -I{} sh -c 'f=$(echo "{}" | tr "/" "%"); curl -sSL --retry 3 -o "'"$1"'/$f" "https://raw.githubusercontent.com/'"$REPO/$SHA"'/{}"'; }
fetch "$W/specs" < "$W/specs.txt"
fetch "$W/testpy" < "$W/testpy.txt"
echo "== tester 'type =' declarations in spec files"
grep -hoiE "^\s*type\s*=\s*'?\"?[A-Za-z]+" "$W"/specs/* | sed -E "s/.*=\s*['\"]?//" | sort | uniq -c | sort -rn
cd "$W/testpy"
echo "== python test files importing mms: $(grep -lE '^\s*import mms|from mms' * | wc -l)"
echo "== python test files using label_to_slope: $(grep -l label_to_slope * | wc -l)"
echo "== fuzzyAbsoluteEqual(...) assertion forms"
grep -ohE "fuzzyAbsoluteEqual\([^)]*\)" * | sed -E 's/\s+/ /g' | sort | uniq -c | sort -rn
echo "== num_fitted_points values"
grep -ohE "num_fitted_points\s*=\s*[0-9]+" * | sort | uniq -c
echo "== literal refinement counts in run_spatial/run_temporal calls"
grep -ohE "run_(spatial|temporal)\([^,]*,\s*[0-9]+" * | sed -E 's/.*,\s*//' | sort -n | uniq -c
