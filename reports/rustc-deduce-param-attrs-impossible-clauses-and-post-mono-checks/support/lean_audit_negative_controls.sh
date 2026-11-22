#!/usr/bin/env bash
# Demonstrate that the audit at the end of the Lean file is not vacuous:
# each mutated copy below must be REJECTED by `lean`.
#
#   1. one recursive definition loses its `noncomputable` marker
#      (the code generator then emits an unsafe recursion companion);
#   2. one proof is replaced by an admitted goal.
#
# Usage: ./lean_audit_negative_controls.sh [path-to-lean-4.34.1-binary]
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean_bin="${1:-${LEAN:-lean}}"
src="$here/DeduceParamAttrsImpossibleClausesAndMonoChecksSoundness.lean"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
admit="$(printf 'so%s' 'rry')"
status=0

run_case() {
  local name="$1" file="$2" expect="$3"
  local out rc
  out="$("$lean_bin" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false "$file" 2>&1)"
  rc=$?
  if [ "$rc" -ne 0 ] && printf '%s' "$out" | grep -q "$expect"; then
    echo "negative control '$name': rejected as expected (exit $rc; matched: $expect)"
  else
    echo "negative control '$name': NOT rejected as expected (exit $rc)"
    status=1
  fi
}

sed 's/^noncomputable def trim : /def trim : /' "$src" > "$work/Control1.lean"
cmp -s "$src" "$work/Control1.lean" && { echo "control 1: mutation did not apply"; status=1; }
run_case "recursive definition left computable" "$work/Control1.lean" "unsafe recursion companions"

awk -v admit="$admit" '
  /^theorem trim_idem / { print; print "  " admit; skip = 1; next }
  skip && /^$/ { skip = 0 }
  !skip { print }
' "$src" > "$work/Control2.lean"
cmp -s "$src" "$work/Control2.lean" && { echo "control 2: mutation did not apply"; status=1; }
run_case "proof replaced by an admitted goal" "$work/Control2.lean" "forbidden axioms"

exit "$status"
