#!/usr/bin/env bash
# Kernel-check SizedHierarchyAndExternTailSoundness.lean and audit its axioms.
#
# Usage:  LEAN=/path/to/lean ./verify_lean.sh
# `LEAN` defaults to `lean` on PATH; it must be Lean 4 v4.34.1 for the recorded
# output to be comparable.  Optionally set RUN_WRAPPER to a resource-limiting
# launcher that is placed in front of every `lean` invocation.
#
# Steps
#   1. token scan of the proof source for forbidden constructs;
#   2. elaborate + kernel-check the module with warnings as errors, writing an
#      .olean into a temporary directory;
#   3. run AxiomAudit.lean against that .olean (walks every declaration).
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN="${LEAN:-lean}"
read -r -a WRAP <<< "${RUN_WRAPPER:-}"
src="$here/SizedHierarchyAndExternTailSoundness.lean"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT

echo "== lean version"
"$LEAN" --version

echo "== token scan (each count must be 0)"
fail=0
for pat in '\bsorry\b' '\badmit\b' 'native_decide' 'bv_decide' '\bomega\b' 'partial def' \
           '\bunsafe\b' 'Classical\.' '^axiom\b' 'implemented_by' '\bderiving\b' '^import\b' \
           '\bopaque\b' '_unsafe_rec'; do
  n="$(grep -c -E "$pat" "$src" || true)"
  printf '  %-18s %s\n' "$pat" "$n"
  if [ "$n" != "0" ]; then fail=1; fi
done
if [ "$fail" != "0" ]; then echo "TOKEN SCAN: FAIL"; exit 1; fi
echo "TOKEN SCAN: PASS"

echo "== elaborate and kernel-check (warnings are errors)"
"${WRAP[@]}" "$LEAN" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  -o "$out/SizedHierarchyAndExternTailSoundness.olean" "$src"
echo "MODULE CHECK: PASS (exit 0)"

echo "== declaration and axiom audit"
LEAN_PATH="$out" "${WRAP[@]}" "$LEAN" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false \
  -DwarningAsError=true "$here/AxiomAudit.lean"
echo "AXIOM AUDIT: PASS (exit 0)"
