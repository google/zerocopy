#!/bin/sh
# Rebuild the Lean toy model in a scratch copy and compare its axiom audit with
# audit/axioms.txt. Requires `lake` for the toolchain named in lean/lean-toolchain.
# Writes nothing into the package directory.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -r "$here/lean/." "$work/"
if grep -rnwE 'sorry|admit|axiom|native_decide|unsafe|partial' --include='*.lean' "$work"; then
  echo "check_lean: forbidden token in Lean sources" >&2
  exit 1
fi
cd "$work"
lake build
lake env lean Audit.lean | tr -d '\r' > "$work/axioms.out"
diff -u "$here/audit/axioms.txt" "$work/axioms.out"
allowed='(propext|Classical\.choice|Quot\.sound)'
if grep -vE "does not depend on any axioms$|depends on axioms: \[$allowed(, $allowed)*\]$" "$work/axioms.out"; then
  echo "check_lean: unexpected axiom dependency" >&2
  exit 1
fi
echo "check_lean: OK ($(wc -l < "$work/axioms.out") theorems audited)"
