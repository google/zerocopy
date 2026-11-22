#!/bin/sh
# Kernel-check the formalization, then audit every constant of the module.
#
#   LEAN=/path/to/lean-v4.34.1/bin/lean sh check_lean.sh
#
# Step 1 elaborates and kernel-checks the module with warnings treated as errors
# and prints the axioms each headline theorem depends on. The compiled module is
# written to a temporary directory that is removed on exit.
# Step 2 imports that module and runs the whole-module audit.
set -eu
LEAN="${LEAN:-lean}"
cd "$(dirname "$0")"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
flags="-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true"
echo "== lean --version"
"$LEAN" --version
echo "== step 1: XrayAttrOverrideAndCoverageBranchSoundness.lean"
"$LEAN" $flags -o "$out/XrayAttrOverrideAndCoverageBranchSoundness.olean" \
  XrayAttrOverrideAndCoverageBranchSoundness.lean
echo "step 1 exit status: $?"
echo "== step 2: AuditXrayAttrOverrideAndCoverageBranchSoundness.lean"
LEAN_PATH="$out" "$LEAN" $flags AuditXrayAttrOverrideAndCoverageBranchSoundness.lean
echo "step 2 exit status: $?"
