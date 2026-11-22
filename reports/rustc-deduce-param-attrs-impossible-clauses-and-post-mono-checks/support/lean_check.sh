#!/usr/bin/env bash
# Kernel-check the Lean development in this directory and print its audit.
#
# Usage: ./lean_check.sh [path-to-lean-4.34.1-binary]
# Exit status 0 means: every proof was accepted by the kernel with
# warnings-as-errors, and the audit command at the end of the file found no
# forbidden axiom, no unsafe/partial/opaque declaration and no unsafe recursion
# companion among the module's own declarations.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean_bin="${1:-${LEAN:-lean}}"
cd "$here"
"$lean_bin" --version
exec "$lean_bin" -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  DeduceParamAttrsImpossibleClausesAndMonoChecksSoundness.lean
