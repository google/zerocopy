#!/usr/bin/env bash
# Environment-wide audit of RustAtomicLoweringSoundness.lean.
#
# The file itself prints `#print axioms` for 53 named theorems. This script
# checks *every* declaration the file adds to the environment: it prepends
# `import Lean`, appends a metaprogram that walks the declarations of the
# current file, and prints one line
#
#   AUDIT|declarations=<n>|theorems=<n>|unsafe=<n>|partial=<n>|unsafe_rec=<n>|axioms=<list>|declarations_using_Quot.sound=<n>
#
# where `axioms` is the union of the axioms every declaration depends on
# (generated auxiliaries such as equation lemmas and derived instances included).
#
#   LEAN=/path/to/lean ./audit_lean_environment.sh
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

{
  echo 'import Lean'
  cat "$here/RustAtomicLoweringSoundness.lean"
  cat <<'LEAN_EOF'

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut axs : Array Name := #[]
  let mut quotUsers : Array Name := #[]
  let mut total := 0
  let mut theorems := 0
  let mut unsafeDecls := 0
  let mut partialDecls := 0
  let mut unsafeRec := 0
  for (name, ci) in env.constants.map₂.toList do
    total := total + 1
    if (name.toString.splitOn "_unsafe_rec").length > 1 then unsafeRec := unsafeRec + 1
    if ci.isUnsafe then unsafeDecls := unsafeDecls + 1
    if ci.isPartial then partialDecls := partialDecls + 1
    if let .thmInfo _ := ci then theorems := theorems + 1
    let used ← collectAxioms name
    if used.contains ``Quot.sound then quotUsers := quotUsers.push name
    for a in used do
      unless axs.contains a do axs := axs.push a
  IO.println s!"AUDIT|declarations={total}|theorems={theorems}|unsafe={unsafeDecls}|partial={partialDecls}|unsafe_rec={unsafeRec}|axioms={axs}|declarations_using_Quot.sound={quotUsers}"
LEAN_EOF
} > "$tmp/Audit.lean"

"${LEAN:-lean}" -DElab.async=false -Ddebug.skipKernelTC=false "$tmp/Audit.lean" | grep '^AUDIT|'
