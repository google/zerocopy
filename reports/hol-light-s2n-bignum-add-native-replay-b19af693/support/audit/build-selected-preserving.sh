#!/bin/bash
# PREPARATION ONLY. Not run. Parent must authorize new outputs and tool process.
# Owned replacement driver retaining upstream inliner/compiler/linker operations
# and flags, deliberately preserving intermediates rather than running rm.
set -eu
: "${TASK_HOL:?exact staged HOL root required}"
: "${TASK_S2N:?exact staged s2n root required}"
: "${TASK_HOL_OUT:?fresh /home/opam/anneal-cross-output required}"
test "$TASK_HOL_OUT" = /home/opam/anneal-cross-output
test -f "$TASK_HOL/hol_lib.cmxa"
test ! -d "$TASK_HOL/_opam"
test -f "$TASK_HOL_OUT/audit/AnnealDriver.ml"
test -f "$TASK_HOL_OUT/audit/AnnealSelectedAudit.ml"
test ! -e "$TASK_HOL_OUT/selected_inlined.ml"
test ! -e "$TASK_HOL_OUT/selected_inlined.cmx"
test ! -e "$TASK_HOL_OUT/selected.native"
export HOLLIGHT_DIR="$TASK_HOL"
export HOLLIGHT_LOAD_PATH=""
cd "$TASK_S2N"
ocaml "$TASK_HOL/inline_load.ml" \
  "$TASK_HOL_OUT/audit/AnnealDriver.ml" "$TASK_HOL_OUT/selected_inlined.ml"
OCAMLRUNPARAM=l=2000000000 \
  ocamlopt.byte -pp "$("$TASK_HOL/hol.sh" -pp)" \
  -I "$TASK_HOL" -I +unix -c hol_lib.cmxa \
  "$TASK_HOL_OUT/selected_inlined.ml" \
  -o "$TASK_HOL_OUT/selected_inlined.cmx" -w -a
ocamlfind ocamlopt -package zarith,unix -linkpkg hol_lib.cmxa \
  -I "$TASK_HOL" "$TASK_HOL_OUT/selected_inlined.cmx" \
  -o "$TASK_HOL_OUT/selected.native"
# Intentionally do not execute the resulting native proof program here.
# Parent/runner captures its own distinct status, full stdout and stderr.
