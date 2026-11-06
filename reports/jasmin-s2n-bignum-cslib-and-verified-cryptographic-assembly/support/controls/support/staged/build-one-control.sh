#!/bin/bash
# PREPARATION ONLY. Not staged/run. Fresh reviewed controls output only.
# Reuses existing exact HOL module, inliner, preprocessor/compiler/linker.
set -eu
: "${TASK_HOL:?required}"
: "${TASK_S2N:?required}"
: "${CTRL_ROOT:?required}"
test "$CTRL_ROOT" = /home/opam/anneal-cross-output/controls
case "$1" in
  ImporterControl|ArithmeticObservation|AxiomPolicyNegative) control_name="$1" ;;
  *) exit 2 ;;
esac
test -f "$TASK_HOL/hol_lib.cmxa"
test ! -d "$TASK_HOL/_opam"
test -f "$CTRL_ROOT/source/$control_name.ml"
test ! -e "$CTRL_ROOT/${control_name}_inlined.ml"
test ! -e "$CTRL_ROOT/${control_name}_inlined.cmx"
test ! -e "$CTRL_ROOT/$control_name.native"
export HOLLIGHT_DIR="$TASK_HOL" HOLLIGHT_LOAD_PATH=""
cd "$TASK_S2N"
ocaml "$TASK_HOL/inline_load.ml" \
  "$CTRL_ROOT/source/$control_name.ml" "$CTRL_ROOT/${control_name}_inlined.ml"
OCAMLRUNPARAM=l=2000000000 ocamlopt.byte \
  -pp "$("$TASK_HOL/hol.sh" -pp)" -I "$TASK_HOL" -I +unix -c hol_lib.cmxa \
  "$CTRL_ROOT/${control_name}_inlined.ml" -o "$CTRL_ROOT/${control_name}_inlined.cmx" -w -a
ocamlfind ocamlopt -package zarith,unix -linkpkg hol_lib.cmxa \
  -I "$TASK_HOL" "$CTRL_ROOT/${control_name}_inlined.cmx" \
  -o "$CTRL_ROOT/$control_name.native"
# No cleanup and no native execution in this producer.
