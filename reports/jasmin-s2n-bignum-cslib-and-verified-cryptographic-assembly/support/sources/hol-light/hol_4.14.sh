#!/bin/bash

# Makefile will replace __DIR__ with the path
export HOLLIGHT_DIR=__DIR__
export HOLLIGHT_USE_MODULE=__USE_MODULE__

if [ "$#" -eq 1 ]; then
  if [ "$1" == "-pp" ]; then
    echo "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I \"${HOLLIGHT_DIR}\" pa_j.cmo"
    exit 0
  elif [ "$1" == "-dir" ]; then
    echo "${HOLLIGHT_DIR}"
    exit 0
  elif [ "$1" == "-use-module" ]; then
    echo "${HOLLIGHT_USE_MODULE}"
    exit 0
  fi
fi

# If a local OPAM is installed, use it
if [ -d "${HOLLIGHT_DIR}/_opam" ]; then
  eval $(opam env --switch "${HOLLIGHT_DIR}/" --set-switch)
fi

if [ "$#" -gt 1 ]; then
  if [ "$1" == "inline-load" ]; then
    # Do the inlining.
    shift
    ocaml ${HOLLIGHT_DIR}/inline_load.ml $@
    exit $?

  elif [ "$1" == "compile" ]; then
    # Native-compile the source code using ocamlopt.
    shift
    OCAMLRUNPARAM=l=2000000000 ocamlopt.byte \
        -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I \"${HOLLIGHT_DIR}\" pa_j.cmo" \
        -I "${HOLLIGHT_DIR}" -I +unix -c \
        hol_lib.cmxa $@
    exit $?

  elif [ "$1" == "link" ]; then
    # Link the native module
    shift
    ocamlfind ocamlopt -package zarith,unix -linkpkg hol_lib.cmxa \
        -I "${HOLLIGHT_DIR}" $@
    exit $?

  fi
fi

# The default ocaml REPL does not accept arrow keys.
# Export LINE_EDITOR to a proper program to enable this before invoking this
# script. If not set, ledit will be used.
if [ "${LINE_EDITOR}" == "" ]; then
  LINE_EDITOR="ledit"
fi

# If a custom hol.ml is given, use it. This variable is used by make-checkpoint.sh .
if [ "${HOL_ML_PATH}" == "" ]; then
  HOL_ML_PATH="${HOLLIGHT_DIR}/hol.ml"
fi

${LINE_EDITOR} ${HOLLIGHT_DIR}/ocaml-hol -init ${HOL_ML_PATH} -I ${HOLLIGHT_DIR}
