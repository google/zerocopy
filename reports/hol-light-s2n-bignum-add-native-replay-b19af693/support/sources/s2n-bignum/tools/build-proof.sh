#!/bin/bash
if [ "$#" -ne 3 ]; then
  echo "../tools/build-proof.sh <.ml file path> <hol.sh> <output .native path>"
  echo "This script builds HOL Light proof using OCaml native compiler and puts the "
  echo "output binary at <output .native path>."
  exit 1
fi

# Return the exit code if any statement fails
set -e

s2n_bignum_arch=$(basename "$(pwd)")

cd ..

ml_path_noarch=$1
ml_path=${s2n_bignum_arch}/${ml_path_noarch}
hol_sh_cmd=$2
output_path=${s2n_bignum_arch}/$3

export HOLLIGHT_DIR="$(dirname ${hol_sh_cmd})"
if [ ! -f "${HOLLIGHT_DIR}/hol_lib.cmxa" ]; then
  echo "hol_lib.cmxa does not exist in HOLLIGHT_DIR('${HOLLIGHT_DIR}')."
  echo "Did you compile HOL Light with HOLLIGHT_USE_MODULE set to 1?"
  exit 1
fi


template_ml="$(mktemp).ml"
echo "Generating a template .ml that loads the file...: ${template_ml}"

(echo 'let s2n_bignum_build_proof_start_time = Unix.time();;'; \
 echo "loadt \"${ml_path}\";;"; \
 echo "check_axioms ();;") >> ${template_ml}

spec_found=0
for spec in $(./tools/collect-specs.sh ${s2n_bignum_arch} ${ml_path_noarch}) ; do
  echo "Printf.printf \"val ${spec} : thm = %s\n\" (string_of_thm ${spec});;"
  spec_found=1
done >> ${template_ml}

(echo 'let s2n_bignum_build_proof_end_time = Unix.time();;'; \
 echo 'Printf.printf "Running time: %f sec, Start unixtime: %f, End unixtime: %f\n" (s2n_bignum_build_proof_end_time -. s2n_bignum_build_proof_start_time) s2n_bignum_build_proof_start_time s2n_bignum_build_proof_end_time;;') >> ${template_ml}


if [ -d "${HOLLIGHT_DIR}/_opam" ]; then
  # To use inline_load.ml ... If OCaml version is too old, otherwise, a few String functions fail.
  eval $(opam env --switch "${HOLLIGHT_DIR}/" --set-switch)
fi

inlined_prefix="$(mktemp)"
inlined_ml="${inlined_prefix}.ml"
inlined_cmx="${inlined_prefix}.cmx"
ocaml ${HOLLIGHT_DIR}/inline_load.ml ${template_ml} ${inlined_ml}

# Give a large stack size.
OCAMLRUNPARAM=l=2000000000 \
ocamlopt.byte -pp "$(${hol_sh_cmd} -pp)" -I "${HOLLIGHT_DIR}" -I +unix -c \
    hol_lib.cmxa ${inlined_ml} -o ${inlined_cmx} -w -a
ocamlfind ocamlopt -package zarith,unix -linkpkg hol_lib.cmxa \
    -I "${HOLLIGHT_DIR}" ${inlined_cmx} \
    -o "${output_path}"

# Remove the intermediate files to save disk space
rm ${inlined_cmx} ${template_ml} ${inlined_ml}
