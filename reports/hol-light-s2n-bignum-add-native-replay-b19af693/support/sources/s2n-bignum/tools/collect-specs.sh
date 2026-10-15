#!/bin/bash
if [ "$#" -ne 1 ] && [ "$#" -ne 2 ]; then
  echo "collect-specs.sh <dir (e.g., arm)> <.ml path (optional)>"
  echo "This script collects the names of HOL Light theorems that are"
  echo "specifications of correctness of assembly functions."
  exit 1
fi

s2n_bignum_arch=$1
if [ "$#" -eq 2 ]; then
  filepat="$2"
else
  filepat="*/*.ml"
fi
cd $s2n_bignum_arch > /dev/null

# An env. var for sorting
export LC_ALL=C
tmpfile=$(mktemp)
grep 'let [A-Z_0-9]*_SUBROUTINE_CORRECT' ${filepat} | cut -f2 -d' ' >$tmpfile
grep 'let [A-Z_0-9]*_SUBROUTINE_SAFE' ${filepat} | cut -f2 -d' ' >>$tmpfile
cat $tmpfile | sort
