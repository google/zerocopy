#!/bin/bash
if [ "$#" -ne 2 ]; then
  echo "../tools/run-proof.sh <.native file to run> <output log path>"
  echo "This script runs precompiled HOL Light proof '<.native file>', prints the output"
  echo "at <output log path>, and inspects the log file to check whether all proofs "
  echo "are done successfully."
  exit 1
fi

# Return the exit code if any statement fails
set -e

s2n_bignum_arch=$(basename "$(pwd)")

cd ..

native_path=${s2n_bignum_arch}/$1
output_path=${s2n_bignum_arch}/$2

"$native_path" 2>&1 > "$output_path"

# Revert the exit code option since 'grep' may return non-zero.
set +e

grep -i "error:\|exception:" "$output_path"
if [ $? -eq 0 ]; then
  echo "${s2n_bignum_arch}/${native_path} had error(s)"
  exit 1
fi
