#!/usr/bin/env bash
# Usage: run.sh <file.lean> [extra lean args...]
# Runs Lean v4.34.1 on one standalone probe with trust level 0 (-t0) and a Lean memory limit
# (-M${LEANMEM:-2048} MiB), recording wall time and peak RSS via /usr/bin/time -v.
# Output goes to <file>.out next to the probe.
#   LEAN     : path to the lean binary (default: elan's v4.34.1 toolchain)
#   LEANMEM  : value for lean -M in MiB (default 2048; A4/A5 were run with LEANMEM=5000)
#   WRAP     : optional resource-limiting wrapper prefix. The recorded outputs were produced under
#              `anneal-lean-run --mode file --memory-max-mb 6144 --timeout 600 --` (a cgroup
#              memory/time wrapper); any equivalent limit, or none, reproduces the results.
set -u
F="$1"; shift
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean}"
if [ -z "${WRAP+x}" ]; then
  if [ -x "$HOME/.local/bin/anneal-lean-run" ]; then
    WRAP="$HOME/.local/bin/anneal-lean-run --mode file --memory-max-mb 6144 --timeout 600 --"
  else
    WRAP=""
  fi
fi
OUT="${F%.lean}.out"
cd "$(dirname "$F")"
{
  echo "# cmd: $WRAP /usr/bin/time -v $LEAN -t0 -M${LEANMEM:-2048} $* $(basename "$F")"
  $WRAP /usr/bin/time -v "$LEAN" -t0 -M"${LEANMEM:-2048}" "$@" "$(basename "$F")" \
    2> >(grep -E 'Elapsed|Maximum resident|Exit status' >&2)
  echo "# exit: $?"
} > "$OUT" 2>&1
cat "$OUT"
