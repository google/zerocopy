#!/usr/bin/env bash
# Runs every borrow-checker probe under several toolchain/edition/flag configurations.
# Output: one log per (probe, config) under $OUT, plus a TSV summary on stdout.
set -u
PROBES=/tmp/work/probes
OUT=/tmp/work/raw
mkdir -p "$OUT"
TMPO=$(mktemp -d /tmp/out)
trap 'rm -rf "$TMPO"' EXIT

run() { # name cfg -- command...
  local name=$1 cfg=$2; shift 2
  local log="$OUT/${name}__${cfg}.txt"
  { echo "\$ $*"; "$@" 2>&1; echo "exit=$?"; } > "$log"
  local code; code=$(tail -1 "$log" | sed 's/exit=//')
  local errs; errs=$(grep -oE '^(error|warning)(\[E[0-9]+\])?' "$log" | sort | uniq -c | tr -s ' ' | tr '\n' ';')
  printf '%s\t%s\t%s\t%s\n' "$name" "$cfg" "$code" "$errs"
}

check() { # toolchain-cmd edition extra... file
  :
}

for f in "$PROBES"/p*.rs; do
  n=$(basename "$f" .rs)
  case "$n" in
    p25_refcell_dynamic|p26_capture_analysis_dump) continue;;
  esac
  for ed in 2018 2021; do
    run "$n" "nightly-default-e$ed" rustc --edition $ed --crate-type lib --emit=metadata -o "$TMPO/x.rmeta" "$f"
    run "$n" "nightly-polonius-off-e$ed" rustc -Zpolonius=off --edition $ed --crate-type lib --emit=metadata -o "$TMPO/x.rmeta" "$f"
    run "$n" "stable-1.100.0-e$ed" rustup run 1.100.0 rustc --edition $ed --crate-type lib --emit=metadata -o "$TMPO/x.rmeta" "$f"
  done
  run "$n" "1.61.0-e2021" rustup run 1.61.0 rustc --edition 2021 --crate-type lib --emit=metadata -o "$TMPO/x.rmeta" "$f"
done
