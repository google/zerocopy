#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Run Miri tests in dynamically batched `cargo-miri runner` processes.
#
# `cargo miri nextest run` spawns a separate Miri interpreter process for every
# test case, paying full interpreter startup and MIR-loading overhead hundreds
# of times per job. This script uses `cargo miri nextest list` to build the
# exact same test binaries and discover the exact same active test set, then
# partitions those tests losslessly across `nproc` concurrent workers:
#
# - Host proc-macro test binaries run natively in one batch per binary (matching
#   `cargo-miri` / `nextest` behavior).
# - Known slow Miri tests run first as singletons (longest-processing-time
#   ordering) so they do not straggle at the tail; this list is purely an
#   ordering hint and can never exclude a test.
# - All remaining target tests run in batched `cargo-miri runner` processes.
#
# The script fails closed if zero tests are discovered, if the partition loses
# or duplicates any test, if any worker exits non-zero, or if the summed
# `libtest` pass count does not equal the discovered test count.

set -euo pipefail

usage() {
  echo "usage: $0 --toolchain <name> --package <pkg> --target <triple> [-- <cargo-args...>]" >&2
  exit 2
}

TOOLCHAIN=""
PACKAGE=""
TARGET=""
EXTRA_ARGS=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --toolchain)
      [[ $# -ge 2 ]] || usage
      TOOLCHAIN="$2"
      shift 2
      ;;
    --package)
      [[ $# -ge 2 ]] || usage
      PACKAGE="$2"
      shift 2
      ;;
    --target)
      [[ $# -ge 2 ]] || usage
      TARGET="$2"
      shift 2
      ;;
    --)
      shift
      EXTRA_ARGS=("$@")
      break
      ;;
    *)
      echo "error: unknown argument: $1" >&2
      usage
      ;;
  esac
done

if [[ -z "$TOOLCHAIN" || -z "$PACKAGE" || -z "$TARGET" ]]; then
  usage
fi

WORKERS="${MIRI_BATCH_WORKERS:-$(nproc)}"
if [[ ! "$WORKERS" =~ ^[1-9][0-9]*$ ]]; then
  echo "error: invalid worker count: $WORKERS" >&2
  exit 1
fi

for tool in jq rustup; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "error: required tool not found in PATH: $tool" >&2
    exit 1
  fi
done

if [[ ! -x ./cargo.sh ]]; then
  echo "error: expected executable ./cargo.sh in current directory ($PWD)" >&2
  exit 1
fi

pids=()
WORK_DIR="$(mktemp -d)"
cleanup() {
  if [[ ${#pids[@]} -gt 0 ]]; then
    kill "${pids[@]}" 2>/dev/null || true
  fi
  rm -rf -- "$WORK_DIR"
}
trap cleanup EXIT
mkdir -p "$WORK_DIR/results"

# Build the Miri sysroot and test binaries and list the exact active test set
# that `cargo miri nextest run --locked --ignore-default-filter` selects.
./cargo.sh +"$TOOLCHAIN" miri nextest list \
  --locked \
  --ignore-default-filter \
  --package "$PACKAGE" \
  --target "$TARGET" \
  "${EXTRA_ARGS[@]}" \
  --message-format json > "$WORK_DIR/list.json"

TC="$(./cargo.sh --version "$TOOLCHAIN")"
CARGO_MIRI="$(env -u RUSTUP_TOOLCHAIN rustup which --toolchain "$TC" cargo-miri)"
# Query the sysroot through `./cargo.sh` so `RUSTFLAGS` match `miri nextest
# list` above and `cargo miri setup` reuses the just-built sysroot.
MIRI_SYSROOT="$(./cargo.sh +"$TOOLCHAIN" miri setup --print-sysroot --target "$TARGET")"
RUSTC_SYSROOT="$(env -u RUSTUP_TOOLCHAIN rustup run "$TC" rustc --print sysroot)"
TARGET_LIBDIR="$(env -u RUSTUP_TOOLCHAIN rustup run "$TC" rustc --print target-libdir)"
HOST_LIBS="${RUSTC_SYSROOT}/lib:${TARGET_LIBDIR}"

if [[ -z "$TC" || ! -x "$CARGO_MIRI" || ! -d "$MIRI_SYSROOT" \
  || ! -d "$RUSTC_SYSROOT" || ! -d "$TARGET_LIBDIR" ]]; then
  echo "error: failed to resolve Miri toolchain paths (tc='$TC', cargo_miri='$CARGO_MIRI', sysroot='$MIRI_SYSROOT')" >&2
  exit 1
fi

DEFAULT_CWD="$PWD"

# Partition every non-ignored test case losslessly into execution buckets.
# `is_heavy` is strictly a scheduling hint: every active test goes into either
# `heavy` or `fast` (its exact complement), never dropped.
jq -n \
  --slurpfile listing "$WORK_DIR/list.json" \
  --argjson workers "$WORKERS" \
  --arg default_cwd "$DEFAULT_CWD" '
  def is_heavy:
    startswith("pointer::ptr::tests::test_ptr_try_cast_into_soundness::")
    or . == "layout::tests::test_normalized_size_bounds"
    or . == "layout::tests::test_validate_rust_layout"
    or . == "layout::tests::test_trailing_slice_layout_normal_form";

  def heavy_rank:
    if (contains("u64") or contains("i64") or contains("f64") or contains("AU64")
        or . == "layout::tests::test_normalized_size_bounds"
        or . == "layout::tests::test_validate_rust_layout")
    then 0 else 1 end;

  ($listing[0]["rust-suites"] // error("missing rust-suites in nextest list"))
  | to_entries
  | sort_by(.key)
  | reduce .[] as $entry ({singletons: [], host: [], fast: []};
      (($entry.value.status // "listed") as $status
       | if $status != "listed" then
           error("unexpected suite status for \($entry.key): \($status)")
         else . end)
      | ($entry.value["build-platform"]) as $plat
      | if ($plat != "host" and $plat != "target") then
          error("unexpected build-platform: \($plat)")
        else . end
      | ($entry.value["binary-path"] // error("missing binary-path")) as $bin
      | ($entry.value.cwd // $default_cwd) as $cwd
      | if (([$entry.key, $bin, $cwd, $plat] | any(contains("\u0000") or contains("\t") or contains("\n") or contains("\r")))) then
          error("invalid control character in suite metadata for \($entry.key)")
        else . end
      | ([ $entry.value.testcases | to_entries[]
           | select((.value.ignored // false) == false)
           | if ((.value["filter-match"].status // "matches") != "matches") then
               error("unexpected filter mismatch on non-ignored test: \(.key)")
             elif (.key == "" or (.key | contains("\u0000")) or (.key | contains("\u001e")) or (.key | contains("\n")) or (.key | contains("\r"))) then
               error("invalid test name in suite \($entry.key)")
             else .key end ] | sort) as $active
      | if ($active | length) == 0 then
          .
        elif $plat == "host" then
          .host += [{
            suite: $entry.key,
            binary_path: $bin,
            cwd: $cwd,
            build_platform: $plat,
            tests: $active
          }]
        else
          ([ $active[] | select(is_heavy) ] | sort_by([heavy_rank, .])) as $heavy
          | [ $active[] | select(is_heavy | not) ] as $fast
          | .singletons += [ $heavy[] | {
              suite: $entry.key,
              binary_path: $bin,
              cwd: $cwd,
              build_platform: $plat,
              tests: [.]
            }]
          | if ($fast | length) == 0 then
              .
            else
              (if ($fast | length) >= ($workers * 12) then ($workers * 3)
               elif ($fast | length) >= ($workers * 4) then $workers
               else 1 end) as $nb
              | .fast += [
                  range(0; $nb) as $k
                  | [ range($k; ($fast | length); $nb) | $fast[.] ] as $chunk
                  | select(($chunk | length) > 0)
                  | {
                      suite: $entry.key,
                      binary_path: $bin,
                      cwd: $cwd,
                      build_platform: $plat,
                      tests: $chunk
                    }
                ]
            end
        end
    )
  | .singletons + .host + .fast
' > "$WORK_DIR/plan.json"

TOTAL_DISCOVERED="$(jq '[.["rust-suites"][].testcases | to_entries[] | select((.value.ignored // false) == false)] | length' "$WORK_DIR/list.json")"
TOTAL_PLANNED="$(jq '[.[].tests | length] | add // 0' "$WORK_DIR/plan.json")"
BUCKET_COUNT="$(jq 'length' "$WORK_DIR/plan.json")"

if [[ "$TOTAL_DISCOVERED" -le 0 ]]; then
  echo "::error::No Miri tests discovered for $PACKAGE / $TARGET"
  exit 1
fi

if [[ "$TOTAL_PLANNED" -ne "$TOTAL_DISCOVERED" ]]; then
  echo "::error::Miri partition count mismatch: discovered $TOTAL_DISCOVERED, planned $TOTAL_PLANNED"
  exit 1
fi

if ! jq -e '([.[] | .suite as $s | .tests[] | "\($s)\u0000\(.)"] | length == (unique | length))' "$WORK_DIR/plan.json" >/dev/null; then
  echo "::error::Miri partition contains duplicate (suite, test) entries"
  exit 1
fi

# Pre-materialize per-batch metadata and test lists in two single-pass `jq`
# calls rather than spawning `jq`/`grep`/`sed` subprocesses inside per-batch
# Bash loops.
mkdir -p "$WORK_DIR/buckets"
mapfile -t BUCKET_META < <(
  jq -r '.[] | [.suite, .binary_path, .cwd, .build_platform, (.tests | length | tostring)] | join("\t")' "$WORK_DIR/plan.json"
)
if [[ "${#BUCKET_META[@]}" -ne "$BUCKET_COUNT" ]]; then
  echo "error: bucket metadata count (${#BUCKET_META[@]}) != BUCKET_COUNT ($BUCKET_COUNT)" >&2
  exit 1
fi

{
  extract_idx=0
  while IFS= read -r -d $'\x1e' record; do
    printf '%s' "$record" > "$WORK_DIR/buckets/${extract_idx}.tests"
    extract_idx=$((extract_idx + 1))
  done
  if [[ "$extract_idx" -ne "$BUCKET_COUNT" ]]; then
    echo "error: extracted $extract_idx batch test lists, expected $BUCKET_COUNT" >&2
    exit 1
  fi
} < <(jq -j '.[] | (.tests | map(. + "\n") | add) + "\u001e"' "$WORK_DIR/plan.json")

summary_msg="Running $TOTAL_DISCOVERED Miri tests across $BUCKET_COUNT batches with $WORKERS workers"
echo "$summary_msg"
if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
  echo "$summary_msg" >> "$GITHUB_STEP_SUMMARY"
fi

run_bucket() {
  local idx="$1"
  local suite bin_path cwd build_platform expected log_file rc_file rc
  local -a tests

  IFS=$'\t' read -r suite bin_path cwd build_platform expected <<< "${BUCKET_META[$idx]}"
  mapfile -t tests < "$WORK_DIR/buckets/${idx}.tests"

  if [[ "${#tests[@]}" -ne "$expected" || "$expected" -le 0 ]]; then
    echo "error: failed to load test list for batch $idx (got ${#tests[@]}, expected $expected)" >&2
    exit 1
  fi

  log_file="$WORK_DIR/results/${idx}.log"
  rc_file="$WORK_DIR/results/${idx}.rc"
  rc=0

  # Run each batch with `--test-threads=1` so Miri does not simulate multiple
  # cooperative guest threads inside one interpreter process; concurrency comes
  # from running `WORKERS` independent processes in parallel.
  (
    cd "$cwd" || exit 1
    if [[ "$build_platform" == "host" ]]; then
      exec env \
        CARGO_MANIFEST_DIR="$cwd" \
        CARGO_PKG_NAME="$PACKAGE" \
        LD_LIBRARY_PATH="$HOST_LIBS${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
        "$bin_path" --color never --test-threads=1 --exact -- "${tests[@]}"
    else
      exec env \
        CARGO_MANIFEST_DIR="$cwd" \
        CARGO_PKG_NAME="$PACKAGE" \
        MIRI_SYSROOT="$MIRI_SYSROOT" \
        RUSTUP_TOOLCHAIN="$TC" \
        LD_LIBRARY_PATH="$HOST_LIBS${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
        "$CARGO_MIRI" runner "$bin_path" --color never --test-threads=1 --exact -- "${tests[@]}"
    fi
  ) >"$log_file" 2>&1 || rc=$?

  printf '%s\n' "$rc" > "$rc_file"
}

# Reap all workers before checking results so every failing batch log is
# reported. `|| true` on `wait` cannot mask failures: each batch's `.rc` file
# must exist and equal `0`, and its parsed `libtest` pass count must match.
active=0
for ((idx = 0; idx < BUCKET_COUNT; idx++)); do
  run_bucket "$idx" &
  pids+=("$!")
  active=$((active + 1))
  if (( active >= WORKERS )); then
    wait -n || true
    active=$((active - 1))
  fi
done
for pid in "${pids[@]}"; do
  wait "$pid" || true
done
pids=()

failures=0
total_passed=0

for ((idx = 0; idx < BUCKET_COUNT; idx++)); do
  IFS=$'\t' read -r suite _ _ _ expected <<< "${BUCKET_META[$idx]}"
  log_file="$WORK_DIR/results/${idx}.log"
  rc_file="$WORK_DIR/results/${idx}.rc"

  if [[ ! -f "$rc_file" ]]; then
    echo "::error::Miri batch $idx ($suite, $expected tests) terminated without writing exit status"
    if [[ -f "$log_file" ]]; then
      cat "$log_file"
    fi
    failures=1
    continue
  fi

  rc="$(<"$rc_file")"
  if [[ "$rc" != "0" ]]; then
    echo "::error::Miri batch $idx ($suite, $expected tests) failed with exit code $rc"
    cat "$log_file"
    failures=1
    continue
  fi

  line_count=0
  passed=""
  while IFS= read -r line; do
    if [[ "$line" =~ ^test\ result:\ ok\.\ ([0-9]+)\ passed\;\ 0\ failed\;\ 0\ ignored\;\ 0\ measured\;\ [0-9]+\ filtered\ out\; ]]; then
      line_count=$((line_count + 1))
      passed="${BASH_REMATCH[1]}"
    fi
  done < "$log_file"

  if [[ "$line_count" -ne 1 ]]; then
    echo "::error::Miri batch $idx ($suite) produced unexpected libtest summary (matches=$line_count)"
    cat "$log_file"
    failures=1
    continue
  fi

  if [[ -z "$passed" || "$passed" -ne "$expected" ]]; then
    echo "::error::Miri batch $idx ($suite) passed $passed tests, expected $expected"
    cat "$log_file"
    failures=1
    continue
  fi

  total_passed=$((total_passed + passed))
  echo "PASS [$((idx + 1))/$BUCKET_COUNT] $suite ($passed tests)"
done

if [[ "$failures" -ne 0 ]]; then
  exit 1
fi

if [[ "$total_passed" -ne "$TOTAL_DISCOVERED" ]]; then
  echo "::error::Miri total passed ($total_passed) != discovered ($TOTAL_DISCOVERED)"
  exit 1
fi

echo "All $total_passed Miri tests passed across $BUCKET_COUNT batches."
