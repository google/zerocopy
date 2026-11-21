#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Run `cargo-kani` either directly (`KANI_SHARD=1/1`) or across deterministic,
# lossless harness shards (`KANI_SHARD=<k>/<n>`).
#
# When `n > 1`, this wrapper discovers the full set of `#[kani::proof]` and
# `#[kani::proof_for_contract]` harnesses via `cargo-kani ... list --format
# json`, places known slow solver harnesses first so they distribute evenly
# across shards, selects index `i % n == k - 1`, inserts `--exact --harness <h>`
# before any `--cbmc-args` boundary, and verifies that Kani's summary reports
# the exact expected verified count with zero failures.

set -euo pipefail

SHARD_SPEC="${KANI_SHARD:-1/1}"
if [[ ! "$SHARD_SPEC" =~ ^([1-9][0-9]*)/([1-9][0-9]*)$ ]]; then
  echo "error: invalid KANI_SHARD='$SHARD_SPEC' (expected '<k>/<n>')" >&2
  exit 2
fi
SHARD_NUM="${BASH_REMATCH[1]}"
SHARD_TOTAL="${BASH_REMATCH[2]}"
if (( SHARD_NUM > SHARD_TOTAL )); then
  echo "error: shard index $SHARD_NUM exceeds shard count $SHARD_TOTAL" >&2
  exit 2
fi

if (( SHARD_TOTAL == 1 )); then
  exec cargo-kani "$@"
fi

DISCOVERY_CARGO_ARGS=()
USER_Z_VALS=(unstable-options function-contracts)
USER_Z_ARGS=(-Z unstable-options -Z function-contracts)
HAS_Z_LIST=0
RAW_MANIFEST_PATH=""
args=("$@")
cbmc_idx="${#args[@]}"

add_user_z_arg() {
  local val="$1"
  if [[ "$val" == "list" ]]; then
    HAS_Z_LIST=1
  fi
  local existing
  for existing in "${USER_Z_VALS[@]}"; do
    if [[ "$existing" == "$val" ]]; then
      return 0
    fi
  done
  USER_Z_VALS+=("$val")
  USER_Z_ARGS+=(-Z "$val")
}

i=0
while (( i < ${#args[@]} )); do
  arg="${args[$i]}"
  case "$arg" in
    autoharness|list|playback|--only-codegen|--no-codegen|--harness|--harness=*|--exact)
      echo "error: '$arg' cannot be combined with KANI_SHARD=$SHARD_SPEC" >&2
      exit 2
      ;;
    --manifest-path)
      if (( i + 1 >= ${#args[@]} )) || [[ -z "${args[$((i + 1))]}" ]]; then
        echo "error: missing or empty value after '$arg'" >&2
        exit 2
      fi
      if [[ -n "$RAW_MANIFEST_PATH" ]]; then
        echo "error: duplicate '--manifest-path' argument" >&2
        exit 2
      fi
      RAW_MANIFEST_PATH="${args[$((i + 1))]}"
      i=$((i + 2))
      continue
      ;;
    --manifest-path=*)
      raw_path="${arg#*=}"
      if [[ -z "$raw_path" ]]; then
        echo "error: empty value in '$arg'" >&2
        exit 2
      fi
      if [[ -n "$RAW_MANIFEST_PATH" ]]; then
        echo "error: duplicate '--manifest-path' argument" >&2
        exit 2
      fi
      RAW_MANIFEST_PATH="$raw_path"
      ;;
    --package|-p|--exclude|-e|--bin)
      if (( i + 1 >= ${#args[@]} )) || [[ -z "${args[$((i + 1))]}" ]]; then
        echo "error: missing or empty value after '$arg'" >&2
        exit 2
      fi
      DISCOVERY_CARGO_ARGS+=("$arg" "${args[$((i + 1))]}")
      i=$((i + 2))
      continue
      ;;
    --features|-F)
      if (( i + 1 >= ${#args[@]} )); then
        echo "error: missing value after '$arg'" >&2
        exit 2
      fi
      DISCOVERY_CARGO_ARGS+=("$arg" "${args[$((i + 1))]}")
      i=$((i + 2))
      continue
      ;;
    --package=*|--exclude=*|--bin=*)
      if [[ -z "${arg#*=}" ]]; then
        echo "error: empty value in '$arg'" >&2
        exit 2
      fi
      DISCOVERY_CARGO_ARGS+=("$arg")
      ;;
    -p*|--features=*|-F*|-e*|--no-default-features|--all-features|--workspace|--lib|--bins|--tests)
      DISCOVERY_CARGO_ARGS+=("$arg")
      ;;
    -Z|--unstable)
      if (( i + 1 >= ${#args[@]} )) || [[ -z "${args[$((i + 1))]}" ]]; then
        echo "error: missing or empty value after '$arg'" >&2
        exit 2
      fi
      add_user_z_arg "${args[$((i + 1))]}"
      i=$((i + 2))
      continue
      ;;
    -Z*|--unstable=*)
      if [[ "$arg" == --unstable=* ]]; then
        z_val="${arg#--unstable=}"
      else
        z_val="${arg#-Z}"
      fi
      if [[ -z "$z_val" ]]; then
        echo "error: empty value in '$arg'" >&2
        exit 2
      fi
      add_user_z_arg "$z_val"
      ;;
    # Verification-only value-taking options (validated here and preserved in
    # VERIFY_KANI_ARGS, but omitted from `cargo-kani list` discovery — notably
    # `--target-dir`, which newer Kani `list` releases reject per Kani #5123).
    --concrete-playback|--default-unwind|--harness-timeout|--output-format|--solver|--target-dir|--unwind)
      if (( i + 1 >= ${#args[@]} )) || [[ -z "${args[$((i + 1))]}" ]]; then
        echo "error: missing or empty value after '$arg'" >&2
        exit 2
      fi
      i=$((i + 2))
      continue
      ;;
    --concrete-playback=*|--default-unwind=*|--harness-timeout=*|--output-format=*|--solver=*|--target-dir=*|--unwind=*)
      if [[ -z "${arg#*=}" ]]; then
        echo "error: empty value in '$arg'" >&2
        exit 2
      fi
      ;;
    -j|--jobs|--randomize-layout)
      if (( i + 1 < ${#args[@]} )) && [[ "${args[$((i + 1))]}" != -* ]]; then
        i=$((i + 2))
        continue
      fi
      ;;
    --cbmc-args)
      cbmc_idx="$i"
      break
      ;;
    --jobs=*|-j[0-9]*|--randomize-layout=*|--memory-safety-checks|--no-memory-safety-checks|--overflow-checks|--no-overflow-checks|--undefined-function-checks|--no-undefined-function-checks|--unwinding-checks|--no-unwinding-checks|--default-checks|--no-default-checks|--extra-pointer-checks|--fail-fast|--force-build|--gen-c|--ignore-global-asm|--keep-temps|--no-assert-contracts|--no-assertion-reach-checks|--no-restrict-vtable|--no-slice-formula|--output-into-files|--prove-safety-only|--run-sanity-checks|--synthesize-loop-contracts|--coverage|--debug|-q|--quiet|-v|--verbose)
      ;;
    *)
      echo "error: unsupported argument '$arg' for sharded Kani discovery" >&2
      exit 2
      ;;
  esac
  i=$((i + 1))
done

VERIFY_KANI_ARGS=("${args[@]:0:$cbmc_idx}")
VERIFY_CBMC_ARGS=("${args[@]:$cbmc_idx}")

ORIG_PWD="$PWD"
if [[ -n "$RAW_MANIFEST_PATH" ]]; then
  MANIFEST_PATH="$(python3 -I -B -c 'import os, sys; print(os.path.abspath(sys.argv[1]))' "$RAW_MANIFEST_PATH")"
else
  MANIFEST_PATH="$(cargo locate-project --message-format plain)"
fi
DISCOVERY_CARGO_ARGS=(--manifest-path "$MANIFEST_PATH" "${DISCOVERY_CARGO_ARGS[@]}")

WORK_DIR="$(mktemp -d)"
CLEANUP_NEW_LIST_FILES=()
cleanup() {
  if (( ${#CLEANUP_NEW_LIST_FILES[@]} > 0 )); then
    rm -f -- "${CLEANUP_NEW_LIST_FILES[@]}"
  fi
  rm -rf -- "$WORK_DIR"
}
trap cleanup EXIT

# Snapshot candidate `kani-list.json` locations outside `$WORK_DIR` that do not
# exist yet before discovery runs. Newer Kani releases can write
# `kani-list.json` into the package root rather than cwd (Kani #5124); tracking
# non-pre-existing candidates lets us locate silent outputs without reading
# stale files and clean up newly created files without touching pre-existing
# ones.
python3 -I -B - "$MANIFEST_PATH" "$ORIG_PWD" "$WORK_DIR/cleanup_candidates.bin" <<'PY'
import json
import os
from pathlib import Path
import subprocess
import sys

manifest_path = Path(sys.argv[1])
orig_pwd = Path(sys.argv[2])
out_path = Path(sys.argv[3])

candidate_dirs: list[Path] = [manifest_path.parent, orig_pwd]
try:
    proc = subprocess.run(
        [
            "cargo",
            "metadata",
            "--no-deps",
            "--format-version",
            "1",
            "--manifest-path",
            str(manifest_path),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode == 0 and proc.stdout.strip():
        meta = json.loads(proc.stdout)
        ws_root = meta.get("workspace_root")
        if isinstance(ws_root, str) and ws_root:
            candidate_dirs.append(Path(ws_root))
        for pkg in meta.get("packages", []):
            mp = pkg.get("manifest_path")
            if isinstance(mp, str) and mp:
                candidate_dirs.append(Path(mp).parent)
except (OSError, ValueError):
    pass

new_candidates: list[str] = []
seen: set[str] = set()
for d in candidate_dirs:
    canon_dir = os.path.realpath(str(d))
    p = Path(canon_dir) / "kani-list.json"
    key = str(p)
    if key in seen:
        continue
    seen.add(key)
    if not p.exists() and not p.is_symlink():
        new_candidates.append(key)

out_path.write_bytes(b"".join(c.encode("utf-8") + b"\x00" for c in new_candidates))
PY
mapfile -d '' -t CLEANUP_NEW_LIST_FILES < "$WORK_DIR/cleanup_candidates.bin"

# Kani 0.60 requires `-Z list` for `cargo-kani list`, whereas newer Kani
# releases stabilized `list` and removed `-Z list`. Probe dynamically so
# automated Kani version rolls continue to work without script changes.
LIST_Z_ARGS=()
if (( HAS_Z_LIST == 0 )) && cargo-kani -Z list --version >/dev/null 2>&1; then
  LIST_Z_ARGS=(-Z list)
fi

list_rc=0
(
  cd "$WORK_DIR"
  cargo-kani "${DISCOVERY_CARGO_ARGS[@]}" list \
    "${USER_Z_ARGS[@]}" "${LIST_Z_ARGS[@]}" \
    --format json
) 2>&1 | tee "$WORK_DIR/list.log" || list_rc=$?
if [[ "$list_rc" -ne 0 ]]; then
  exit "$list_rc"
fi

SUMMARY_LINE="$(
  python3 -I -B - \
    "$WORK_DIR" \
    "$WORK_DIR/list.log" \
    "$WORK_DIR/cleanup_candidates.bin" \
    "$SHARD_NUM" \
    "$SHARD_TOTAL" \
    "$WORK_DIR/shard.bin" <<'PY'
import json
import os
from pathlib import Path
import re
import sys

work_dir = Path(sys.argv[1])
list_log_path = Path(sys.argv[2])
candidates_path = Path(sys.argv[3])
shard_num = int(sys.argv[4])
shard_total = int(sys.argv[5])
out_path = Path(sys.argv[6])

ANSI_RE = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")
WROTE_RE = re.compile(r"^Wrote list results to (.+)$", flags=re.MULTILINE)


def resolve_list_path() -> Path:
    log_text = list_log_path.read_text(encoding="utf-8", errors="replace")
    clean = ANSI_RE.sub("", log_text).replace("\r\n", "\n").replace("\r", "\n")
    announced: list[Path] = []
    seen_resolved: set[str] = set()
    for match in WROTE_RE.finditer(clean):
        raw = match.group(1).strip()
        if not raw:
            continue
        p = Path(raw)
        if not p.is_absolute():
            p = work_dir / p
        canon = str(p.resolve()) if p.exists() else os.path.abspath(str(p))
        if canon not in seen_resolved:
            seen_resolved.add(canon)
            announced.append(p)
    if len(announced) > 1:
        raise SystemExit(
            f"ambiguous kani-list.json paths in list output: {[str(p) for p in announced]}"
        )
    if len(announced) == 1:
        target = announced[0]
        if not target.is_file():
            raise SystemExit(
                f"announced kani-list.json path does not exist: {target}"
            )
        return target

    work_default = work_dir / "kani-list.json"
    if work_default.is_file():
        return work_default

    raw_cands = candidates_path.read_bytes().split(b"\x00")
    newly_created: list[Path] = []
    seen_new: set[str] = set()
    for c in raw_cands:
        if not c:
            continue
        p = Path(c.decode("utf-8"))
        if not p.is_file():
            continue
        canon = str(p.resolve())
        if canon not in seen_new:
            seen_new.add(canon)
            newly_created.append(p)
    if len(newly_created) == 1:
        return newly_created[0]
    if len(newly_created) > 1:
        raise SystemExit(
            "multiple newly created kani-list.json files found: "
            f"{[str(p) for p in newly_created]}"
        )
    raise SystemExit("could not locate kani-list.json after cargo-kani list")


def extract_harnesses(doc: dict, key: str) -> list[str]:
    if key not in doc:
        raise SystemExit(f"missing required key {key!r} in kani-list.json")
    raw = doc[key]
    harnesses: list[str] = []
    if isinstance(raw, dict):
        for file_name, names in raw.items():
            if not isinstance(file_name, str) or not isinstance(names, list):
                raise SystemExit(f"malformed map entry in {key!r}")
            if not all(isinstance(h, str) for h in names):
                raise SystemExit(f"non-string harness name in {key!r}")
            harnesses.extend(names)
        return harnesses
    if isinstance(raw, list):
        for entry in raw:
            if (
                not isinstance(entry, dict)
                or not isinstance(entry.get("file"), str)
                or not isinstance(entry.get("harnesses"), list)
            ):
                raise SystemExit(f"malformed record entry in {key!r}")
            names = entry["harnesses"]
            if not all(isinstance(h, str) for h in names):
                raise SystemExit(f"non-string harness name in {key!r}")
            harnesses.extend(names)
        return harnesses
    raise SystemExit(
        f"unsupported {key!r} shape in kani-list.json: {type(raw).__name__}"
    )


list_path = resolve_list_path()
data = json.loads(list_path.read_text(encoding="utf-8"))
if not isinstance(data, dict):
    raise SystemExit("kani-list.json top-level value must be a JSON object")

file_version = data.get("file-version")
if file_version != "0.1":
    raise SystemExit(
        f"unsupported kani-list.json file-version: {file_version!r} (expected '0.1')"
    )

std_list = extract_harnesses(data, "standard-harnesses")
con_list = extract_harnesses(data, "contract-harnesses")
totals = data.get("totals")
if not isinstance(totals, dict):
    raise SystemExit("missing or malformed 'totals' in kani-list.json")
exp_std = totals.get("standard-harnesses")
exp_con = totals.get("contract-harnesses")
if type(exp_std) is not int or type(exp_con) is not int:
    raise SystemExit(
        f"malformed harness totals in kani-list.json: ({exp_std!r}, {exp_con!r})"
    )

if len(std_list) != exp_std or len(con_list) != exp_con:
    raise SystemExit(
        f"kani-list totals mismatch: got ({len(std_list)}, {len(con_list)}), "
        f"expected ({exp_std}, {exp_con})"
    )

all_harnesses = sorted(set(std_list) | set(con_list))
if len(all_harnesses) != len(std_list) + len(con_list):
    raise SystemExit("duplicate harness names in kani-list.json")
if not all_harnesses:
    raise SystemExit("zero Kani harnesses discovered")
if any("\x00" in h or not h for h in all_harnesses):
    raise SystemExit("invalid empty or NUL-containing harness name")

# Order the heaviest solver harnesses first so round-robin assignment balances
# them evenly across shards. This is strictly a permutation of `all_harnesses`.
heavy_priority = {
    "layout::proofs::prove_dst_layout_extend_dst_panics": 0,
    "layout::proofs::prove_trailing_slice_layout_advance": 1,
    "layout::proofs::prove_dst_layout_pad_to_align_dst_outer_alignment_formula": 2,
    "layout::proofs::prove_max_trailing_bytes": 3,
}

def sort_key(name: str):
    if name in heavy_priority:
        return (0, heavy_priority[name], name)
    if name.startswith("layout::proofs::"):
        return (1, 0, name)
    return (2, 0, name)

ordered = sorted(all_harnesses, key=sort_key)
if len(ordered) != len(all_harnesses) or set(ordered) != set(all_harnesses):
    raise SystemExit("internal error: harness ordering is not a bijection")

selected = [
    h for idx, h in enumerate(ordered) if (idx % shard_total) == (shard_num - 1)
]
if not selected:
    raise SystemExit(
        f"shard {shard_num}/{shard_total} selected 0 of {len(ordered)} harnesses"
    )

out_path.write_bytes(b"".join(h.encode("utf-8") + b"\x00" for h in selected))
print(f"{len(selected)} {len(ordered)}")
PY
)"

read -r EXPECTED_SHARD_COUNT TOTAL_HARNESS_COUNT <<< "$SUMMARY_LINE"
mapfile -d '' -t SHARD_HARNESSES < "$WORK_DIR/shard.bin"
if [[ "${#SHARD_HARNESSES[@]}" -ne "$EXPECTED_SHARD_COUNT" || "$EXPECTED_SHARD_COUNT" -le 0 ]]; then
  echo "error: loaded ${#SHARD_HARNESSES[@]} harnesses, expected $EXPECTED_SHARD_COUNT" >&2
  exit 1
fi

msg="Running Kani shard $SHARD_NUM/$SHARD_TOTAL: $EXPECTED_SHARD_COUNT of $TOTAL_HARNESS_COUNT harnesses"
echo "$msg"
if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
  echo "$msg" >> "$GITHUB_STEP_SUMMARY"
fi

HARNESS_ARGS=(--exact)
for h in "${SHARD_HARNESSES[@]}"; do
  HARNESS_ARGS+=(--harness "$h")
done

kani_rc=0
cargo-kani "${VERIFY_KANI_ARGS[@]}" "${HARNESS_ARGS[@]}" "${VERIFY_CBMC_ARGS[@]}" \
  2>&1 | tee "$WORK_DIR/kani.log" || kani_rc=$?
if [[ "$kani_rc" -ne 0 ]]; then
  exit "$kani_rc"
fi

python3 -I -B - "$WORK_DIR/kani.log" "$EXPECTED_SHARD_COUNT" <<'PY'
from pathlib import Path
import re
import sys

log_text = Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
expected = int(sys.argv[2])
clean = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", log_text)
matches = re.findall(
    r"^Complete - (\d+) successfully verified harnesses, (\d+) failures, (\d+) total\.\s*$",
    clean,
    flags=re.MULTILINE,
)
if len(matches) != 1:
    raise SystemExit(
        f"expected exactly one Kani completion summary, found {len(matches)}"
    )
verified, failed, total = (int(x) for x in matches[0])
if failed != 0 or verified != expected or total != expected:
    raise SystemExit(
        f"Kani summary mismatch: verified={verified}, failed={failed}, "
        f"total={total}, expected={expected}"
    )
PY
