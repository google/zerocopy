#!/usr/bin/env bash
# Optional native Linux x86 stage; source/harness patches must be reviewed first.
set -euo pipefail
repo="$PWD"
evidence="$repo/validation-evidence/v1"
mkdir "$evidence"
work="$(mktemp -d "$RUNNER_TEMP/anneal-v1-validation.XXXXXX")"
archive="$(python3 - <<'PY'
import json
from pathlib import Path
report=json.loads(Path('validation-evidence/hashes.json').read_text())
assert report['validated'] and report['system']=='x86_64-linux'
archive=Path(report['archive_store'])
assert archive.is_file()
print(archive)
PY
)"
runtime="$repo/validation-relocated/bundle"
export PATH="$runtime/rust/bin:$PATH"
export LD_LIBRARY_PATH="$runtime/rust/lib:$runtime/lean/lib/lean"
export CARGO_HOME="$work/cargo-home" CARGO_TARGET_DIR="$work/cargo-target"
export CARGO_BUILD_JOBS=2 LEAN_NUM_THREADS=2 CARGO_INCREMENTAL=0
export CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0
export ANNEAL_TOOLCHAIN_DIR="$work/toolchain-base"
export ANNEAL_INTEGRATION_TARGET_DIR="$work/fixture-sandboxes"
export ANNEAL_INTEGRATION_REAL_JOBS=2
export ANNEAL_VALIDATION_OUTPUT_DIR="$evidence/fixture-outputs"
export ANNEAL_INTEGRATION_PROFILE="$evidence/fixtures-profile.jsonl"
unset BLESS ANNEAL_BLESS ANNEAL_KEEP_TEST_DIR KEEP_TEST_DIR
test ! -e "$ANNEAL_TOOLCHAIN_DIR"
mkdir -p "$ANNEAL_INTEGRATION_TARGET_DIR" "$CARGO_HOME"

check_disk() {
  python3 - "$repo" "$1" <<'PY'
import shutil, sys
assert shutil.disk_usage(sys.argv[1]).free >= int(sys.argv[2]) * 1024**3, 'Insufficient disk space for cold V1 validation'
PY
}
check_disk 17

run_stage() {
  local name="$1"
  shift
  local deadline
  case "$name" in
    fixtures) deadline=30m ;;
    units|build) deadline=15m ;;
    report) deadline=2m ;;
    *) deadline=10m ;;
  esac
  printf '%q ' "$@" > "$evidence/$name.command"
  printf '\n' >> "$evidence/$name.command"
  set +e
  timeout "$deadline" "$@" 2>&1 | tee "$evidence/$name.log"
  local results=("${PIPESTATUS[@]}")
  set -e
  printf '{"command_exit":%s,"log_exit":%s}\n' "${results[0]}" "${results[1]}" \
    > "$evidence/$name.status.json"
  if test "${results[1]}" -ne 0; then
    return "${results[1]}"
  fi
  return "${results[0]}"
}

manifest="$repo/anneal/v1/Cargo.toml"
run_stage fetch cargo fetch --manifest-path "$manifest" --locked --target x86_64-unknown-linux-gnu
result=0
run_stage units cargo test --manifest-path "$manifest" --locked --offline --bin cargo-anneal || result=$?
run_stage build cargo build --manifest-path "$manifest" --locked --offline --bin cargo-anneal
binary="$CARGO_TARGET_DIR/debug/cargo-anneal"
run_stage setup "$binary" setup --local-archive "$archive"
check_disk 10
installed_bin="$("$binary" toolchain-path)"
installed="$(dirname "$(dirname "$installed_bin")")"
test -x "$installed/rust/bin/rustc"
test -x "$installed/aeneas/bin/charon"
test -x "$installed/lean/bin/lake"
export PATH="$installed/rust/bin:$installed/lean/bin:$PATH"
export LD_LIBRARY_PATH="$installed/rust/lib:$installed/lean/lib/lean"
if test "${ANNEAL_VALIDATION_BLESS_REVIEWED:-}" = 1; then
  export ANNEAL_VALIDATION_OUTPUT_DIR="$evidence/bless-outputs"
  export ANNEAL_INTEGRATION_PROFILE="$evidence/bless-profile.jsonl"
  # Each selected fixture was reviewed against the first native x86 probe.
  # Expand also checks its later Aeneas-only output; its headers were reviewed.
  for fixture in cfg_blind_spot edge_cases_cfg/test_7_1_phantom_fn \
    edge_cases_cfg/test_7_3_ghost_spec edge_cases_charon/test_8_2_unions \
    expand_output extern_never_verified raw_ptr_dst_layout split_artifact \
    target_selection ui_silent_panic unions weird_functions; do
    BLESS=1 run_stage "bless-${fixture//\//-}" cargo test --manifest-path "$manifest" \
      --locked --offline --test integration -- --test-threads=4 --nocapture --exact \
      "run_integration_test::$fixture/anneal.toml"
  done
  python3 - "$repo" "$evidence" <<'PY'
from pathlib import Path
import json, subprocess, sys
repo, evidence = map(Path, sys.argv[1:])
expected = {
    'cfg_blind_spot/expected.stderr',
    'edge_cases_cfg/test_7_1_phantom_fn/expected.stderr',
    'edge_cases_cfg/test_7_3_ghost_spec/expected.stderr',
    'edge_cases_charon/test_8_2_unions/expected.stderr',
    'expand_output/expected-all.stdout', 'expand_output/expected-aeneas.stdout',
    'extern_never_verified/out.txt', 'raw_ptr_dst_layout/expected.stderr',
    'split_artifact/expected.stderr', 'target_selection/expected.stderr',
    'ui_silent_panic/expected.stderr', 'unions/expected.stderr',
    'weird_functions/expected.stderr',
}
prefix = 'anneal/v1/tests/fixtures/'
paths = subprocess.check_output(['git', 'diff', '--name-only', '--', prefix], cwd=repo, text=True).splitlines()
assert set(paths) == {prefix + path for path in expected}, paths
patch = subprocess.check_output(['git', 'diff', '--', prefix], cwd=repo)
(evidence / 'harness-blessed-snapshots.patch').write_bytes(patch)
commands = [json.loads(line) for line in (evidence / 'bless-profile.jsonl').read_text().splitlines()]
assert sum(event.get('event') == 'command' for event in commands) == 14
PY
  export ANNEAL_VALIDATION_OUTPUT_DIR="$evidence/fixture-outputs"
  export ANNEAL_INTEGRATION_PROFILE="$evidence/fixtures-profile.jsonl"
fi
unset BLESS ANNEAL_BLESS
run_stage fixtures cargo test --manifest-path "$manifest" --locked --offline --test integration \
  -- --test-threads=4 --nocapture || result=$?
export CARGO_TARGET_DIR="$work/control-target"
for control in ordinary-success ordinary-false-post; do
  control_dir="$work/$control"
  mkdir -p "$control_dir/src"
  package="${control//-/_}"
  printf '[package]\nname="%s"\nversion="0.1.0"\nedition="2024"\n[workspace]\n' \
    "$package" > "$control_dir/Cargo.toml"
  ensures='ret = x'
  if test "$control" = ordinary-false-post; then ensures='ret ≠ x'; fi
  printf '/// ```lean, anneal\n/// ensures:\n///   %s\n/// proof:\n///   simp_all [identity]\n/// ```\npub fn identity(x: u32) -> u32 { x }\n' \
    "$ensures" > "$control_dir/src/lib.rs"
  status=0
  (cd "$control_dir"; run_stage "$control" "$binary" verify) || status=$?
  if test "$control" = ordinary-success && test "$status" -ne 0; then result=1; fi
  if test "$control" = ordinary-false-post; then
    if test "$status" -eq 0; then result=1; fi
    python3 - "$evidence/$control.log" <<'PY' || result=1
import sys
from pathlib import Path
log=Path(sys.argv[1]).read_text()
assert all(text in log for text in ['unsolved goals','False','Lean verification failed'])
PY
  fi
done
python3 - "$CARGO_TARGET_DIR" "$evidence/controls-generated" <<'PY' || result=1
import shutil,sys
from pathlib import Path
root,destination=map(Path,sys.argv[1:])
files=[p for p in root.rglob('*') if p.is_file() and p.suffix in ['.lean','.llbc']]
assert len(files)<=500 and sum(p.stat().st_size for p in files)<=50*1024**2
assert any(p.suffix=='.lean' for p in files) and any(p.suffix=='.llbc' for p in files)
for source in files:
    target=destination/source.relative_to(root)
    target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,target)
PY
# This helper reads exact harness sidecars; it must neither bless nor normalize.
run_stage report python3 "$repo/ci/validate-anneal-v1-report.py" "$repo" "$evidence" || result=$?
printf '{"validated":%s,"stage_exit":%s}\n' "$([ "$result" -eq 0 ] && echo true || echo false)" \
  "$result" > "$evidence/stage-status.json"
exit "$result"
