#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZEROCOPY_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
WORKSPACE_ROOT="$(cd "$ZEROCOPY_ROOT/.." && pwd)"
if [[ -z "${PLAYGROUND_ROOT:-}" ]]; then
  PLAYGROUND_ROOT=""
  for candidate in \
    "$WORKSPACE_ROOT/rust-anneal-playground" \
    "$ZEROCOPY_ROOT/../rust-anneal-playground" \
    "$PWD/../rust-anneal-playground" \
    /usr/local/google/Projects/workspaces-open/*/rust-anneal-playground
  do
    if [[ -d "$candidate" ]]; then
      PLAYGROUND_ROOT="$candidate"
      break
    fi
  done
fi
ANNEAL_BIN="${ANNEAL_BIN:-$ZEROCOPY_ROOT/anneal/target/debug/cargo-anneal}"
RESULT_DIR="${RESULT_DIR:-$SCRIPT_DIR/results/$(date -u +%Y%m%dT%H%M%SZ)}"
VERIFY_TIMEOUT="${VERIFY_TIMEOUT:-180}"
RUN_FULL_PLAYGROUND="${RUN_FULL_PLAYGROUND:-1}"

if [[ ! -d "$PLAYGROUND_ROOT" ]]; then
  echo "PLAYGROUND_ROOT does not exist: $PLAYGROUND_ROOT" >&2
  echo "Clone https://github.com/platonicsock/rust-anneal-playground next to zerocopy, or set PLAYGROUND_ROOT." >&2
  exit 1
fi

if [[ ! -x "$ANNEAL_BIN" ]]; then
  cargo build --manifest-path "$ZEROCOPY_ROOT/anneal/Cargo.toml" --bin cargo-anneal
fi

if [[ -z "${ANNEAL_TOOLCHAIN_DIR:-}" ]]; then
  if [[ -d "$ZEROCOPY_ROOT/anneal/target/anneal-toolchain" ]]; then
    export ANNEAL_TOOLCHAIN_DIR="$ZEROCOPY_ROOT/anneal/target/anneal-toolchain"
  else
    echo "ANNEAL_TOOLCHAIN_DIR is not set and no local anneal/target/anneal-toolchain was found." >&2
    echo "Run cargo anneal setup first, or set ANNEAL_TOOLCHAIN_DIR to an installed toolchain parent." >&2
    exit 1
  fi
fi

mkdir -p "$RESULT_DIR"
WORK_DIR="$RESULT_DIR/work"
mkdir -p "$WORK_DIR"
TIMINGS="$RESULT_DIR/timings.tsv"
printf 'case\tstatus\telapsed_hms\telapsed_seconds\n' > "$TIMINGS"

write_checked_add() {
  local dst="$1"
  mkdir -p "$(dirname "$dst")"
  cat > "$dst" <<'RS'
/// Performs checked addition.
///
/// ```lean, anneal, spec
/// ensures: match ret with
///   | .none => (x : Int) + (y : Int) > I32.max \/ (x : Int) + (y : Int) < I32.min
///   | .some v => (v : Int) = (x : Int) + (y : Int)
/// proof (h_anon):
///   unfold checked_add at h_returns
///   have h := Aeneas.Std.I32.checked_add_bv_spec x y
///   simp_all [Aeneas.Std.I32.checked_add]
///   cases ret <;> simp_all <;> scalar_tac
/// proof (h_progress):
///   unfold checked_add
///   simp_all
/// ```
pub fn checked_add(x: i32, y: i32) -> Option<i32> {
    x.checked_add(y)
}

fn main() {}
RS
}

make_minimal_project() {
  local project="$1"
  mkdir -p "$project/src"
  cat > "$project/Cargo.toml" <<'TOML'
[package]
name = "playground"
version = "0.0.1"
edition = "2021"
TOML
  write_checked_add "$project/src/main.rs"
}

make_playground_project() {
  local project="$1"
  mkdir -p "$project/src"
  python3 - "$PLAYGROUND_ROOT/compiler/base/Cargo.toml" "$project/Cargo.toml" <<'PY'
import pathlib
import sys

src = pathlib.Path(sys.argv[1])
dst = pathlib.Path(sys.argv[2])
text = src.read_text()
package_header = text.split("[profile.dev]", 1)[0]
if "edition =" not in package_header:
    text = text.replace(
        'authors = ["The Rust Playground"]\n',
        'authors = ["The Rust Playground"]\nedition = "2021"\n',
        1,
    )
dst.write_text(text)
PY
  write_checked_add "$project/src/main.rs"
}

run_timed() {
  local name="$1"
  shift
  local stdout="$RESULT_DIR/$name.stdout"
  local stderr="$RESULT_DIR/$name.stderr"
  local timefile="$RESULT_DIR/$name.time"
  printf '%q ' "$@" > "$RESULT_DIR/$name.command"
  printf '\n' >> "$RESULT_DIR/$name.command"

  set +e
  /usr/bin/time -f 'elapsed_hms=%E
elapsed_seconds=%e' -o "$timefile" timeout "$VERIFY_TIMEOUT" "$@" >"$stdout" 2>"$stderr"
  local status=$?
  set -e

  local elapsed_hms elapsed_seconds
  elapsed_hms="$(sed -n 's/^elapsed_hms=//p' "$timefile" | tail -1)"
  elapsed_seconds="$(sed -n 's/^elapsed_seconds=//p' "$timefile" | tail -1)"
  printf '%s\t%s\t%s\t%s\n' "$name" "$status" "$elapsed_hms" "$elapsed_seconds" >> "$TIMINGS"
}

extract_trace_times() {
  local file="$1"
  if [[ -f "$file" ]]; then
    grep -E "Charon for|Aeneas for|'lake build' took" "$file" || true
  fi
}

minimal="$WORK_DIR/minimal"
playground="$WORK_DIR/playground"
make_minimal_project "$minimal"
make_playground_project "$playground"

run_timed metadata_minimal cargo metadata --format-version 1 --manifest-path "$minimal/Cargo.toml" --no-deps
run_timed minimal_generate env ANNEAL_TOOLCHAIN_DIR="$ANNEAL_TOOLCHAIN_DIR" RUST_LOG=trace "$ANNEAL_BIN" generate --manifest-path "$minimal/Cargo.toml"
run_timed minimal_verify_1 env ANNEAL_TOOLCHAIN_DIR="$ANNEAL_TOOLCHAIN_DIR" RUST_LOG=trace "$ANNEAL_BIN" verify --manifest-path "$minimal/Cargo.toml"
run_timed minimal_verify_2 env ANNEAL_TOOLCHAIN_DIR="$ANNEAL_TOOLCHAIN_DIR" RUST_LOG=trace "$ANNEAL_BIN" verify --manifest-path "$minimal/Cargo.toml"

if [[ "$RUN_FULL_PLAYGROUND" = "1" ]]; then
  run_timed metadata_playground cargo metadata --format-version 1 --manifest-path "$playground/Cargo.toml" --no-deps
  run_timed playground_generate_1 env ANNEAL_TOOLCHAIN_DIR="$ANNEAL_TOOLCHAIN_DIR" RUST_LOG=trace "$ANNEAL_BIN" generate --manifest-path "$playground/Cargo.toml"
  run_timed playground_generate_2 env ANNEAL_TOOLCHAIN_DIR="$ANNEAL_TOOLCHAIN_DIR" RUST_LOG=trace "$ANNEAL_BIN" generate --manifest-path "$playground/Cargo.toml"
  run_timed playground_verify_warm env ANNEAL_TOOLCHAIN_DIR="$ANNEAL_TOOLCHAIN_DIR" RUST_LOG=trace "$ANNEAL_BIN" verify --manifest-path "$playground/Cargo.toml"

  lean_root="$(find "$playground/target/anneal" -mindepth 2 -maxdepth 2 -type d -name lean | head -1 || true)"
  toolchain_root="$(find "$ANNEAL_TOOLCHAIN_DIR/.anneal/toolchain" -mindepth 1 -maxdepth 1 -type d | head -1 || true)"
  if [[ -n "$lean_root" && -n "$toolchain_root" ]]; then
    lake_env=(
      env -u CI
      "LEAN_SYSROOT=$toolchain_root/lean"
      "MATHLIB_NO_CACHE_ON_UPDATE=1"
      "LAKE_CACHE_DIR=$toolchain_root/lake-cache"
      "PATH=$toolchain_root/lean/bin:$PATH"
      "LD_LIBRARY_PATH=$toolchain_root/lean/lib:$toolchain_root/lean/lib/lean:${LD_LIBRARY_PATH:-}"
    )
    run_timed playground_manual_lake_no_rewrite \
      bash -c 'cd "$1" && shift && "$@" --keep-toolchain --old build Generated Anneal' \
      bash "$lean_root" "${lake_env[@]}" "$toolchain_root/lean/bin/lake"
    run_timed playground_lake_env_true \
      bash -c 'cd "$1" && shift && "$@" --keep-toolchain env true' \
      bash "$lean_root" "${lake_env[@]}" "$toolchain_root/lean/bin/lake"

    specs="$(find "$lean_root/generated" -name 'Playground*.lean' | head -1 || true)"
    if [[ -n "$specs" ]]; then
      "${lake_env[@]}" "$toolchain_root/lean/bin/lake" --keep-toolchain env printenv LEAN_PATH > "$RESULT_DIR/playground.LEAN_PATH"
      lean_path="$(cat "$RESULT_DIR/playground.LEAN_PATH")"
      run_timed playground_direct_lean_diagnostics \
        env -u CI "LEAN_SYSROOT=$toolchain_root/lean" "LEAN_PATH=$lean_path" \
          "MATHLIB_NO_CACHE_ON_UPDATE=1" "LAKE_CACHE_DIR=$toolchain_root/lake-cache" \
          "PATH=$toolchain_root/lean/bin:$PATH" \
          "LD_LIBRARY_PATH=$toolchain_root/lean/lib:$toolchain_root/lean/lib/lean:${LD_LIBRARY_PATH:-}" \
          "$toolchain_root/lean/bin/lean" --json "$specs"
    fi
  fi
fi

{
  echo "# Playground Workflow Results"
  echo
  echo "- Result directory: $RESULT_DIR"
  echo "- Playground root: $PLAYGROUND_ROOT"
  echo "- Anneal binary: $ANNEAL_BIN"
  echo "- Anneal toolchain parent: $ANNEAL_TOOLCHAIN_DIR"
  echo "- Timeout per command: ${VERIFY_TIMEOUT}s"
  echo
  echo "## Timings"
  echo
  echo '```tsv'
  cat "$TIMINGS"
  echo '```'
  echo
  echo "## Trace Times"
  echo
  for f in "$RESULT_DIR"/*.stderr; do
    base="$(basename "$f")"
    if extract_trace_times "$f" >/tmp/anneal-trace-times.$$; then
      if [[ -s /tmp/anneal-trace-times.$$ ]]; then
        echo "### $base"
        echo
        echo '```text'
        cat /tmp/anneal-trace-times.$$
        echo '```'
        echo
      fi
    fi
    rm -f /tmp/anneal-trace-times.$$
  done
  if [[ -d "$playground/target" ]]; then
    echo "## Playground Target Size"
    echo
    echo '```text'
    du -sh "$playground/target" "$playground/target/anneal/cargo_target" 2>/dev/null || true
    echo '```'
  fi
} > "$RESULT_DIR/summary.md"

echo "$RESULT_DIR"
