#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: $0 <flake-eval|ci-tests|clippy|sandbox|audit|guard-mutation|ws-meta|ws-test|installed-smoke>" >&2
  exit 2
fi

# Wall-clock limit in seconds for each mode. The two tiers mirror the legacy
# `anneal-current.yml` job timeouts (90 and 30 minutes). An unlisted mode gets
# the shorter tier so that a new mode added without an entry here fails fast
# and visibly, prompting an explicit entry, rather than running unbounded.
check_timeout_secs() {
  case "$1" in
    ws-test|audit|installed-smoke|guard-mutation) echo 5400 ;;
    clippy|flake-eval|ci-tests|sandbox|ws-meta) echo 1800 ;;
    *) echo 1800 ;;
  esac
}

# Name the likely cause when the re-executed script receives SIGTERM, then
# re-raise it with the default action so `timeout` sees the termination.
report_sigterm() {
  echo "error: run_anneal_check.sh $TIMEOUT_MODE got SIGTERM: its" \
    "${TIMEOUT_LIMIT}s limit expired or the run was cancelled" >&2
  trap - TERM
  kill -TERM "$$"
}

# Re-execute this script once under coreutils `timeout`, so every mode is
# bounded without wrapping individual commands. At the limit, `timeout` sends
# SIGTERM to the script's whole process group and exits 124; if anything
# survives another 120 seconds, it sends SIGKILL and exits 137. Any other exit
# status or terminating signal of the script passes through unchanged. The
# re-executed copy sees `ANNEAL_CHECK_TIMEOUT_ACTIVE` and clears it, so the
# sentinel never leaks into the commands the mode runs.
# `ANNEAL_CHECK_TIMEOUT_SECS` can only tighten the limit; tests use it.
reexec_under_timeout() {
  local mode="$1" limit override
  if [[ -n "${ANNEAL_CHECK_TIMEOUT_ACTIVE:-}" ]]; then
    TIMEOUT_MODE="$mode"
    TIMEOUT_LIMIT="$ANNEAL_CHECK_TIMEOUT_ACTIVE"
    unset ANNEAL_CHECK_TIMEOUT_ACTIVE
    trap report_sigterm TERM
    return 0
  fi
  limit="$(check_timeout_secs "$mode")"
  override="${ANNEAL_CHECK_TIMEOUT_SECS:-}"
  if [[ -n "$override" ]]; then
    if [[ ! "$override" =~ ^[1-9][0-9]{0,5}$ ]] || ((override > limit)); then
      echo "error: ANNEAL_CHECK_TIMEOUT_SECS must be in 1..$limit: $override" >&2
      exit 2
    fi
    limit="$override"
  fi
  echo "run_anneal_check.sh $mode: limit ${limit}s; exit 124 or 137 means it" \
    "timed out" >&2
  export ANNEAL_CHECK_TIMEOUT_ACTIVE="$limit"
  exec /usr/bin/timeout --verbose --kill-after=120s "${limit}s" \
    "$BASH" "$0" "$@"
}

reexec_under_timeout "$@"

MODE="$1"
shift

cd "$(cd "$(dirname "$0")/.." && pwd)"

verify_root_tcb_manifest() {
  local linked_path
  linked_path="$(find trusted -type l -print -quit)"
  if [[ -n "$linked_path" ]]; then
    echo "symlink in Anneal trusted tree: $linked_path" >&2
    exit 1
  fi
  sha256sum --check --strict trusted/root-manifest.sha256
  local root name path
  for root in . ..; do
    for name in .cargo rust-toolchain rust-toolchain.toml .gitmodules; do
      path="$root/$name"
      if [[ -e "$path" || -L "$path" ]]; then
        echo "forbidden root config override: $path" >&2
        exit 1
      fi
    done
  done
}

# Parse `KEY=VALUE` lines from `ci/check_bundle_tree.py` fail-closed without
# `eval` or pipeline `errexit` suppression, preserving spaces in values such as
# `RUSTFLAGS`.
apply_bundle_env() {
  local output line key val
  output="$(/usr/bin/python3 -I -B ci/check_bundle_tree.py "$@")"
  while IFS= read -r line; do
    [[ -n "$line" ]] || continue
    if [[ "$line" != *=* ]]; then
      echo "error: malformed check_bundle_tree.py line: $line" >&2
      exit 1
    fi
    key="${line%%=*}"
    val="${line#*=}"
    if [[ ! "$key" =~ ^[A-Z0-9_]+$ ]]; then
      echo "error: invalid check_bundle_tree.py env key: $key" >&2
      exit 1
    fi
    export "$key=$val"
  done <<< "$output"
}

# Refuse to use a mounted Cargo cache that could steer later cargo runs:
# `config`/`config.toml` can set `build.rustc-wrapper`, target runners, or
# source replacement, `credentials`/`credentials.toml` must never reach a
# shared cache, and `bin/` can shadow cargo subcommands. Any entry with one of
# these names, including a symlink, fails closed.
require_inert_cargo_home() {
  local cargo_home="$1" name
  for name in config config.toml credentials credentials.toml bin; do
    if [[ -e "$cargo_home/$name" || -L "$cargo_home/$name" ]]; then
      echo "error: refusing CARGO_HOME $cargo_home: it contains $name" >&2
      exit 1
    fi
  done
}

# Apply `require_inert_cargo_home` to `<mount>` whenever the effective
# `CARGO_HOME` (`<cargo_home>`) names it, whether the caller preset it or this
# script adopted it. Trailing slashes and, via `realpath -m`, `.`/`..`
# components and symlinks are normalized before comparing.
guard_mounted_cargo_home() {
  local cargo_home="$1" mount="$2"
  [[ -n "$cargo_home" ]] || return 0
  while [[ "$cargo_home" == */ && "$cargo_home" != / ]]; do
    cargo_home="${cargo_home%/}"
  done
  while [[ "$mount" == */ && "$mount" != / ]]; do
    mount="${mount%/}"
  done
  if [[ "$cargo_home" == "$mount" ]] || {
    command -v realpath >/dev/null 2>&1 \
      && [[ "$(realpath -m -- "$cargo_home")" == "$(realpath -m -- "$mount")" ]]
  }; then
    require_inert_cargo_home "$mount"
  fi
}

verify_bwrap_sandbox() {
  bwrap --unshare-all --die-with-parent --new-session --clearenv \
    --tmpfs / --dev /dev --proc /proc \
    --ro-bind /usr/lib /usr/lib \
    --ro-bind-try /usr/lib64 /usr/lib64 \
    --ro-bind-try /lib /lib \
    --ro-bind-try /lib64 /lib64 \
    --ro-bind-try /etc/ld.so.cache /etc/ld.so.cache \
    --ro-bind /usr/bin/true /true \
    -- /true
}

# Build `anneal-rustc-capture` and delegate staging/packing to the canonical
# `ci/pack_omnibus_archive.sh` shared with `flake.nix`.
prepare_omnibus_payload() {
  local mode_flag="$1"
  local target_path="$2"
  local stage_root="${SCRATCH_ROOT}/omnibus-stage"
  local capture_target="${SCRATCH_ROOT}/rustc-capture-target"
  rm -rf "$stage_root" "$capture_target"
  mkdir -p "$stage_root"

  local rust_tc lean_tc
  rust_tc="$(readlink -f /opt/anneal-nix/rust-toolchain)"
  lean_tc="$(readlink -f /opt/anneal-nix/lean-toolchain)"

  CARGO_TARGET_DIR="$capture_target" \
  RUSTC=/opt/anneal-nix/build-rustc \
  RUSTFLAGS="-Lnative=${rust_tc}/lib" \
  cargo build --locked --offline --release \
    --manifest-path trusted/rustc-capture/Cargo.toml

  printf '%s\n' \
    '#!/usr/bin/env bash' \
    "export LEAN_SYSROOT=\"$lean_tc\"" \
    "export LD_LIBRARY_PATH=\"$lean_tc/lib:$lean_tc/lib/lean:/opt/anneal-nix/runtime-libs\${LD_LIBRARY_PATH:+:\$LD_LIBRARY_PATH}\"" \
    "exec \"$lean_tc/bin/lean\" \"\$@\"" \
    > "$stage_root/build-lean"
  chmod 0755 "$stage_root/build-lean"

  ./ci/pack_omnibus_archive.sh \
    --platform linux \
    --anneal-root "$PWD" \
    --rust-toolchain "$rust_tc" \
    --lean-toolchain "$lean_tc" \
    --lean-exec "$stage_root/build-lean" \
    --rustc-capture-bin "$capture_target/release/anneal-rustc-capture" \
    --libz /opt/anneal-nix/runtime-libs/libz.so.1 \
    --libgcc-s /opt/anneal-nix/runtime-libs/libgcc_s.so.1 \
    --python /usr/bin/python3 \
    --work-dir "$stage_root/work" \
    --prebuild-jobs "${CARGO_BUILD_JOBS:-4}" \
    --zstd-jobs "${CARGO_BUILD_JOBS:-4}" \
    "$mode_flag" "$target_path"

  rm -rf "$stage_root" "$capture_target"
}

build_omnibus_archive() {
  local out_archive="$1"
  prepare_omnibus_payload --output-archive "$out_archive"
}

# Stage the trimmed omnibus toolchain layout directly into `<install_root>`
# for `ws-test` shards without `zstd -12` compression, archive verification
# decompressions, or `bwrap` archive unpacking (`installed-smoke` exercises
# the full archive pack + `cargo-anneal setup --local-archive` path).
stage_ws_toolchain_root() {
  local install_root="$1"
  prepare_omnibus_payload --stage-dir "$install_root"
}

verify_root_tcb_manifest

unset ANNEAL_MIRI_CACHE_DIR ANNEAL_TEST_ARCHIVE ANNEAL_TEST_CASE
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-4}"
export RUST_TEST_THREADS="${RUST_TEST_THREADS:-4}"
export SCRATCH_ROOT="${HOME:-/scratch}"
export CARGO_NET_OFFLINE=true
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-${SCRATCH_ROOT}/anneal-target}"
mkdir -p "$CARGO_TARGET_DIR"

if [[ -d /opt/anneal-cargo-vendor ]]; then
  ANNEAL_CARGO_HOME="${SCRATCH_ROOT}/anneal-cargo-home"
  mkdir -p "$ANNEAL_CARGO_HOME"
  cat > "$ANNEAL_CARGO_HOME/config.toml" <<'EOF'
[source.crates-io]
replace-with = "anneal-vendor"

[source.anneal-vendor]
directory = "/opt/anneal-cargo-vendor"
EOF
  export CARGO_HOME="$ANNEAL_CARGO_HOME"
elif [[ -d /cargo-home && ( -z "${CARGO_HOME:-}" || "${CARGO_HOME}" == "/usr/local/cargo" ) ]]; then
  export CARGO_HOME="/cargo-home"
fi
guard_mounted_cargo_home "${CARGO_HOME:-}" /cargo-home
if [[ -x /opt/anneal-nix/build-rustc ]]; then
  export RUSTC="/opt/anneal-nix/build-rustc"
fi

HASH_OPT_ARGS=(
  --config 'profile.dev.package.cpufeatures.opt-level=3'
  --config 'profile.dev.package.digest.opt-level=3'
  --config 'profile.dev.package.sha2.opt-level=3'
)
FULL_OPT_ARGS=(
  "${HASH_OPT_ARGS[@]}"
  --config 'profile.dev.package.zstd-sys.opt-level=3'
)

case "$MODE" in
  flake-eval)
    rm -rf "${SCRATCH_ROOT}/nix-cache" "${SCRATCH_ROOT}/nix-upper" "${SCRATCH_ROOT}/nix-work"
    cp -a /opt/nix-cache "${SCRATCH_ROOT}/nix-cache"
    chmod -R u+w "${SCRATCH_ROOT}/nix-cache"
    mkdir -p "${SCRATCH_ROOT}/nix-upper" "${SCRATCH_ROOT}/nix-work"
    # Overlay a scratch upperdir onto read-only `/nix` inside a private mount
    # namespace so Nix preserves the pre-populated `/nix/var/nix/db/db.sqlite`
    # valid-path database while allowing `path:.` to copy into `/nix/store`.
    # shellcheck disable=SC2016
    unshare -Ur -m bash -euo pipefail -c '
      mount -t overlay overlay \
        -o "lowerdir=/nix,upperdir=${SCRATCH_ROOT}/nix-upper,workdir=${SCRATCH_ROOT}/nix-work" \
        /nix
      export XDG_CACHE_HOME="${SCRATCH_ROOT}/nix-cache"
      for output in packages devShells; do
        nix eval --offline --json "path:.#$output" \
          --apply "builtins.mapAttrs (_: builtins.mapAttrs (_: pkg: pkg.drvPath))" \
          >/dev/null
      done
    '
    ;;

  ci-tests)
    export ANNEAL_CI_STRICT=1
    rg --version >/dev/null
    ./ci/check_todo.sh
    ./ci/check_non_stable_version.sh
    ./ci/check_actions.sh
    ./ci/check_job_dependencies.sh
    PY_BIN="/usr/bin/python3"
    if [[ -x /opt/anneal-nix/release-check-python/bin/python3 ]]; then
      PY_BIN="/opt/anneal-nix/release-check-python/bin/python3"
    fi
    "$PY_BIN" -I -B ./ci/check_minirust_pin.py \
      --repo-root . --check-lean --check-anchors
    "$PY_BIN" -I -B -m unittest discover -s ci -p 'test_*.py' -v
    ;;

  clippy)
    # Runs on `zc-stable-msrv` (which installs `clippy` and
    # `wasm32-unknown-unknown`; `anneal-tc` omits them).
    if ! cargo clippy --version >/dev/null 2>&1; then
      echo "error: cargo clippy is required for mode 'clippy' (run on zc-stable-msrv)" >&2
      exit 1
    fi
    cargo clippy --locked --offline --no-deps \
      -p cargo-anneal --no-default-features \
      --lib --bins \
      -- -A clippy::type_complexity -D warnings
    cargo clippy --locked --offline --no-deps \
      -p cargo-anneal-tests --no-default-features \
      --test cli --test inspect \
      -- -A clippy::type_complexity -D warnings
    RUSTFLAGS="-D warnings" cargo check --locked --offline \
      -p cargo-anneal --no-default-features \
      --lib --target wasm32-unknown-unknown
    ;;

  sandbox)
    # Runs on `anneal-arm64` (which installs `clippy`; `anneal-tc` omits it).
    if ! cargo clippy --version >/dev/null 2>&1; then
      echo "error: cargo clippy is required for mode 'sandbox' (run on anneal-arm64)" >&2
      exit 1
    fi
    verify_bwrap_sandbox
    SANDBOX_DIAG="${SCRATCH_ROOT}/sandbox-diag"
    rm -rf "$SANDBOX_DIAG"
    mkdir -p "$SANDBOX_DIAG"
    cargo clippy --locked --offline -p cargo-anneal \
      --lib -- -D warnings
    cargo clippy --locked --offline -p cargo-anneal-tests \
      --test sandbox_escape -- -D warnings
    cargo test --locked --offline -p cargo-anneal --lib sandbox:: \
      -- --list > "$SANDBOX_DIAG/sandbox-lib.stdout"
    test "$(grep -c ': test$' "$SANDBOX_DIAG/sandbox-lib.stdout")" -ge 1
    cargo test --locked --offline -p cargo-anneal --lib sandbox:: \
      -- --test-threads=1
    cargo test --locked --offline -p cargo-anneal-tests --test sandbox_escape \
      -- --list --exact \
      sandbox_escape_vectors_blocked_in_tier1_and_tier2 \
      wall_clock_timeout_kills_process_group_in_tier1_and_tier2 \
      tier1_as_pid1_prevents_post_exit_out_writes \
      > "$SANDBOX_DIAG/sandbox-selection.stdout"
    test "$(grep -c ': test$' "$SANDBOX_DIAG/sandbox-selection.stdout")" -eq 3
    cargo test --locked --offline -p cargo-anneal-tests --test sandbox_escape \
      -- --test-threads=1 --exact \
      sandbox_escape_vectors_blocked_in_tier1_and_tier2 \
      wall_clock_timeout_kills_process_group_in_tier1_and_tier2 \
      tier1_as_pid1_prevents_post_exit_out_writes
    ;;

  audit)
    verify_bwrap_sandbox
    LEAN_STAGE="${SCRATCH_ROOT}/anneal-lean-root"
    rm -rf "$LEAN_STAGE"
    mkdir -p "$LEAN_STAGE"
    cp -rL /opt/anneal-nix/lean-toolchain "$LEAN_STAGE/lean"
    chmod -R u+w "$LEAN_STAGE/lean"
    apply_bundle_env --root "$LEAN_STAGE" --lean-only
    MIRI_CACHE="${ANNEAL_CI_MIRI_CACHE_DIR:-/ci-cache/miri}"
    AUDIT_CACHE_ARGS=()
    if [[ -d "$MIRI_CACHE" && -w "$MIRI_CACHE" ]]; then
      AUDIT_CACHE_ARGS=(--miri-cache-dir "$MIRI_CACHE")
    elif [[ -d "$MIRI_CACHE" ]]; then
      SCRATCH_MIRI_CACHE="${SCRATCH_ROOT}/miri-cache"
      rm -rf "$SCRATCH_MIRI_CACHE"
      cp -a "$MIRI_CACHE" "$SCRATCH_MIRI_CACHE"
      chmod -R u+w "$SCRATCH_MIRI_CACHE"
      AUDIT_CACHE_ARGS=(--miri-cache-dir "$SCRATCH_MIRI_CACHE")
    fi
    cargo "${HASH_OPT_ARGS[@]}" run --locked --offline -p anneal-audit -- \
      --lean "$ANNEAL_TEST_INSTALL_ROOT/lean/bin/lean" \
      --require-correspondence \
      "${AUDIT_CACHE_ARGS[@]}"
    ;;

  guard-mutation)
    GUARD_DIAG="${SCRATCH_ROOT}/guard-mutation"
    rm -rf "$GUARD_DIAG"
    mkdir -p "$GUARD_DIAG"
    /usr/bin/python3 -I -B ci/check_guard_mutation.py \
      --lean /opt/anneal-nix/lean-toolchain/bin/lean \
      --jobs 4 \
      --json-out "$GUARD_DIAG/guard-mutation.json"
    ;;

  ws-meta)
    # `ws-meta` runs only `regenerate_bundle --check`, `--no-default-features`
    # lib/bin/cli/inspect tests, and `--workspace --doc`, none of which read
    # `ANNEAL_CAPTURE` or prebuilt `.olean`s. Stage only the Lean toolchain
    # (for `default_lean_path()` / `ANNEAL_LEAN` unit tests) and point Cargo /
    # rustdoc at `/opt/anneal-nix/rust-toolchain` directly rather than building
    # `anneal-rustc-capture` and `prebuild_bundled_oleans.py` an extra time;
    # all six `ws-test` shards and `installed-smoke` exercise the trimmed
    # omnibus layout.
    verify_bwrap_sandbox
    INSTALL_CACHE="${SCRATCH_ROOT}/anneal-ws-meta-toolchain"
    INSTALL_ROOT="$INSTALL_CACHE/anneal/toolchain/extracted"
    rm -rf "$INSTALL_CACHE"
    mkdir -p "$INSTALL_ROOT"
    LEAN_TC="$(readlink -f /opt/anneal-nix/lean-toolchain)"
    cp -r "$LEAN_TC" "$INSTALL_ROOT/lean"
    chmod -R u+w "$INSTALL_ROOT/lean"
    apply_bundle_env --cache-root "$INSTALL_CACHE" --root "$INSTALL_ROOT" --lean-only
    RUST_TC="$(readlink -f /opt/anneal-nix/rust-toolchain)"
    export XDG_CACHE_HOME="$INSTALL_CACHE"
    export ANNEAL_LEAN="$ANNEAL_TEST_INSTALL_ROOT/lean/bin/lean"
    export ANNEAL_SYSROOT="$RUST_TC"
    export ANNEAL_TEST_RUST_SYSROOT="$RUST_TC"
    export RUSTDOC="$RUST_TC/bin/rustdoc"
    export LD_LIBRARY_PATH="$RUST_TC/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
    export RUSTFLAGS="-Lnative=$RUST_TC/lib -Clink-arg=-Wl,-rpath,$RUST_TC/lib"
    cargo run --locked --offline -p cargo-anneal --example regenerate_bundle \
      "${FULL_OPT_ARGS[@]}" \
      -- --root . --check
    cargo test --locked --offline -p cargo-anneal --no-default-features \
      "${FULL_OPT_ARGS[@]}" \
      --lib --bin cargo-anneal
    cargo test --locked --offline -p cargo-anneal-tests --no-default-features \
      "${FULL_OPT_ARGS[@]}" \
      --test cli --test inspect
    cargo test --workspace --locked --offline \
      "${FULL_OPT_ARGS[@]}" \
      --doc
    ;;

  ws-test)
    : "${SHARD_SPEC:?}"
    verify_bwrap_sandbox
    INSTALL_CACHE="${SCRATCH_ROOT}/anneal-ws-toolchain"
    INSTALL_ROOT="$INSTALL_CACHE/anneal/toolchain/extracted"
    rm -rf "$INSTALL_CACHE"
    mkdir -p "$INSTALL_ROOT"
    stage_ws_toolchain_root "$INSTALL_ROOT"
    apply_bundle_env --cache-root "$INSTALL_CACHE" --root "$INSTALL_ROOT"
    cargo nextest run --workspace --locked --offline \
      "${FULL_OPT_ARGS[@]}" \
      --no-fail-fast --failure-output immediate \
      --partition "hash:${SHARD_SPEC}"
    ;;

  installed-smoke)
    export ANNEAL_TEST_JOBS="4"
    export ANNEAL_TEST_TIMEOUT_SECS="120"
    verify_bwrap_sandbox
    DIAG="${SCRATCH_ROOT}/installed-smoke-diag"
    TOOLS_ROOT="${SCRATCH_ROOT}/anneal-tools"
    BOOT_TARGET="${SCRATCH_ROOT}/anneal-bootstrap-target"
    ARCHIVE_PATH="${SCRATCH_ROOT}/anneal-exocrate.tar.zst"
    rm -rf "$DIAG" "$TOOLS_ROOT" "$BOOT_TARGET" "$ARCHIVE_PATH"
    mkdir -p "$DIAG" "$TOOLS_ROOT" "$BOOT_TARGET"
    export ANNEAL_TEST_DIAGNOSTICS="$DIAG"

    if [[ -z "${ANNEAL_TEST_SOURCE_REVISION:-}" ]]; then
      if git rev-parse --verify HEAD >/dev/null 2>&1; then
        ANNEAL_TEST_SOURCE_REVISION="$(git rev-parse HEAD)"
      else
        MANIFEST_DIGEST="$(sha256sum trusted/root-manifest.sha256 | awk '{print $1}')"
        ANNEAL_TEST_SOURCE_REVISION="manifest-sha256:${MANIFEST_DIGEST}"
      fi
    fi
    if [[ -z "$ANNEAL_TEST_SOURCE_REVISION" ]]; then
      echo "error: failed to resolve non-empty ANNEAL_TEST_SOURCE_REVISION" >&2
      exit 1
    fi
    export ANNEAL_TEST_SOURCE_REVISION

    build_omnibus_archive "$ARCHIVE_PATH"

    cargo install --locked --offline --debug --path trusted/cargo-anneal \
      "${FULL_OPT_ARGS[@]}" \
      --target-dir "$BOOT_TARGET" --root "$TOOLS_ROOT"
    rm -rf "$BOOT_TARGET"
    export ANNEAL_TEST_CARGO_ANNEAL="$TOOLS_ROOT/bin/cargo-anneal"
    export ANNEAL_TEST_TOOLS_ROOT="$TOOLS_ROOT"

    INSTALL_CACHE="${SCRATCH_ROOT}/anneal-smoke-toolchain"
    SETUP_PROJECT="${SCRATCH_ROOT}/anneal-setup-project"
    rm -rf "$INSTALL_CACHE" "$SETUP_PROJECT"
    mkdir -p "$INSTALL_CACHE" "$SETUP_PROJECT/src"
    export XDG_CACHE_HOME="$INSTALL_CACHE"
    printf '%s\n' \
      '[package]' \
      'name = "anneal-setup-smoke"' \
      'version = "0.0.0"' \
      'edition = "2024"' \
      > "$SETUP_PROJECT/Cargo.toml"
    touch "$SETUP_PROJECT/src/lib.rs"
    (
      cd "$SETUP_PROJECT"
      "$ANNEAL_TEST_CARGO_ANNEAL" setup --local-archive "$ARCHIVE_PATH"
    )
    rm -f "$ARCHIVE_PATH"

    apply_bundle_env \
      --cache-root "$XDG_CACHE_HOME" \
      --discover-single \
      --diagnostics "$DIAG/installation.json" \
      --source-revision "$ANNEAL_TEST_SOURCE_REVISION"

    DRIVER_PROBE="${SCRATCH_ROOT}/anneal-driver-probe"
    rm -rf "$DRIVER_PROBE"
    mkdir -p "$DRIVER_PROBE"
    printf '%s\n' 'pub fn identity(n: u32) -> u32 { n }' > "$DRIVER_PROBE/probe.rs"
    (
      cd "$DRIVER_PROBE"
      env -i "$ANNEAL_TEST_INSTALL_ROOT/bin/anneal-rustc-capture" \
        --edition=2024 --crate-type=lib --emit=metadata \
        probe.rs -o probe.rmeta
    ) > "$DIAG/driver.stdout" 2> "$DIAG/driver.stderr"
    test -s "$DRIVER_PROBE/probe.rmeta"
    test ! -s "$DIAG/driver.stdout"
    grep -Fx 'note: anneal-rustc-capture: compiler analysis callback reached; verification not performed' \
      "$DIAG/driver.stderr"

    cargo install --locked --offline --debug --path trusted/audit \
      "${FULL_OPT_ARGS[@]}" \
      --root "$TOOLS_ROOT"
    export ANNEAL_TEST_AUDITOR="$TOOLS_ROOT/bin/anneal-audit"

    bwrap --unshare-all --die-with-parent --new-session --clearenv \
      --cap-drop ALL --tmpfs / --dev /dev --proc /proc --tmpfs /tmp \
      --dir /tmp/home --chdir /tmp \
      --setenv HOME /tmp/home --setenv PATH /usr/bin:/bin \
      --setenv XDG_CACHE_HOME /toolchain-cache \
      --ro-bind /usr /usr \
      --ro-bind-try /bin /bin --ro-bind-try /lib /lib \
      --ro-bind-try /lib64 /lib64 \
      --ro-bind-try /etc/ld.so.cache /etc/ld.so.cache \
      --ro-bind "$XDG_CACHE_HOME" /toolchain-cache \
      --ro-bind "$ANNEAL_TEST_CARGO_ANNEAL" /cargo-anneal \
      --ro-bind "$PWD/ci/probe_alpha.py" /anneal/ci/probe_alpha.py \
      --ro-bind "$PWD/trusted/cargo-anneal/assets/scalar" \
        /anneal/trusted/cargo-anneal/assets/scalar \
      -- /usr/bin/python3 -I -B /anneal/ci/probe_alpha.py --cli /cargo-anneal

    STARNIX_SRC="${ANNEAL_STARNIX_SOURCE_DIR:-/opt/starnix-ebpf-src}"
    if [[ ! -d "$STARNIX_SRC" ]]; then
      echo "error: missing Starnix pinned source directory: $STARNIX_SRC" >&2
      exit 1
    fi
    STARNIX_OUT="${SCRATCH_ROOT}/starnix-run"
    rm -rf "$STARNIX_OUT"
    mkdir -p "$STARNIX_OUT"
    REPO_ROOT="$(cd .. && pwd)"
    bwrap --unshare-all --die-with-parent --new-session \
      --clearenv --cap-drop ALL --tmpfs / --dev /dev --proc /proc \
      --tmpfs /tmp --dir /tmp/home --chdir "$PWD" \
      --setenv HOME /tmp/home --setenv TMPDIR /tmp \
      --setenv PATH /usr/bin:/bin \
      --setenv LD_LIBRARY_PATH "$ANNEAL_SYSROOT/lib" \
      --ro-bind /usr /usr \
      --ro-bind-try /bin /bin --ro-bind-try /lib /lib \
      --ro-bind-try /lib64 /lib64 --ro-bind-try /etc /etc \
      --ro-bind-try /nix/store /nix/store \
      --ro-bind "$REPO_ROOT" "$REPO_ROOT" \
      --ro-bind "$ANNEAL_TEST_INSTALL_ROOT" "$ANNEAL_TEST_INSTALL_ROOT" \
      --ro-bind "$ANNEAL_TEST_TOOLS_ROOT" "$ANNEAL_TEST_TOOLS_ROOT" \
      --ro-bind "$STARNIX_SRC" "$STARNIX_SRC" \
      --bind "$STARNIX_OUT" "$STARNIX_OUT" \
      -- /usr/bin/python3 -I -B ci/verify_starnix_e2e.py \
      --source-dir "$STARNIX_SRC" \
      --cli "$ANNEAL_TEST_CARGO_ANNEAL" \
      --capture "$ANNEAL_CAPTURE" \
      --sysroot "$ANNEAL_SYSROOT" \
      --lean "$ANNEAL_LEAN" \
      --artifacts-dir "$STARNIX_OUT/starnix-evidence"

    ZC_OUT="${SCRATCH_ROOT}/zerocopy-run"
    rm -rf "$ZC_OUT"
    mkdir -p "$ZC_OUT"
    bwrap --unshare-all --die-with-parent --new-session \
      --clearenv --cap-drop ALL --tmpfs / --dev /dev --proc /proc \
      --tmpfs /tmp --dir /tmp/home --chdir "$PWD" \
      --setenv HOME /tmp/home --setenv TMPDIR /tmp \
      --setenv PATH /usr/bin:/bin \
      --setenv LD_LIBRARY_PATH "$ANNEAL_SYSROOT/lib" \
      --ro-bind /usr /usr \
      --ro-bind-try /bin /bin --ro-bind-try /lib /lib \
      --ro-bind-try /lib64 /lib64 --ro-bind-try /etc /etc \
      --ro-bind-try /nix/store /nix/store \
      --ro-bind "$REPO_ROOT" "$REPO_ROOT" \
      --ro-bind "$ANNEAL_TEST_INSTALL_ROOT" "$ANNEAL_TEST_INSTALL_ROOT" \
      --ro-bind "$ANNEAL_TEST_TOOLS_ROOT" "$ANNEAL_TEST_TOOLS_ROOT" \
      --bind "$ZC_OUT" "$ZC_OUT" \
      -- /usr/bin/python3 -I -B ci/verify_zerocopy.py \
      --cli "$ANNEAL_TEST_CARGO_ANNEAL" \
      --capture "$ANNEAL_CAPTURE" \
      --sysroot "$ANNEAL_SYSROOT" \
      --lean "$ANNEAL_LEAN" \
      --artifacts-dir "$ZC_OUT/zerocopy-evidence" \
      --jobs "$ANNEAL_TEST_JOBS"

    # `cargo package` archives only the crate directory, so the packaged build
    # script needs staged `packaged/{bundled_resources.rs,bundled_theory.json}`
    # snapshots. The checkout is read-only here, so stage them in a scratch
    # copy.
    PKG_SRC="${SCRATCH_ROOT}/package-src"
    rm -rf "$PKG_SRC"
    mkdir -p "$PKG_SRC"
    cp -a . "$PKG_SRC/anneal"
    chmod -R u+w "$PKG_SRC/anneal"
    (
      cd "$PKG_SRC/anneal"
      test ! -e trusted/cargo-anneal/packaged
      cargo run --locked --offline -p cargo-anneal --example regenerate_bundle \
        "${FULL_OPT_ARGS[@]}" \
        -- --root . --stage-package
      staged="$(cd trusted/cargo-anneal/packaged && find . -mindepth 1 | LC_ALL=C sort)"
      expected_staged="$(printf './bundled_resources.rs\n./bundled_theory.json')"
      test "$staged" = "$expected_staged"
      cargo metadata --locked --offline --format-version 1 --no-deps \
        > "$DIAG/package-metadata.json"
      cargo package --allow-dirty --no-verify --offline --registry crates-io \
        -p cargo-anneal "${FULL_OPT_ARGS[@]}"
    )
    rm -rf "$PKG_SRC"
    PREPARED_MANIFEST="$(/usr/bin/python3 -I -B - <<'PY'
import json
import os
from pathlib import Path
import shutil
import tarfile

diagnostics = Path(os.environ["ANNEAL_TEST_DIAGNOSTICS"])
metadata = json.loads((diagnostics / "package-metadata.json").read_text())
packages = [p for p in metadata["packages"] if p["name"] == "cargo-anneal"]
if len(packages) != 1:
    raise SystemExit("expected exactly one cargo-anneal package")
package = packages[0]
slug = f"{package['name']}-{package['version']}"
prepared = Path(os.environ["CARGO_TARGET_DIR"]) / "package"
archive = prepared / f"{slug}.crate"
if not archive.is_file():
    raise SystemExit(f"packaged .crate archive is missing: {archive}")
# Remove any extraction left by an earlier run on a reused target dir so
# files dropped from the new `.crate` cannot satisfy the build below.
extracted = prepared / slug
if extracted.is_dir() and not extracted.is_symlink():
    shutil.rmtree(extracted)
elif extracted.exists() or extracted.is_symlink():
    extracted.unlink()
if extracted.exists() or extracted.is_symlink():
    raise SystemExit(f"stale extracted crate dir survived removal: {extracted}")
with tarfile.open(archive, "r:gz") as tf:
    tf.extractall(prepared, filter="data")
manifest = extracted / "Cargo.toml"
if not manifest.is_file():
    raise SystemExit(f"prepared crate manifest is missing: {manifest}")
print(manifest)
PY
    )"
    cargo build --locked --offline --manifest-path "$PREPARED_MANIFEST" \
      --lib --bins "${FULL_OPT_ARGS[@]}"
    cargo test --locked --offline --manifest-path "$PREPARED_MANIFEST" --no-run \
      "${FULL_OPT_ARGS[@]}"

    cargo test --locked --offline -p cargo-anneal-tests --test installed_smoke \
      "${FULL_OPT_ARGS[@]}" \
      -- --ignored --exact installed_smoke --list \
      > "$DIAG/installed-smoke-selection.stdout"
    grep -Fx 'installed_smoke: test' "$DIAG/installed-smoke-selection.stdout"
    cargo test --locked --offline -p cargo-anneal-tests --test installed_smoke \
      "${FULL_OPT_ARGS[@]}" \
      -- --ignored --exact installed_smoke --nocapture
    ;;

  *)
    echo "error: unknown mode: $MODE" >&2
    exit 2
    ;;
esac
