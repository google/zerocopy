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
  echo "usage: $0 <flake-eval|ci-tests|clippy|sandbox|audit|guard-mutation|ws-test|installed-smoke>" >&2
  exit 2
fi
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

build_omnibus_archive() {
  local out_archive="$1"
  local stage_root="${SCRATCH_ROOT}/omnibus-stage"
  local capture_target="${SCRATCH_ROOT}/rustc-capture-target"
  rm -rf "$stage_root" "$capture_target"
  mkdir -p \
    "$stage_root/dist_staging/bin" \
    "$stage_root/dist_staging/rust/lib" \
    "$stage_root/dist_staging/share/anneal/trusted/audit"

  local rust_tc
  rust_tc="$(readlink -f /opt/anneal-nix/rust-toolchain)"
  local lean_tc
  lean_tc="$(readlink -f /opt/anneal-nix/lean-toolchain)"

  CARGO_TARGET_DIR="$capture_target" \
  RUSTC=/opt/anneal-nix/build-rustc \
  RUSTFLAGS="-Lnative=${rust_tc}/lib" \
  cargo build --locked --offline --release \
    --manifest-path trusted/rustc-capture/Cargo.toml

  install -m 0755 "$capture_target/release/anneal-rustc-capture" \
    "$stage_root/dist_staging/bin/anneal-rustc-capture"
  rm -rf "$capture_target"

  cp -r trusted/lean "$stage_root/dist_staging/share/anneal/trusted/lean"
  # Stage only the bundled theory modules that `theory/bundle-manifest.json`
  # lists, as `flake.nix` does, so canary suites never enter the archive.
  mkdir -p "$stage_root/dist_staging/share/anneal/theory"
  cp theory/bundle-manifest.json \
    "$stage_root/dist_staging/share/anneal/theory/bundle-manifest.json"
  jq -e -r '.modules[].path' theory/bundle-manifest.json \
    > "$stage_root/theory_manifest_paths.txt"
  test -s "$stage_root/theory_manifest_paths.txt"
  local rel_path
  while IFS= read -r rel_path; do
    case "$rel_path" in
      *..*|*Canaries*)
        echo "ERROR: forbidden bundle-manifest path: $rel_path" >&2
        exit 1
        ;;
      theory/Anneal/*.lean)
        install -D -m 0644 "$rel_path" \
          "$stage_root/dist_staging/share/anneal/$rel_path"
        ;;
      *)
        echo "ERROR: unexpected bundle-manifest path: $rel_path" >&2
        exit 1
        ;;
    esac
  done < "$stage_root/theory_manifest_paths.txt"
  cp trusted/audit/TrustedBoundary.lean \
    "$stage_root/dist_staging/share/anneal/trusted/audit/TrustedBoundary.lean"
  cp trusted/audit/library-lock.json \
    "$stage_root/dist_staging/share/anneal/trusted/audit/library-lock.json"

  /usr/bin/python3 -I -B ci/render_correspondence_provenance.py \
    --trusted-bundle-rs trusted/cargo-anneal/src/trusted_bundle.rs \
    --upstream-pin vendor/lean-miri/UPSTREAM_PIN.json \
    --correspondence-adapters-dir trusted/correspondence \
    --correspondence-proofs-dir correspondence \
    --trusted-lean-dir trusted/lean \
    --output "$stage_root/dist_staging/share/anneal/correspondence-provenance.json"
  jq -e 'type == "object" and .schema_version == 1' \
    "$stage_root/dist_staging/share/anneal/correspondence-provenance.json" \
    > /dev/null

  chmod -R u+w "$stage_root/dist_staging"

  printf '%s\n' \
    '#!/usr/bin/env bash' \
    "export LEAN_SYSROOT=\"$lean_tc\"" \
    "export LD_LIBRARY_PATH=\"$lean_tc/lib:$lean_tc/lib/lean:/opt/anneal-nix/runtime-libs\${LD_LIBRARY_PATH:+:\$LD_LIBRARY_PATH}\"" \
    "exec \"$lean_tc/bin/lean\" \"\$@\"" \
    > "$stage_root/build-lean"
  chmod 0755 "$stage_root/build-lean"
  mkdir -p "$stage_root/prebuild_src/trusted/cargo-anneal/src"
  cp trusted/cargo-anneal/src/trusted_bundle.rs \
    "$stage_root/prebuild_src/trusted/cargo-anneal/src/trusted_bundle.rs"
  cp -r "$stage_root/dist_staging/share/anneal/trusted/audit" \
    "$stage_root/prebuild_src/trusted/audit"
  cp -r "$stage_root/dist_staging/share/anneal/trusted/lean" \
    "$stage_root/prebuild_src/trusted/lean"
  cp -r "$stage_root/dist_staging/share/anneal/theory" \
    "$stage_root/prebuild_src/theory"
  /usr/bin/python3 -I -B ci/prebuild_bundled_oleans.py \
    --anneal-root "$stage_root/prebuild_src" \
    --lean-bin "$lean_tc/bin/lean" \
    --lean-exec "$stage_root/build-lean" \
    --lean-prefix "$lean_tc" \
    --output-dir "$stage_root/dist_staging/share/anneal/prebuilt" \
    --jobs "${CARGO_BUILD_JOBS:-4}"
  chmod -R u+w "$stage_root/dist_staging/share/anneal/prebuilt"

  cp -L /opt/anneal-nix/runtime-libs/libz.so.1 \
    "$stage_root/dist_staging/rust/lib/libz.so.1"
  cp -L /opt/anneal-nix/runtime-libs/libgcc_s.so.1 \
    "$stage_root/dist_staging/rust/lib/libgcc_s.so.1"
  chmod u+w \
    "$stage_root/dist_staging/rust/lib/libz.so.1" \
    "$stage_root/dist_staging/rust/lib/libgcc_s.so.1"

  patchelf \
    --add-needed libz.so.1 \
    --set-interpreter "$(patchelf --print-interpreter "$rust_tc/bin/rustc")" \
    --set-rpath '$ORIGIN/../rust/lib' \
    "$stage_root/dist_staging/bin/anneal-rustc-capture"

  for full_path in \
    "$stage_root/dist_staging/bin/anneal-rustc-capture" \
    "$lean_tc/bin/lean" \
    "$rust_tc/bin/cargo" \
    "$rust_tc/bin/rustc" \
    "$stage_root/dist_staging/share/anneal/correspondence-provenance.json" \
    "$stage_root/dist_staging/share/anneal/prebuilt/manifest.json" \
    "$stage_root/dist_staging/share/anneal/prebuilt/TrustedBoundary.olean" \
    "$stage_root/dist_staging/share/anneal/prebuilt/lib/Trusted/MirAst.olean" \
    "$stage_root/dist_staging/share/anneal/prebuilt/lib/Anneal/MirWp.olean" \
    "$stage_root/dist_staging/share/anneal/prebuilt/lib/Anneal/Scalar.olean" \
    "$stage_root/dist_staging/share/anneal/prebuilt/lib/Anneal/Wp.olean" \
    "$stage_root/dist_staging/share/anneal/trusted/audit/TrustedBoundary.lean" \
    "$stage_root/dist_staging/share/anneal/trusted/audit/library-lock.json" \
    "$stage_root/dist_staging/share/anneal/trusted/lean/foundation-lock.json" \
    "$stage_root/dist_staging/share/anneal/trusted/lean/lean-toolchain" \
    "$stage_root/dist_staging/share/anneal/trusted/lean/Trusted/MirAst.lean" \
    "$stage_root/dist_staging/share/anneal/trusted/lean/Trusted/MirSemantics.lean" \
    "$stage_root/dist_staging/share/anneal/theory/bundle-manifest.json" \
    "$stage_root/dist_staging/share/anneal/theory/Anneal/MirWp.lean" \
    "$stage_root/dist_staging/share/anneal/theory/Anneal/Scalar.lean" \
    "$stage_root/dist_staging/share/anneal/theory/Anneal/Wp.lean"; do
    if [[ ! -f "$full_path" ]]; then
      echo "ERROR: expected archive entry missing: $full_path" >&2
      exit 1
    fi
  done

  pack_omnibus_archive \
    "$stage_root" "$lean_tc" "$rust_tc" theory/bundle-manifest.json "$out_archive"
  rm -rf "$stage_root"
}

# Pack `<stage_root>/dist_staging` plus the Lean and Rust toolchains into
# `<out_archive>` and verify the result. This mirrors the `tar_args`,
# duplicate-library symlinks, leak bans, required entries, and
# `library-lock.json` digest checks of `flake.nix`'s `omnibus-archive`
# (Linux branch) so `ws-test` and `installed-smoke` exercise the payload that
# `release.yml` ships. `ci/test_run_anneal_check.py` fails when the two drift.
pack_omnibus_archive() {
  local stage_root="$1"
  local lean_tc="$2"
  local rust_tc="$3"
  local bundle_manifest="$4"
  local out_archive="$5"

  # `flake.nix` uses `stdenv.hostPlatform.rust.rustcTarget`; the pinned
  # toolchain's own host triple names the same `lib/rustlib/<target>` tree.
  local rust_target_lines rust_target
  rust_target_lines="$(
    LD_LIBRARY_PATH="$rust_tc/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
      "$rust_tc/bin/rustc" -vV | sed -n 's/^host: //p'
  )"
  if [[ ! "$rust_target_lines" =~ ^[A-Za-z0-9_.-]+$ ]]; then
    echo "ERROR: cannot derive one rustc host triple: $rust_target_lines" >&2
    exit 1
  fi
  rust_target="$rust_target_lines"
  if [[ ! -d "$rust_tc/lib/rustlib/$rust_target" ]]; then
    echo "ERROR: missing rustlib tree for $rust_target in $rust_tc" >&2
    exit 1
  fi

  local lean_parent lean_base lean_esc rust_parent rust_base rust_esc
  lean_parent="$(dirname "$lean_tc")"
  lean_base="$(basename "$lean_tc")"
  lean_esc="$(printf '%s' "$lean_base" | sed 's/[.[\*^$:]/\\&/g')"
  rust_parent="$(dirname "$rust_tc")"
  rust_base="$(basename "$rust_tc")"
  rust_esc="$(printf '%s' "$rust_base" | sed 's/[.[\*^$:]/\\&/g')"

  local tar_args=(
    --mode='u+w'
    --hard-dereference
    --sort=name
    --mtime=@0
    --owner=0
    --group=0
    --numeric-owner
    --anchored
    --exclude="$lean_base/include"
    --exclude="$lean_base/bin/lake"
    --exclude="$lean_base/bin/leanchecker"
    --exclude="$lean_base/bin/clang*"
    --exclude="$lean_base/bin/ld.lld"
    --exclude="$lean_base/bin/lld*"
    --exclude="$lean_base/bin/llvm-*"
    --exclude="$lean_base/bin/leanc"
    --exclude="$lean_base/bin/leanir"
    --exclude="$lean_base/bin/leantar"
    --exclude="$lean_base/bin/cadical"
    --exclude="$lean_base/bin/leanmake"
    --exclude="$lean_base/lib/clang"
    --exclude="$lean_base/lib/libLLVM*"
    --exclude="$lean_base/lib/libclang*"
    --exclude="$lean_base/lib/*.a"
    --exclude="$lean_base/lib/lean/*.a"
    --exclude="$lean_base/lib/lean/Init.ilean"
    --exclude="$lean_base/lib/lean/Std.ilean"
    --exclude="$lean_base/lib/lean/Lean.ilean"
    --exclude="$lean_base/lib/lean/Lean/*.ilean"
    --exclude="$lean_base/lib/lean/Lake"
    --exclude="$lean_base/lib/lean/Lake.*"
    --exclude="$lean_base/lib/lean/LakeMain.*"
    --exclude="$lean_base/lib/lean/LeanIR"
    --exclude="$lean_base/lib/lean/LeanIR.*"
    --exclude="$lean_base/lib/lean/LeanChecker*"
    --exclude="$lean_base/lib/lean/Leanc*"
    --exclude="$lean_base/src/lean/lake"
    --exclude="$lean_base/src/lean/Lean"
    --exclude="$lean_base/src/lean/Lean.lean"
    --exclude="$lean_base/src/lean/Std.lean"
    --exclude="$lean_base/src/lean/LeanChecker.lean"
    --exclude="$lean_base/src/lean/LeanIR.lean"
    --exclude="$lean_base/src/lean/Leanc.lean"
    --exclude="$rust_base/share"
    --exclude="$rust_base/etc"
    --exclude="$rust_base/manifest.in"
    --exclude="$rust_base/libexec"
    --exclude="$rust_base/bin/miri"
    --exclude="$rust_base/bin/cargo-miri"
    --exclude="$rust_base/bin/rust-gdb*"
    --exclude="$rust_base/bin/rust-lldb"
    --exclude="$rust_base/lib/rustlib/src"
    --exclude="$rust_base/lib/rustlib/rustc-src"
    --exclude="$rust_base/lib/rustlib/etc"
    --exclude="$rust_base/lib/rustlib/$rust_target/lib/librustc-*_rt.*.a"
    --exclude="$rust_base/lib/rustlib/$rust_target/bin/llc"
    --exclude="$rust_base/lib/rustlib/$rust_target/bin/llvm-*"
    --exclude="$rust_base/lib/rustlib/$rust_target/bin/opt"
    --exclude="$rust_base/lib/rustlib/$rust_target/bin/wasm-component-ld"
  )

  # Replace byte-identical regular-file `libLLVM`/`librustc_driver` copies in
  # the target rustlib dir with relative symlinks to `rust/lib`.
  local staged_rust_symlinks=()
  local rustlib_target_lib="$rust_tc/lib/rustlib/$rust_target/lib"
  local prefix lib_path lib_name dup_path
  if [[ -d "$rustlib_target_lib" ]]; then
    for prefix in libLLVM librustc_driver-; do
      for lib_path in "$rust_tc"/lib/"$prefix"*; do
        [[ -e "$lib_path" ]] || continue
        lib_name="$(basename "$lib_path")"
        dup_path="$rustlib_target_lib/$lib_name"
        if [[ -f "$lib_path" && ! -L "$lib_path" \
            && -f "$dup_path" && ! -L "$dup_path" ]] \
            && cmp -s "$lib_path" "$dup_path"; then
          tar_args+=(
            --exclude="$rust_base/lib/rustlib/$rust_target/lib/$lib_name"
          )
          mkdir -p \
            "$stage_root/dist_staging/rust/lib/rustlib/$rust_target/lib"
          ln -s "../../../$lib_name" \
            "$stage_root/dist_staging/rust/lib/rustlib/$rust_target/lib/$lib_name"
          staged_rust_symlinks+=(
            "rust/lib/rustlib/$rust_target/lib/$lib_name"
          )
        fi
      done
    done
  fi
  tar_args+=(
    --exclude="$rust_base/lib/libz.so.1"
    --exclude="$rust_base/lib/libgcc_s.so.1"
    --exclude="$rust_base/lib/rustlib/$rust_target/bin/rust-objcopy"
  )
  tar_args+=(
    --transform="flags=r;s:^${lean_esc}\$:lean:;s:^${lean_esc}/:lean/:"
    --transform="flags=r;s:^${rust_esc}\$:rust:;s:^${rust_esc}/:rust/:"
    -cf -
    -C "$stage_root/dist_staging" bin share
    -C "$lean_parent" "$lean_base"
    -C "$rust_parent" "$rust_base"
  )
  if [[ "${#staged_rust_symlinks[@]}" -gt 0 ]]; then
    tar_args+=(
      -C "$stage_root/dist_staging"
      "${staged_rust_symlinks[@]}"
    )
  fi
  tar_args+=(
    -C "$stage_root/dist_staging"
    rust/lib/libz.so.1
    rust/lib/libgcc_s.so.1
  )

  tar "${tar_args[@]}" \
    | zstd -T"${CARGO_BUILD_JOBS:-4}" -12 --long=27 -f -o "$out_archive"

  zstd -dc "$out_archive" | tar -tf - > "$stage_root/archive_entries.txt"
  zstd -dc "$out_archive" | tar -tvf - > "$stage_root/archive_listing.txt"
  if grep -Eqv '^(bin|lean|rust|share)(/|$)' "$stage_root/archive_entries.txt"; then
    echo "ERROR: unexpected top-level entry in omnibus archive" >&2
    exit 1
  fi
  local excluded_patterns=(
    '^lean/include(/|$)'
    '^lean/bin/(lake|leanchecker|clang|ld\.lld|lld|llvm-|leanc|leanir|leantar|cadical|leanmake)'
    '^lean/lib/(clang|libLLVM|libclang)'
    '^lean/lib/.*\.a$'
    '^lean/lib/lean/(Lake(Main)?(/|\.|$)|LeanIR|LeanChecker|Leanc|(Init|Std|Lean)\.ilean$|Lean/.*\.ilean$)'
    '^lean/src/lean/(lake|Lean|Std\.lean$|LeanChecker|LeanIR|Leanc)'
    '^rust/(share|etc|manifest\.in|libexec)(/|$)'
    '^rust/bin/(miri|cargo-miri|rust-gdb|rust-lldb)'
    '^rust/lib/rustlib/(src|rustc-src|etc)(/|$)'
    '^rust/lib/rustlib/.*/bin/(llc|llvm-|opt|wasm-component-ld)'
    '^rust/lib/rustlib/.*/lib/librustc-.*_rt\..*\.a$'
  )
  excluded_patterns+=(
    '^rust/lib/rustlib/.*/bin/rust-objcopy$'
  )
  local pat
  for pat in "${excluded_patterns[@]}"; do
    if grep -Eq "$pat" "$stage_root/archive_entries.txt"; then
      echo "ERROR: excluded payload ($pat) leaked into archive" >&2
      exit 1
    fi
  done
  if grep -Eq \
      "^-.* rust/lib/rustlib/$rust_target/lib/(libLLVM|librustc_driver-)" \
      "$stage_root/archive_listing.txt"; then
    echo "ERROR: duplicate regular-file libLLVM/librustc_driver in archive" >&2
    exit 1
  fi
  local expected_entries=(
    bin/anneal-rustc-capture
    lean/bin/lean
    lean/lib/lean/Init.olean
    lean/lib/lean/Init.ir
    rust/bin/cargo
    rust/bin/rustc
    rust/bin/rustdoc
    share/anneal/correspondence-provenance.json
    share/anneal/prebuilt/manifest.json
    share/anneal/prebuilt/TrustedBoundary.olean
    share/anneal/prebuilt/lib/Trusted/MirAst.olean
    share/anneal/prebuilt/lib/Anneal/MirWp.olean
    share/anneal/prebuilt/lib/Anneal/Scalar.olean
    share/anneal/prebuilt/lib/Anneal/Wp.olean
    share/anneal/trusted/audit/TrustedBoundary.lean
    share/anneal/trusted/audit/library-lock.json
    share/anneal/trusted/lean/foundation-lock.json
    share/anneal/trusted/lean/lean-toolchain
    share/anneal/trusted/lean/Trusted/MirAst.lean
    share/anneal/trusted/lean/Trusted/MirSemantics.lean
    share/anneal/theory/bundle-manifest.json
    share/anneal/theory/Anneal/MirWp.lean
    share/anneal/theory/Anneal/Scalar.lean
    share/anneal/theory/Anneal/Wp.lean
  )
  expected_entries+=(
    rust/lib/libz.so.1
    rust/lib/libgcc_s.so.1
    "rust/lib/rustlib/$rust_target/bin/rust-lld"
    "rust/lib/rustlib/$rust_target/bin/gcc-ld/ld.lld"
    lean/lib/lean/libInit_shared.so
    lean/lib/lean/libLake_shared.so
    lean/lib/lean/libleanshared.so
    lean/lib/lean/libleanshared_1.so
    lean/lib/lean/libleanshared_2.so
  )
  local entry
  for entry in "${expected_entries[@]}"; do
    if ! grep -Fxq -- "$entry" "$stage_root/archive_entries.txt"; then
      echo "ERROR: expected archive entry missing from $out_archive: $entry" >&2
      exit 1
    fi
  done
  for prefix in libLLVM librustc_driver-; do
    if ! grep -Eq "^rust/lib/rustlib/$rust_target/lib/$prefix" \
        "$stage_root/archive_entries.txt"; then
      echo "ERROR: missing $prefix in target rustlib dir" >&2
      exit 1
    fi
  done
  if grep -Eq '^share/anneal/(theory|prebuilt)/.*Canaries' \
    "$stage_root/archive_entries.txt"; then
    echo "ERROR: canary module leaked into share/anneal in $out_archive" >&2
    exit 1
  fi
  if grep -Eq '^share/anneal/(theory/Anneal\.lean|prebuilt/lib/Anneal\.olean)$' \
    "$stage_root/archive_entries.txt"; then
    echo "ERROR: retired monolithic Anneal umbrella leaked into share/anneal in $out_archive" >&2
    exit 1
  fi
  jq -e -r '"share/anneal/" + .modules[].path' "$bundle_manifest" \
    | LC_ALL=C sort -u > "$stage_root/expected_theory_entries.txt"
  grep -E '^share/anneal/theory/.*\.lean$' "$stage_root/archive_entries.txt" \
    | LC_ALL=C sort > "$stage_root/actual_theory_entries.txt"
  local theory_drift
  theory_drift="$(comm -3 \
    "$stage_root/expected_theory_entries.txt" \
    "$stage_root/actual_theory_entries.txt")"
  if [[ -n "$theory_drift" ]]; then
    echo "ERROR: share/anneal/theory Lean files diverge from bundle-manifest.json:" >&2
    printf '%s\n' "$theory_drift" >&2
    exit 1
  fi

  # Verify the four sysroot trees pinned by `library-lock.json` inside the
  # built archive byte for byte, rejecting symlinks.
  rm -rf "$stage_root/lock_check"
  mkdir -p "$stage_root/lock_check"
  zstd -dc "$out_archive" | tar -C "$stage_root/lock_check" -xf - \
    share/anneal/trusted/audit/library-lock.json \
    lean/lib/lean/Init \
    lean/lib/lean/Std \
    lean/src/lean/Init \
    lean/src/lean/Std
  LOCK_CHECK_DIR="$stage_root/lock_check" /usr/bin/python3 -I -B - << 'PYEOF'
import hashlib, os, sys
from pathlib import Path

root = Path(os.environ["LOCK_CHECK_DIR"])
lock = root / "share/anneal/trusted/audit/library-lock.json"
lines = [ln.strip() for ln in lock.read_text(encoding="utf-8").splitlines() if ln.strip()]
if len(lines) != 4:
    sys.exit(f"ERROR: expected 4 library-lock.json entries, found {len(lines)}")
for line in lines:
    expected_sha, label = line.split("  ", 1)
    if not label.endswith("/**"):
        sys.exit(f"ERROR: unexpected library-lock label {label!r}")
    tree_dir = root / label[:-3]
    if tree_dir.is_symlink() or not tree_dir.is_dir():
        sys.exit(f"ERROR: invalid sysroot lock dir {tree_dir}")
    files = []
    for cur, dirs, names in os.walk(tree_dir, followlinks=False):
        cur_p = Path(cur)
        for d in dirs:
            if (cur_p / d).is_symlink():
                sys.exit(f"ERROR: symlink forbidden in sysroot: {cur_p / d}")
        for n in names:
            fp = cur_p / n
            if fp.is_symlink() or not fp.is_file():
                sys.exit(f"ERROR: non-regular file in sysroot: {fp}")
            rel = fp.relative_to(tree_dir).as_posix()
            files.append((rel, fp))
    files.sort(key=lambda item: item[0].encode("utf-8"))
    h = hashlib.sha256()
    for rel, fp in files:
        fh = hashlib.sha256()
        with fp.open("rb") as f:
            while True:
                chunk = f.read(65536)
                if not chunk:
                    break
                fh.update(chunk)
        h.update(rel.encode("utf-8"))
        h.update(b"\0")
        h.update(fh.digest())
    actual_sha = h.hexdigest()
    if actual_sha != expected_sha:
        sys.exit(f"ERROR: library-lock mismatch for {label}: got {actual_sha}, expected {expected_sha}")
print("Verified all 4 library-lock.json sysroot tree digests in archive.")
PYEOF
  rm -rf "$stage_root/lock_check"
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
    rg --version >/dev/null
    ./ci/check_todo.sh
    ./ci/check_non_stable_version.sh
    ./ci/check_actions.sh
    ./ci/check_job_dependencies.sh
    PY_BIN="/usr/bin/python3"
    if [[ -x /opt/anneal-nix/release-check-python/bin/python3 ]]; then
      PY_BIN="/opt/anneal-nix/release-check-python/bin/python3"
    fi
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

  ws-test)
    : "${SHARD_SPEC:?}"
    verify_bwrap_sandbox
    ARCHIVE_PATH="${SCRATCH_ROOT}/anneal-exocrate.tar.zst"
    build_omnibus_archive "$ARCHIVE_PATH"
    INSTALL_CACHE="${SCRATCH_ROOT}/anneal-ws-toolchain"
    INSTALL_ROOT="$INSTALL_CACHE/anneal/toolchain/extracted"
    rm -rf "$INSTALL_CACHE"
    mkdir -p "$INSTALL_ROOT"
    bwrap --unshare-all --die-with-parent --new-session --clearenv \
      --cap-drop ALL --tmpfs / --dev /dev --proc /proc \
      --setenv PATH /usr/bin:/bin \
      --ro-bind /usr /usr \
      --ro-bind-try /bin /bin \
      --ro-bind-try /lib /lib \
      --ro-bind-try /lib64 /lib64 \
      --ro-bind-try /etc/ld.so.cache /etc/ld.so.cache \
      --ro-bind "$ARCHIVE_PATH" /archive.tar.zst \
      --bind "$INSTALL_ROOT" /out \
      -- tar --no-same-owner --zstd -xf /archive.tar.zst -C /out
    rm -f "$ARCHIVE_PATH"
    apply_bundle_env --cache-root "$INSTALL_CACHE" --root "$INSTALL_ROOT"
    if [[ "$SHARD_SPEC" == 1/* ]]; then
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
    fi
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

    # `cargo package` archives only the crate directory, so the packaged
    # build script needs a staged `packaged/bundled_resources.rs`. The
    # checkout is read-only here, so stage it in a scratch copy.
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
      staged="$(cd trusted/cargo-anneal/packaged && find . -mindepth 1)"
      test "$staged" = "./bundled_resources.rs"
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
