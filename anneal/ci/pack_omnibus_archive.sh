#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Canonical omnibus toolchain staging, packing, and single-pass archive
# verification shared by `anneal/flake.nix` and `anneal/ci/run_anneal_check.sh`.
#
# Supports two mutually exclusive output modes:
#   --output-archive <path.tar.zst>  Pack deterministic zstd archive and verify
#                                    entries, leak bans, theory manifest, and
#                                    all 4 `library-lock.json` sysroot digests
#                                    in a single streaming decompression pass.
#   --stage-dir <dir>                Stage the identical trimmed toolchain tree
#                                    directly into `<dir>` via an uncompressed
#                                    tar pipe, skipping zstd compression and
#                                    archive verification.

set -euo pipefail

usage() {
  cat >&2 <<'EOF'
usage: pack_omnibus_archive.sh \
  --rust-toolchain <dir> \
  --lean-toolchain <dir> \
  --rustc-capture-bin <path> \
  --lean-exec <path> \
  --work-dir <dir> \
  (--anneal-root <dir> | explicit source path flags) \
  (--output-archive <path.tar.zst> | --stage-dir <dir>) \
  [--platform <linux|darwin>] \
  [--rust-target <triple>] \
  [--libz <path>] [--libgcc-s <path>] \
  [--python <path>] [--prebuild-jobs <n>] [--zstd-jobs <n>]
EOF
  exit 2
}

platform=""
rust_tc=""
lean_tc=""
rust_target=""
lean_exec=""
rustc_capture_bin=""
anneal_root=""
lean_foundation=""
lean_theory=""
target_spec_preflight=""
target_inspector=""
target_library_lock=""
trusted_bundle_source=""
upstream_pin=""
minirust_upstream_pin=""
correspondence_adapters=""
correspondence_proofs=""
render_provenance_script=""
prebuild_oleans_script=""
libz_path=""
libgcc_s_path=""
python_bin="python3"
work_dir=""
prebuild_jobs="4"
zstd_jobs="4"
out_archive=""
stage_dir=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --platform)
      [[ $# -ge 2 ]] || usage
      platform="$2"
      shift 2
      ;;
    --rust-toolchain)
      [[ $# -ge 2 ]] || usage
      rust_tc="$2"
      shift 2
      ;;
    --lean-toolchain)
      [[ $# -ge 2 ]] || usage
      lean_tc="$2"
      shift 2
      ;;
    --rust-target)
      [[ $# -ge 2 ]] || usage
      rust_target="$2"
      shift 2
      ;;
    --lean-exec)
      [[ $# -ge 2 ]] || usage
      lean_exec="$2"
      shift 2
      ;;
    --rustc-capture-bin)
      [[ $# -ge 2 ]] || usage
      rustc_capture_bin="$2"
      shift 2
      ;;
    --anneal-root)
      [[ $# -ge 2 ]] || usage
      anneal_root="$2"
      shift 2
      ;;
    --lean-foundation)
      [[ $# -ge 2 ]] || usage
      lean_foundation="$2"
      shift 2
      ;;
    --lean-theory)
      [[ $# -ge 2 ]] || usage
      lean_theory="$2"
      shift 2
      ;;
    --target-spec-preflight)
      [[ $# -ge 2 ]] || usage
      target_spec_preflight="$2"
      shift 2
      ;;
    --target-inspector)
      [[ $# -ge 2 ]] || usage
      target_inspector="$2"
      shift 2
      ;;
    --target-library-lock)
      [[ $# -ge 2 ]] || usage
      target_library_lock="$2"
      shift 2
      ;;
    --trusted-bundle-source)
      [[ $# -ge 2 ]] || usage
      trusted_bundle_source="$2"
      shift 2
      ;;
    --upstream-pin)
      [[ $# -ge 2 ]] || usage
      upstream_pin="$2"
      shift 2
      ;;
    --minirust-upstream-pin)
      [[ $# -ge 2 ]] || usage
      minirust_upstream_pin="$2"
      shift 2
      ;;
    --correspondence-adapters)
      [[ $# -ge 2 ]] || usage
      correspondence_adapters="$2"
      shift 2
      ;;
    --correspondence-proofs)
      [[ $# -ge 2 ]] || usage
      correspondence_proofs="$2"
      shift 2
      ;;
    --render-provenance-script)
      [[ $# -ge 2 ]] || usage
      render_provenance_script="$2"
      shift 2
      ;;
    --prebuild-oleans-script)
      [[ $# -ge 2 ]] || usage
      prebuild_oleans_script="$2"
      shift 2
      ;;
    --libz)
      [[ $# -ge 2 ]] || usage
      libz_path="$2"
      shift 2
      ;;
    --libgcc-s)
      [[ $# -ge 2 ]] || usage
      libgcc_s_path="$2"
      shift 2
      ;;
    --python)
      [[ $# -ge 2 ]] || usage
      python_bin="$2"
      shift 2
      ;;
    --work-dir)
      [[ $# -ge 2 ]] || usage
      work_dir="$2"
      shift 2
      ;;
    --prebuild-jobs)
      [[ $# -ge 2 ]] || usage
      prebuild_jobs="$2"
      shift 2
      ;;
    --zstd-jobs)
      [[ $# -ge 2 ]] || usage
      zstd_jobs="$2"
      shift 2
      ;;
    --output-archive)
      [[ $# -ge 2 ]] || usage
      out_archive="$2"
      shift 2
      ;;
    --stage-dir)
      [[ $# -ge 2 ]] || usage
      stage_dir="$2"
      shift 2
      ;;
    *)
      echo "ERROR: unknown argument: $1" >&2
      usage
      ;;
  esac
done

if [[ -n "$anneal_root" ]]; then
  : "${lean_foundation:=$anneal_root/trusted/lean}"
  : "${lean_theory:=$anneal_root/theory}"
  : "${target_spec_preflight:=$anneal_root/trusted/audit/SpecPreflight.lean}"
  : "${target_inspector:=$anneal_root/trusted/audit/TrustedBoundary.lean}"
  : "${target_library_lock:=$anneal_root/trusted/audit/library-lock.json}"
  : "${trusted_bundle_source:=$anneal_root/trusted/cargo-anneal/src/trusted_bundle.rs}"
  : "${upstream_pin:=$anneal_root/vendor/lean-miri/UPSTREAM_PIN.json}"
  : "${minirust_upstream_pin:=$anneal_root/vendor/minirust/UPSTREAM_PIN.json}"
  : "${correspondence_adapters:=$anneal_root/trusted/correspondence}"
  : "${correspondence_proofs:=$anneal_root/correspondence}"
  : "${render_provenance_script:=$anneal_root/ci/render_correspondence_provenance.py}"
  : "${prebuild_oleans_script:=$anneal_root/ci/prebuild_bundled_oleans.py}"
fi

if [[ -n "$out_archive" && -n "$stage_dir" ]] || [[ -z "$out_archive" && -z "$stage_dir" ]]; then
  echo "ERROR: specify exactly one of --output-archive or --stage-dir" >&2
  exit 2
fi

for req_var in \
  rust_tc lean_tc lean_exec rustc_capture_bin work_dir \
  lean_foundation lean_theory target_spec_preflight target_inspector target_library_lock \
  trusted_bundle_source upstream_pin minirust_upstream_pin correspondence_adapters \
  correspondence_proofs render_provenance_script prebuild_oleans_script; do
  if [[ -z "${!req_var}" ]]; then
    echo "ERROR: missing required parameter: $req_var" >&2
    exit 2
  fi
done

if [[ ! -d "$rust_tc" ]]; then
  echo "ERROR: missing rust toolchain directory: $rust_tc" >&2
  exit 1
fi
if [[ ! -d "$lean_tc" ]]; then
  echo "ERROR: missing lean toolchain directory: $lean_tc" >&2
  exit 1
fi
# Canonicalize directories passed to `tar -C` so relative `--work-dir`,
# `--rust-toolchain`, or `--lean-toolchain` arguments cannot interact with GNU
# `tar`'s cumulative `-C` resolution when `staged_rust_symlinks` is non-empty.
mkdir -p "$work_dir"
work_dir="$(CDPATH='' cd -P -- "$work_dir" && pwd)"
rust_tc="$(CDPATH='' cd -P -- "$rust_tc" && pwd)"
lean_tc="$(CDPATH='' cd -P -- "$lean_tc" && pwd)"

if [[ -z "$rust_target" ]]; then
  rust_target_lines="$(
    LD_LIBRARY_PATH="$rust_tc/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
      "$rust_tc/bin/rustc" -vV | sed -n 's/^host: //p'
  )"
  if [[ ! "$rust_target_lines" =~ ^[A-Za-z0-9_.-]+$ ]]; then
    echo "ERROR: cannot derive one rustc host triple: $rust_target_lines" >&2
    exit 1
  fi
  rust_target="$rust_target_lines"
fi

if [[ ! -d "$rust_tc/lib/rustlib/$rust_target" ]]; then
  echo "ERROR: missing rustlib tree for $rust_target in $rust_tc" >&2
  exit 1
fi

if [[ -z "$platform" ]]; then
  case "$rust_target" in
    *-linux-*) platform="linux" ;;
    *-darwin) platform="darwin" ;;
    *)
      echo "ERROR: cannot infer platform from rust target: $rust_target" >&2
      exit 1
      ;;
  esac
fi

case "$platform" in
  linux)
    if [[ -z "$libz_path" || -z "$libgcc_s_path" ]]; then
      echo "ERROR: --libz and --libgcc-s are required on linux" >&2
      exit 2
    fi
    ;;
  darwin) ;;
  *)
    echo "ERROR: unsupported platform: $platform" >&2
    exit 2
    ;;
esac

if ! [[ "$prebuild_jobs" =~ ^[0-9]+$ ]] || [[ "$prebuild_jobs" -le 0 ]] || [[ "$prebuild_jobs" -gt 4 ]]; then
  prebuild_jobs=4
fi
if ! [[ "$zstd_jobs" =~ ^[0-9]+$ ]]; then
  zstd_jobs=4
fi

dist_staging="$work_dir/dist_staging"
rm -rf "$dist_staging" "$work_dir/prebuild_src" "$work_dir/theory_manifest_paths.txt"
mkdir -p \
  "$dist_staging/bin" \
  "$dist_staging/share/anneal/trusted/audit" \
  "$dist_staging/share/anneal/theory"

install -m 0755 "$rustc_capture_bin" "$dist_staging/bin/anneal-rustc-capture"
cp -r "$lean_foundation" "$dist_staging/share/anneal/trusted/lean"
cp "$lean_theory/bundle-manifest.json" \
  "$dist_staging/share/anneal/theory/bundle-manifest.json"

jq -e -r '.modules[].path' "$lean_theory/bundle-manifest.json" \
  > "$work_dir/theory_manifest_paths.txt"
test -s "$work_dir/theory_manifest_paths.txt"
while IFS= read -r rel_path; do
  case "$rel_path" in
    *..*|*Canaries*)
      echo "ERROR: forbidden bundle-manifest path: $rel_path" >&2
      exit 1
      ;;
    theory/Anneal/*.lean)
      sub_path="${rel_path#theory/}"
      install -D -m 0644 \
        "$lean_theory/$sub_path" \
        "$dist_staging/share/anneal/theory/$sub_path"
      ;;
    *)
      echo "ERROR: unexpected bundle-manifest path: $rel_path" >&2
      exit 1
      ;;
  esac
done < "$work_dir/theory_manifest_paths.txt"

cp "$target_spec_preflight" "$dist_staging/share/anneal/trusted/audit/SpecPreflight.lean"
cp "$target_inspector" "$dist_staging/share/anneal/trusted/audit/TrustedBoundary.lean"
cp "$target_library_lock" "$dist_staging/share/anneal/trusted/audit/library-lock.json"

# Render correspondence provenance directly from the canonical inputs so
# archive metadata and `cargo-anneal verify` receipts share one deterministic
# schema and inventory.
"$python_bin" -I -B "$render_provenance_script" \
  --trusted-bundle-rs "$trusted_bundle_source" \
  --upstream-pin "$upstream_pin" \
  --minirust-upstream-pin "$minirust_upstream_pin" \
  --correspondence-adapters-dir "$correspondence_adapters" \
  --correspondence-proofs-dir "$correspondence_proofs" \
  --trusted-lean-dir "$lean_foundation" \
  --output "$dist_staging/share/anneal/correspondence-provenance.json"
jq -e 'type == "object" and .schema_version == 1' \
  "$dist_staging/share/anneal/correspondence-provenance.json" \
  > /dev/null

chmod -R u+w "$dist_staging"

# Prebuild deterministic, content-addressed `.olean` artifacts for
# `TrustedBoundary.lean`, `SpecPreflight.lean`, `Trusted.*`, and bundled
# `Anneal.*` theory modules so cold `cargo-anneal verify` reuses them across
# invocations without lowering verification replay coverage.
mkdir -p "$work_dir/prebuild_src/trusted/cargo-anneal/src"
cp "$trusted_bundle_source" "$work_dir/prebuild_src/trusted/cargo-anneal/src/trusted_bundle.rs"
cp -r "$dist_staging/share/anneal/trusted/audit" "$work_dir/prebuild_src/trusted/audit"
cp -r "$dist_staging/share/anneal/trusted/lean" "$work_dir/prebuild_src/trusted/lean"
cp -r "$dist_staging/share/anneal/theory" "$work_dir/prebuild_src/theory"
"$python_bin" -I -B "$prebuild_oleans_script" \
  --anneal-root "$work_dir/prebuild_src" \
  --lean-bin "$lean_tc/bin/lean" \
  --lean-exec "$lean_exec" \
  --lean-prefix "$lean_tc" \
  --output-dir "$dist_staging/share/anneal/prebuilt" \
  --jobs "$prebuild_jobs"
chmod -R u+w "$dist_staging/share/anneal/prebuilt"
rm -rf "$work_dir/prebuild_src"

if [[ "$platform" == "linux" ]]; then
  # Carry the compiler's non-libc runtime dependencies beside its libraries.
  # Dereference symlinks so relocation cannot silently depend on the build
  # machine's store.
  mkdir -p "$dist_staging/rust/lib"
  cp -L "$libz_path" "$dist_staging/rust/lib/libz.so.1"
  cp -L "$libgcc_s_path" "$dist_staging/rust/lib/libgcc_s.so.1"
  chmod u+w \
    "$dist_staging/rust/lib/libz.so.1" \
    "$dist_staging/rust/lib/libgcc_s.so.1"

  # Point `anneal-rustc-capture` at the standard Linux dynamic linker used by
  # upstream `rustc`, ensure direct `libz.so.1` DT_NEEDED without duplicating
  # an existing entry (Nix's `rustc-capture` postFixup already adds it), and
  # set relative `$ORIGIN` RPATH. `rust/` and `lean/` stay unpacked directly
  # from upstream release archives.
  interp="$(patchelf --print-interpreter "$rust_tc/bin/rustc")"
  needed_libs="$(patchelf --print-needed "$dist_staging/bin/anneal-rustc-capture")"
  patchelf_args=(
    --set-interpreter "$interp"
    --set-rpath '$ORIGIN/../rust/lib'
  )
  if ! grep -Fxq "libz.so.1" <<< "$needed_libs"; then
    patchelf_args=(--add-needed libz.so.1 "${patchelf_args[@]}")
  fi
  patchelf "${patchelf_args[@]}" "$dist_staging/bin/anneal-rustc-capture"

  # Fail closed at build time if any Nix-store dynamic linker, RPATH, or
  # DT_NEEDED reference remains or if bundled runtime libraries are missing
  # from the staged toolchain/lib dirs.
  interp="$(patchelf --print-interpreter "$dist_staging/bin/anneal-rustc-capture")"
  rpath="$(patchelf --print-rpath "$dist_staging/bin/anneal-rustc-capture")"
  # Use here-strings, not pipelines: under `pipefail`, an early `grep -q` exit
  # could SIGPIPE a multi-write producer and flip the condition.
  if [[ -z "$interp" ]] \
      || grep -Fq '/nix/store/' <<< "$interp" \
      || grep -Fq '/nix/store/' <<< "$rpath"; then
    echo "ERROR: Nix store reference leaked into ELF header ($interp / $rpath)" >&2
    exit 1
  fi
  if [[ "$rpath" != '$ORIGIN/../rust/lib' ]]; then
    echo "ERROR: unexpected ELF RPATH in anneal-rustc-capture: $rpath" >&2
    exit 1
  fi
  needed_libs="$(patchelf --print-needed "$dist_staging/bin/anneal-rustc-capture")"
  if [[ -z "$needed_libs" ]]; then
    echo "ERROR: empty DT_NEEDED list for anneal-rustc-capture" >&2
    exit 1
  fi
  while IFS= read -r needed; do
    [[ -z "$needed" ]] && continue
    if grep -Fq '/nix/store/' <<< "$needed"; then
      echo "ERROR: Nix store DT_NEEDED entry in anneal-rustc-capture: $needed" >&2
      exit 1
    fi
    case "$needed" in
      librustc_driver*|libLLVM*|libz.so.1|libgcc_s.so.1)
        if [[ ! -e "$rust_tc/lib/$needed" && ! -e "$dist_staging/rust/lib/$needed" ]]; then
          echo "ERROR: missing staged runtime dependency $needed for anneal-rustc-capture" >&2
          exit 1
        fi
        ;;
      ld-linux*.so.*|libc.so.6|libm.so.6|libdl.so.2|libpthread.so.0|librt.so.1)
        ;;
      *)
        echo "ERROR: unexpected DT_NEEDED dependency $needed in anneal-rustc-capture" >&2
        exit 1
        ;;
    esac
  done <<< "$needed_libs"
elif [[ "$platform" == "darwin" ]]; then
  # Strip Nix-store dylib and LC_RPATH references so the Darwin driver
  # resolves system libraries and bundled `rust/lib/` via
  # `@executable_path/../rust/lib` outside any Nix store.
  capture_bin="$dist_staging/bin/anneal-rustc-capture"
  otool_libs="$(otool -L "$capture_bin")"
  otool_cmds="$(otool -l "$capture_bin")"
  if [[ -z "$otool_libs" || -z "$otool_cmds" ]]; then
    echo "ERROR: failed to inspect Mach-O headers for anneal-rustc-capture" >&2
    exit 1
  fi
  dylibs="$(awk 'NR > 1 { print $1 }' <<< "$otool_libs")"
  while IFS= read -r dylib; do
    [[ -z "$dylib" ]] && continue
    case "$dylib" in
      /nix/store/*/lib/libiconv.dylib|/nix/store/*/lib/libiconv.*.dylib)
        install_name_tool -change "$dylib" /usr/lib/libiconv.2.dylib "$capture_bin"
        ;;
      /nix/store/*/lib/libz.dylib|/nix/store/*/lib/libz.*.dylib)
        install_name_tool -change "$dylib" /usr/lib/libz.1.dylib "$capture_bin"
        ;;
      /nix/store/*)
        echo "ERROR: unexpected Nix store dylib in anneal-rustc-capture: $dylib" >&2
        exit 1
        ;;
    esac
  done <<< "$dylibs"
  rpaths="$(awk '
    $1 == "cmd" && $2 == "LC_RPATH" { in_rpath = 1; next }
    in_rpath && $1 == "path" { print $2; in_rpath = 0 }
  ' <<< "$otool_cmds")"
  has_target_rpath=0
  while IFS= read -r rp; do
    [[ -z "$rp" ]] && continue
    case "$rp" in
      /nix/store/*)
        install_name_tool -delete_rpath "$rp" "$capture_bin"
        ;;
      '@executable_path/../rust/lib')
        has_target_rpath=1
        ;;
    esac
  done <<< "$rpaths"
  if [[ "$has_target_rpath" -ne 1 ]]; then
    install_name_tool -add_rpath '@executable_path/../rust/lib' "$capture_bin"
  fi
  codesign -s - --force "$capture_bin"
  post_otool_libs="$(otool -L "$capture_bin")"
  post_otool_cmds="$(otool -l "$capture_bin")"
  if [[ -z "$post_otool_libs" || -z "$post_otool_cmds" ]]; then
    echo "ERROR: failed to re-inspect Mach-O headers for anneal-rustc-capture" >&2
    exit 1
  fi
  if grep -Fq '/nix/store/' <<< "$post_otool_libs" \
      || grep -Fq '/nix/store/' <<< "$post_otool_cmds"; then
    echo "ERROR: Nix store reference leaked into Darwin Mach-O load commands" >&2
    exit 1
  fi
  post_rpaths="$(awk '
    $1 == "cmd" && $2 == "LC_RPATH" { in_rpath = 1; next }
    in_rpath && $1 == "path" { print $2; in_rpath = 0 }
  ' <<< "$post_otool_cmds")"
  if [[ "$post_rpaths" != '@executable_path/../rust/lib' ]]; then
    echo "ERROR: unexpected Darwin LC_RPATH in anneal-rustc-capture: $post_rpaths" >&2
    exit 1
  fi
fi

for full_path in \
  "$dist_staging/bin/anneal-rustc-capture" \
  "$lean_tc/bin/lean" \
  "$rust_tc/bin/cargo" \
  "$rust_tc/bin/rustc" \
  "$dist_staging/share/anneal/correspondence-provenance.json" \
  "$dist_staging/share/anneal/prebuilt/manifest.json" \
  "$dist_staging/share/anneal/prebuilt/SpecPreflight.olean" \
  "$dist_staging/share/anneal/prebuilt/TrustedBoundary.olean" \
  "$dist_staging/share/anneal/prebuilt/lib/Trusted/MirAst.olean" \
  "$dist_staging/share/anneal/prebuilt/lib/Anneal/MirWp.olean" \
  "$dist_staging/share/anneal/prebuilt/lib/Anneal/Scalar.olean" \
  "$dist_staging/share/anneal/prebuilt/lib/Anneal/Wp.olean" \
  "$dist_staging/share/anneal/trusted/audit/SpecPreflight.lean" \
  "$dist_staging/share/anneal/trusted/audit/TrustedBoundary.lean" \
  "$dist_staging/share/anneal/trusted/audit/library-lock.json" \
  "$dist_staging/share/anneal/trusted/lean/foundation-lock.json" \
  "$dist_staging/share/anneal/trusted/lean/lean-toolchain" \
  "$dist_staging/share/anneal/trusted/lean/Trusted/MirAst.lean" \
  "$dist_staging/share/anneal/trusted/lean/Trusted/MirSemantics.lean" \
  "$dist_staging/share/anneal/theory/bundle-manifest.json" \
  "$dist_staging/share/anneal/theory/Anneal/MirWp.lean" \
  "$dist_staging/share/anneal/theory/Anneal/Scalar.lean" \
  "$dist_staging/share/anneal/theory/Anneal/Wp.lean"; do
  if [[ ! -f "$full_path" ]]; then
    echo "ERROR: expected archive entry missing: $full_path" >&2
    exit 1
  fi
done

# Stream `lean/` and `rust/` directly from their verified store paths without
# copying 3.3 GiB into `$work_dir`. `flags=r` rewrites member paths without
# altering internal `.so` symlink targets, `--hard-dereference` breaks store
# hardlinks into standalone files, `--mode='u+w'` makes entries writable, and
# `--sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner` keeps archive
# output deterministic.
lean_parent="$(dirname "$lean_tc")"
lean_base="$(basename "$lean_tc")"
lean_esc="$(printf '%s' "$lean_base" | sed 's/[.[\*^$:]/\\&/g')"
rust_parent="$(dirname "$rust_tc")"
rust_base="$(basename "$rust_tc")"
rust_esc="$(printf '%s' "$rust_base" | sed 's/[.[\*^$:]/\\&/g')"

tar_args=(
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
staged_rust_symlinks=()
rustlib_target_lib="$rust_tc/lib/rustlib/$rust_target/lib"
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
        mkdir -p "$dist_staging/rust/lib/rustlib/$rust_target/lib"
        ln -s "../../../$lib_name" \
          "$dist_staging/rust/lib/rustlib/$rust_target/lib/$lib_name"
        staged_rust_symlinks+=(
          "rust/lib/rustlib/$rust_target/lib/$lib_name"
        )
      fi
    done
  done
fi

if [[ "$platform" == "linux" ]]; then
  tar_args+=(
    --exclude="$rust_base/lib/libz.so.1"
    --exclude="$rust_base/lib/libgcc_s.so.1"
    --exclude="$rust_base/lib/rustlib/$rust_target/bin/rust-objcopy"
  )
fi

tar_args+=(
  --transform="flags=r;s:^${lean_esc}\$:lean:;s:^${lean_esc}/:lean/:"
  --transform="flags=r;s:^${rust_esc}\$:rust:;s:^${rust_esc}/:rust/:"
  -cf -
  -C "$dist_staging" bin share
  -C "$lean_parent" "$lean_base"
  -C "$rust_parent" "$rust_base"
)

if [[ "${#staged_rust_symlinks[@]}" -gt 0 ]]; then
  tar_args+=(
    -C "$dist_staging"
    "${staged_rust_symlinks[@]}"
  )
fi

if [[ "$platform" == "linux" ]]; then
  tar_args+=(
    -C "$dist_staging"
    rust/lib/libz.so.1
    rust/lib/libgcc_s.so.1
  )
fi

if [[ -n "$stage_dir" ]]; then
  rm -rf "$stage_dir"
  mkdir -p "$stage_dir"
  tar "${tar_args[@]}" | tar --no-same-owner -xf - -C "$stage_dir"
  rm -rf "$dist_staging" "$work_dir/theory_manifest_paths.txt"
  exit 0
fi

# Compress with zstd -12 --long=27 (128 MiB window, matching the default
# libzstd ZSTD_WINDOWLOG_LIMIT_DEFAULT used by exocrate).
tar "${tar_args[@]}" | zstd -T"$zstd_jobs" -12 --long=27 -f -o "$out_archive"

# Verify the produced archive in a single streaming decompression pass:
# top-level confinement, excluded payload leak bans, duplicate regular-file
# `libLLVM` / `librustc_driver` bans, required entries, `bundle-manifest.json`
# theory parity, and byte-for-byte SHA-256 verification of all 4
# `library-lock.json` sysroot trees (rejecting symlinks and non-regular files).
cat > "$work_dir/verify_archive.py" <<'PYEOF'
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tarfile

out_archive = os.environ["OUT_ARCHIVE"]
platform = os.environ["PLATFORM"]
rust_target = os.environ["RUST_TARGET"]
bundle_manifest_path = Path(os.environ["BUNDLE_MANIFEST"])
staged_lock_path = Path(os.environ["STAGED_LIBRARY_LOCK"])

staged_lock_bytes = staged_lock_path.read_bytes()
lock_lines = [
    ln.strip()
    for ln in staged_lock_bytes.decode("utf-8").splitlines()
    if ln.strip()
]
if len(lock_lines) != 4:
    sys.exit(f"ERROR: expected 4 library-lock.json entries, found {len(lock_lines)}")

lock_specs: list[tuple[str, str, str]] = []
lock_prefixes: set[str] = set()
lock_ancestors: set[str] = set()
for line in lock_lines:
    expected_sha, label = line.split("  ", 1)
    if not label.endswith("/**"):
        sys.exit(f"ERROR: unexpected library-lock label {label!r}")
    prefix = label[:-3]
    if not prefix or prefix.startswith("/") or ".." in prefix.split("/"):
        sys.exit(f"ERROR: invalid sysroot lock dir {prefix!r}")
    lock_specs.append((expected_sha, label, prefix))
    lock_prefixes.add(prefix)
    parts = prefix.split("/")
    for i in range(1, len(parts) + 1):
        lock_ancestors.add("/".join(parts[:i]))

excluded_patterns = [
    r"^lean/include(/|$)",
    r"^lean/bin/(lake|leanchecker|clang|ld\.lld|lld|llvm-|leanc|leanir|leantar|cadical|leanmake)",
    r"^lean/lib/(clang|libLLVM|libclang)",
    r"^lean/lib/.*\.a$",
    r"^lean/lib/lean/(Lake(Main)?(/|\.|$)|LeanIR|LeanChecker|Leanc|(Init|Std|Lean)\.ilean$|Lean/.*\.ilean$)",
    r"^lean/src/lean/(lake|Lean|Std\.lean$|LeanChecker|LeanIR|Leanc)",
    r"^rust/(share|etc|manifest\.in|libexec)(/|$)",
    r"^rust/bin/(miri|cargo-miri|rust-gdb|rust-lldb)",
    r"^rust/lib/rustlib/(src|rustc-src|etc)(/|$)",
    r"^rust/lib/rustlib/.*/bin/(llc|llvm-|opt|wasm-component-ld)",
    r"^rust/lib/rustlib/.*/lib/librustc-.*_rt\..*\.a$",
]
if platform == "linux":
    excluded_patterns.append(r"^rust/lib/rustlib/.*/bin/rust-objcopy$")
compiled_excluded = [(pat, re.compile(pat)) for pat in excluded_patterns]

top_level_re = re.compile(r"^(bin|lean|rust|share)(/|$)")
dup_lib_re = re.compile(
    rf"^rust/lib/rustlib/{re.escape(rust_target)}/lib/(libLLVM|librustc_driver-)"
)
canary_re = re.compile(r"^share/anneal/(theory|prebuilt)/.*Canaries")
retired_umbrella_names = frozenset(
    {
        "share/anneal/theory/Anneal.lean",
        "share/anneal/prebuilt/lib/Anneal.olean",
    }
)

seen_entries: set[str] = set()
seen_non_dir_entries: set[str] = set()
seen_lock_dirs: set[str] = set()
lock_files: dict[str, dict[str, bytes]] = {prefix: {} for prefix in lock_prefixes}
archived_lock_bytes: bytes | None = None

with tarfile.open(fileobj=sys.stdin.buffer, mode="r|") as tf:
    for member in tf:
        name = member.name.rstrip("/")
        if not top_level_re.match(name):
            sys.exit(f"ERROR: unexpected top-level entry in omnibus archive: {name}")
        for pat, rx in compiled_excluded:
            if rx.search(name):
                sys.exit(f"ERROR: excluded payload ({pat}) leaked into archive: {name}")
        if member.isreg() and dup_lib_re.match(name):
            sys.exit(
                f"ERROR: duplicate regular-file libLLVM/librustc_driver in archive: {name}"
            )
        if canary_re.search(name):
            sys.exit(f"ERROR: canary module leaked into share/anneal in {out_archive}: {name}")
        if name in retired_umbrella_names:
            sys.exit(
                f"ERROR: retired monolithic Anneal umbrella leaked into share/anneal in {out_archive}: {name}"
            )

        if name in seen_entries:
            sys.exit(f"ERROR: duplicate archive entry in {out_archive}: {name}")
        seen_entries.add(name)
        if member.isreg() or member.issym():
            seen_non_dir_entries.add(name)

        if name == "share/anneal/trusted/audit/library-lock.json":
            if not member.isreg():
                sys.exit("ERROR: archived library-lock.json is not a regular file")
            fobj = tf.extractfile(member)
            if fobj is None:
                sys.exit("ERROR: unable to read archived library-lock.json")
            archived_lock_bytes = fobj.read()

        if name in lock_ancestors:
            if member.issym() or member.islnk():
                sys.exit(f"ERROR: symlink forbidden in sysroot: {name}")
            if not member.isdir():
                sys.exit(f"ERROR: invalid sysroot lock dir {name}")
            if name in lock_prefixes:
                seen_lock_dirs.add(name)
            continue

        for prefix in lock_prefixes:
            if name.startswith(prefix + "/"):
                if member.issym() or member.islnk():
                    sys.exit(f"ERROR: symlink forbidden in sysroot: {name}")
                if member.isdir():
                    break
                if not member.isreg():
                    sys.exit(f"ERROR: non-regular file in sysroot: {name}")
                rel = name[len(prefix) + 1 :]
                if rel in lock_files[prefix]:
                    sys.exit(f"ERROR: duplicate sysroot archive entry: {name}")
                fobj = tf.extractfile(member)
                if fobj is None:
                    sys.exit(f"ERROR: unable to read sysroot archive entry: {name}")
                fh = hashlib.sha256()
                while True:
                    chunk = fobj.read(65536)
                    if not chunk:
                        break
                    fh.update(chunk)
                lock_files[prefix][rel] = fh.digest()
                break

# Drain any trailing tar padding so upstream `zstd -dc` exits cleanly without
# SIGPIPE.
while sys.stdin.buffer.read(65536):
    pass

expected_entries = [
    "bin/anneal-rustc-capture",
    "lean/bin/lean",
    "lean/lib/lean/Init.olean",
    "lean/lib/lean/Init.ir",
    "rust/bin/cargo",
    "rust/bin/rustc",
    "rust/bin/rustdoc",
    "share/anneal/correspondence-provenance.json",
    "share/anneal/prebuilt/manifest.json",
    "share/anneal/prebuilt/SpecPreflight.olean",
    "share/anneal/prebuilt/TrustedBoundary.olean",
    "share/anneal/prebuilt/lib/Trusted/MirAst.olean",
    "share/anneal/prebuilt/lib/Anneal/MirWp.olean",
    "share/anneal/prebuilt/lib/Anneal/Scalar.olean",
    "share/anneal/prebuilt/lib/Anneal/Wp.olean",
    "share/anneal/trusted/audit/SpecPreflight.lean",
    "share/anneal/trusted/audit/TrustedBoundary.lean",
    "share/anneal/trusted/audit/library-lock.json",
    "share/anneal/trusted/lean/foundation-lock.json",
    "share/anneal/trusted/lean/lean-toolchain",
    "share/anneal/trusted/lean/Trusted/MirAst.lean",
    "share/anneal/trusted/lean/Trusted/MirSemantics.lean",
    "share/anneal/theory/bundle-manifest.json",
    "share/anneal/theory/Anneal/MirWp.lean",
    "share/anneal/theory/Anneal/Scalar.lean",
    "share/anneal/theory/Anneal/Wp.lean",
]
if platform == "linux":
    expected_entries.extend(
        [
            "rust/lib/libz.so.1",
            "rust/lib/libgcc_s.so.1",
            f"rust/lib/rustlib/{rust_target}/bin/rust-lld",
            f"rust/lib/rustlib/{rust_target}/bin/gcc-ld/ld.lld",
            "lean/lib/lean/libInit_shared.so",
            "lean/lib/lean/libLake_shared.so",
            "lean/lib/lean/libleanshared.so",
            "lean/lib/lean/libleanshared_1.so",
            "lean/lib/lean/libleanshared_2.so",
        ]
    )

for entry in expected_entries:
    if entry not in seen_non_dir_entries:
        sys.exit(
            f"ERROR: expected archive entry missing or not a file/symlink in {out_archive}: {entry}"
        )

if platform == "linux":
    for lib_prefix in ("libLLVM", "librustc_driver-"):
        target_prefix = f"rust/lib/rustlib/{rust_target}/lib/{lib_prefix}"
        if not any(e.startswith(target_prefix) for e in seen_non_dir_entries):
            sys.exit(f"ERROR: missing {lib_prefix} in target rustlib dir")

manifest = json.loads(bundle_manifest_path.read_text(encoding="utf-8"))
expected_theory = {
    f"share/anneal/{m['path']}" for m in manifest["modules"]
}
actual_theory = {
    e
    for e in seen_non_dir_entries
    if e.startswith("share/anneal/theory/") and e.endswith(".lean")
}
if expected_theory != actual_theory:
    missing = sorted(expected_theory - actual_theory)
    extra = sorted(actual_theory - expected_theory)
    sys.exit(
        "ERROR: share/anneal/theory Lean files diverge from bundle-manifest.json: "
        f"missing={missing} extra={extra}"
    )

if archived_lock_bytes is None:
    sys.exit("ERROR: missing share/anneal/trusted/audit/library-lock.json in archive")
if archived_lock_bytes != staged_lock_bytes:
    sys.exit("ERROR: archived library-lock.json diverges from staged lockfile")

for expected_sha, label, prefix in lock_specs:
    if prefix not in seen_lock_dirs and not lock_files[prefix]:
        sys.exit(f"ERROR: invalid sysroot lock dir {prefix}")
    h = hashlib.sha256()
    for rel, digest in sorted(
        lock_files[prefix].items(), key=lambda item: item[0].encode("utf-8")
    ):
        h.update(rel.encode("utf-8"))
        h.update(b"\0")
        h.update(digest)
    actual_sha = h.hexdigest()
    if actual_sha != expected_sha:
        sys.exit(
            f"ERROR: library-lock mismatch for {label}: "
            f"got {actual_sha}, expected {expected_sha}"
        )

print("Verified all 4 library-lock.json sysroot tree digests in archive.")
PYEOF

zstd -dc "$out_archive" | \
  OUT_ARCHIVE="$out_archive" \
  PLATFORM="$platform" \
  RUST_TARGET="$rust_target" \
  BUNDLE_MANIFEST="$lean_theory/bundle-manifest.json" \
  STAGED_LIBRARY_LOCK="$dist_staging/share/anneal/trusted/audit/library-lock.json" \
  "$python_bin" -I -B "$work_dir/verify_archive.py"

rm -rf "$dist_staging" "$work_dir/theory_manifest_paths.txt" "$work_dir/verify_archive.py"
