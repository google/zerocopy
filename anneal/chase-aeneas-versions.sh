#!/usr/bin/env bash
# Chase the version inputs that are coupled to an Aeneas release asset.

set -euo pipefail

usage() {
  cat >&2 <<'USAGE'
usage: chase-aeneas-versions.sh RELEASE_TAG [--target linux-x86_64] [--work-dir DIR] [--keep]

Downloads an Aeneas release archive, extracts the Lean and Rust toolchain
versions it was built against, and computes the recursive Nix hashes used by
flake.nix for the matching Lean and Rust toolchain directories.

The mathlib-cache-download output hash depends on Lake's CDN cache result and
is reported as a follow-up Nix fixed-output hash to refresh after these values.
USAGE
}

target=linux-x86_64
work_dir=
keep=0

if [[ $# -lt 1 ]]; then
  usage
  exit 2
fi

release_tag=$1
shift

while [[ $# -gt 0 ]]; do
  case "$1" in
    --target)
      target=${2:?missing --target value}
      shift 2
      ;;
    --work-dir)
      work_dir=${2:?missing --work-dir value}
      shift 2
      ;;
    --keep)
      keep=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      usage
      exit 2
      ;;
  esac
done

case "$target" in
  linux-x86_64)
    rust_platform=x86_64-unknown-linux-gnu
    lean_platform=linux
    ;;
  linux-aarch64)
    rust_platform=aarch64-unknown-linux-gnu
    lean_platform=linux_aarch64
    ;;
  macos-x86_64)
    rust_platform=x86_64-apple-darwin
    lean_platform=darwin
    ;;
  macos-aarch64)
    rust_platform=aarch64-apple-darwin
    lean_platform=darwin_aarch64
    ;;
  *)
    echo "unsupported Aeneas target: $target" >&2
    exit 2
    ;;
esac

need() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "required command not found: $1" >&2
    exit 1
  }
}

need curl
need sha256sum
need tar
need zstd
need strings
need python3
need nix

if [[ -z "$work_dir" ]]; then
  work_dir=$(mktemp -d)
else
  mkdir -p "$work_dir"
fi

cleanup() {
  if [[ "$keep" -eq 0 ]]; then
    rm -rf "$work_dir"
  else
    echo "kept work directory: $work_dir" >&2
  fi
}
trap cleanup EXIT

download() {
  local url=$1
  local dst=$2
  if [[ ! -f "$dst" ]]; then
    echo "downloading $url" >&2
    curl -fL --retry 3 --retry-delay 2 -o "$dst" "$url"
  fi
}

hash_path_sri() {
  nix hash path --type sha256 --sri "$1"
}

aeneas_archive="$work_dir/aeneas-$target.tar.gz"
aeneas_url="https://github.com/AeneasVerif/aeneas/releases/download/$release_tag/aeneas-$target.tar.gz"
download "$aeneas_url" "$aeneas_archive"
aeneas_sha256_hex=$(sha256sum "$aeneas_archive" | awk '{print $1}')

extract_dir="$work_dir/aeneas"
mkdir -p "$extract_dir"
tar -xzf "$aeneas_archive" -C "$extract_dir"

lean_toolchain_file="$extract_dir/backends/lean/lean-toolchain"
if [[ ! -f "$lean_toolchain_file" ]]; then
  echo "Aeneas archive did not contain backends/lean/lean-toolchain" >&2
  exit 1
fi

lean_raw=$(tr -d '\n' < "$lean_toolchain_file")
lean_version=${lean_raw#leanprover/lean4:}
lean_raw_version=${lean_version#v}

charon_bin="$extract_dir/charon"
if [[ ! -f "$charon_bin" ]]; then
  echo "Aeneas archive did not contain charon" >&2
  exit 1
fi

commit_date=$(
  strings "$charon_bin" |
    grep -o 'rustc version .* ([0-9a-f]\{9\} [0-9]\{4\}-[0-9]\{2\}-[0-9]\{2\})' |
    head -n 1 |
    grep -o '[0-9]\{4\}-[0-9]\{2\}-[0-9]\{2\}' |
    tr -d '\n'
)

if [[ -z "$commit_date" ]]; then
  echo "could not infer Rust commit date from charon binary" >&2
  exit 1
fi

rust_date=$(
  python3 - "$commit_date" <<'PY'
import datetime
import sys

print((datetime.date.fromisoformat(sys.argv[1]) + datetime.timedelta(days=1)).isoformat())
PY
)

lean_dir="$work_dir/lean-toolchain"
mkdir -p "$lean_dir"
lean_archive="$work_dir/lean-$lean_raw_version-$lean_platform.tar.zst"
lean_url="https://releases.lean-lang.org/lean4/$lean_version/lean-$lean_raw_version-$lean_platform.tar.zst"
download "$lean_url" "$lean_archive"
zstd -dc "$lean_archive" | tar -x -C "$lean_dir" --strip-components=1
lean_output_hash=$(hash_path_sri "$lean_dir")

rust_dir="$work_dir/rust-toolchain"
mkdir -p "$rust_dir"
for component in rustc rust-std rustc-dev llvm-tools miri; do
  archive="$work_dir/$component-nightly-$rust_platform.tar.gz"
  url="https://static.rust-lang.org/dist/$rust_date/$component-nightly-$rust_platform.tar.gz"
  download "$url" "$archive"
  tmp_extract="$work_dir/extract-$component"
  rm -rf "$tmp_extract"
  mkdir -p "$tmp_extract"
  tar -xzf "$archive" -C "$tmp_extract"
  top_dir=$(find "$tmp_extract" -mindepth 1 -maxdepth 1 -type d | head -n 1)
  comp_dir=$(find "$top_dir" -mindepth 1 -maxdepth 1 -type d | head -n 1)
  cp -R "$comp_dir"/. "$rust_dir"/
done

rust_src_archive="$work_dir/rust-src-nightly.tar.gz"
download "https://static.rust-lang.org/dist/$rust_date/rust-src-nightly.tar.gz" "$rust_src_archive"
tmp_extract="$work_dir/extract-rust-src"
rm -rf "$tmp_extract"
mkdir -p "$tmp_extract"
tar -xzf "$rust_src_archive" -C "$tmp_extract"
top_dir=$(find "$tmp_extract" -mindepth 1 -maxdepth 1 -type d | head -n 1)
cp -R "$top_dir/rust-src"/. "$rust_dir"/
rust_output_hash=$(hash_path_sri "$rust_dir")

mathlib_rev=$(
  grep -A2 'require mathlib from git' "$extract_dir/backends/lean/lakefile.lean" |
    grep -o '@ "[^"]*"' |
    sed -E 's/@ "([^"]*)"/\1/' |
    head -n 1
)

cat <<EOF
releaseTag = "$release_tag"
aeneas_target = "$target"
aeneas_sha256 = "$aeneas_sha256_hex"

lean_toolchain = "$lean_raw"
leanVersion = "$lean_version"
lean_sha256 = "$lean_output_hash"

rustDate = "$rust_date"
rust_toolchain = "nightly-$rust_date"
rust_sha256 = "$rust_output_hash"

mathlib_requested_rev = "$mathlib_rev"

Next hashes to refresh in flake.nix:
- packages.aeneas-download-$target.sha256: $aeneas_sha256_hex
- packages.lean-toolchain.leanVersion: $lean_version
- packages.lean-toolchain.sha256: $lean_output_hash
- packages.rust-toolchain.rustDate: $rust_date
- packages.rust-toolchain.sha256: $rust_output_hash
- packages.mathlib-cache-download.outputHash: recompute after updating the above;
  it is the recursive hash of Lake's downloaded cache plus package checkouts.
EOF
