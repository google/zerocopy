#!/usr/bin/env bash
set -euo pipefail

WORKDIR="$(mktemp -d)"
trap 'rm -rf "$WORKDIR"' EXIT

mkdir -p "$WORKDIR/repo/crates/core" "$WORKDIR/repo/crates/leaf"
echo "pub fn core() {}" > "$WORKDIR/repo/crates/core/lib.rs"
echo "pub fn leaf() {}" > "$WORKDIR/repo/crates/leaf/lib.rs"
echo "SECRET_UNDECLARED_DOC" > "$WORKDIR/repo/README.md"

echo "=== Bubblewrap version ==="
bwrap --version

echo ""
echo "=== Running check confined to ONLY crates/core (--tmpfs /work + --ro-bind) ==="
bwrap \
  --unshare-all \
  --die-with-parent \
  --ro-bind /usr /usr \
  --ro-bind /bin /bin \
  --ro-bind /lib /lib \
  --ro-bind /lib64 /lib64 \
  --tmpfs /work \
  --ro-bind "$WORKDIR/repo/crates/core" /work/crates/core \
  --chdir /work \
  /bin/sh -c '
    echo "[1] Read declared file /work/crates/core/lib.rs:"
    cat /work/crates/core/lib.rs

    echo "[2] Attempt to read undeclared /work/README.md:"
    if cat /work/README.md 2>&1; then
      echo "ERROR: should not be readable"
    else
      echo "BLOCKED (exit=$?)"
    fi

    echo "[3] Attempt to read undeclared /work/crates/leaf/lib.rs:"
    if cat /work/crates/leaf/lib.rs 2>&1; then
      echo "ERROR: should not be readable"
    else
      echo "BLOCKED (exit=$?)"
    fi

    echo "[4] Attempt to mutate read-only /work/crates/core/lib.rs:"
    if sh -c "echo mutated >> /work/crates/core/lib.rs" 2>&1; then
      echo "ERROR: should not be writable"
    else
      echo "BLOCKED (exit=$?)"
    fi
  '
