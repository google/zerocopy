#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

TMP_DIR="$(mktemp -d)"
mkdir -p "$TMP_DIR/bin"

cat << 'EOF' > "$TMP_DIR/bin/hello"
#!/usr/bin/env bash
echo "Hello, world!"
EOF

chmod +x "$TMP_DIR/bin/hello"

tar --zstd -cf "$SCRIPT_DIR/toolchain.tar.zst" -C "$TMP_DIR" .

rm -rf "$TMP_DIR"
