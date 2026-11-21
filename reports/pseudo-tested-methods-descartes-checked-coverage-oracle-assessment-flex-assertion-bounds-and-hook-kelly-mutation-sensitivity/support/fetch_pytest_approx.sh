#!/bin/sh
# Materialise pytest's approx implementation from the pinned revision without installing pytest.
# approx.py imports only the standard library and _pytest.warning_types.
set -eu
REV=9efd0121a4396da80c20d7c3b7844825966612f6
DEST=${1:-/tmp/pytest_approx_shim}
mkdir -p "$DEST/_pytest"
: > "$DEST/_pytest/__init__.py"
for f in approx.py warning_types.py; do
  curl -sSLf "https://raw.githubusercontent.com/pytest-dev/pytest/$REV/src/_pytest/$f" -o "$DEST/_pytest/$f"
done
echo "PYTHONPATH=$DEST python3 helper_semantics.py"
