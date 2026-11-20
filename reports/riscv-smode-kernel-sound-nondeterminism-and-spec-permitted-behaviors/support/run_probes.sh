#!/usr/bin/env bash
# Re-check both probes with a plain Lean 4 toolchain (no Lake project, no imports beyond the prelude).
# Usage: LEAN=/path/to/lean ./run_probes.sh      (default: `lean` on PATH; observed with Lean 4.34.1)
set -euo pipefail
LEAN="${LEAN:-lean}"
cd "$(dirname "$0")"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
{ cat PerLevelStaleTranslation.lean
  printf '\n#print axioms PerLevelStale.perLevel_admits_never_valid\n#print axioms PerLevelStale.fenced_no_gap\n'; } > "$tmp/P1.lean"
{ cat LrScContextSwitch.lean
  printf '\n#print axioms LrScSwitch.lost_update_permitted\n#print axioms LrScSwitch.dummy_sc_sound\n#print axioms LrScSwitch.qemu_like_masks_bug\n'; } > "$tmp/P2.lean"
"$LEAN" --version
"$LEAN" "$tmp/P1.lean"
"$LEAN" "$tmp/P2.lean"
