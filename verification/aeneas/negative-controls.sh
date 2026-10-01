#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Run after run.sh. Mutate generated scratch files, never checked-in sources.
set -euo pipefail
cd "$(dirname "$0")/../.."
repo=$PWD
tools_dir=${AENEAS_TOOLCHAIN_DIR:-"$repo/target/aeneas/toolchain"}
export PATH="$tools_dir/lean/bin:$PATH"
check_workspace() (
cd "$repo/target/aeneas/$1"
echo "Testing failure controls in $1"
backup=$(mktemp -d)
cp Proofs.lean "$backup/Proofs.lean"
cp Zerocopy/Funs.lean "$backup/Funs.lean"
restore() {
    cp "$backup/Proofs.lean" Proofs.lean
    cp "$backup/Funs.lean" Zerocopy/Funs.lean
    rm -rf "$backup"
}
trap restore EXIT

if [[ $1 == verification ]]; then
    echo '-- Harmless generated-comment difference' >> Zerocopy/Funs.lean
    python3 "$repo/verification/aeneas/golden.py" compare \
        "$PWD/Zerocopy" "$repo/target/aeneas/rendered-golden"
    lake build > "$backup/comment-build.log" 2>&1 || {
        cat "$backup/comment-build.log" >&2; exit 1;
    }
    lake env lean -DwarningAsError=true Check.lean
    echo "Confirmed: comment drift passes comparison and live proofs"
fi

cat >> Proofs.lean <<'LEAN'
namespace Zerocopy.Proofs
theorem negative_control : True := by sorry
end Zerocopy.Proofs
LEAN
if ! lake build Required > "$backup/sorry-build.log" 2>&1; then
    cat "$backup/sorry-build.log" >&2
    exit 1
fi
if lake env lean Check.lean > "$backup/sorry-check.log" 2>&1; then
    echo "Axiom audit accepted an admitted proof" >&2
    exit 1
fi
if ! grep -q 'unapproved axiom' "$backup/sorry-check.log" ||
    ! grep -q 'sorryAx' "$backup/sorry-check.log"; then
    cat "$backup/sorry-check.log" >&2
    exit 1
fi
echo "Confirmed: the axiom audit rejects an admitted proof"
cp "$backup/Proofs.lean" Proofs.lean

python3 - <<'PY'
from pathlib import Path
import re
p = Path("Proofs.lean")
s, count = re.subn(r'theorem min_spec\b.*?(?=\ntheorem |\nend Zerocopy.Proofs)',
                  'theorem min_spec : True := by trivial\n', p.read_text(), flags=re.S)
if count != 1:
    raise SystemExit("Obligation negative control no longer matches")
p.write_text(s)
PY
if lake build Required > "$backup/obligation-build.log" 2>&1; then
    echo "Required obligation accepted an unrelated True theorem" >&2
    exit 1
fi
if ! grep -Eq '(error: Required[.]lean:|Required[.]lean:.*error)' "$backup/obligation-build.log"; then
    cat "$backup/obligation-build.log" >&2
    exit 1
fi
echo "Confirmed: required obligations reject an unrelated True theorem"
cp "$backup/Proofs.lean" Proofs.lean

python3 - <<'PY'
from pathlib import Path
p = Path("Zerocopy/Funs.lean")
s = p.read_text()
if s.count("if i > i1") != 1:
    raise SystemExit("min negative control no longer matches generated output")
p.write_text(s.replace("if i > i1", "if i < i1"))
PY
if [[ $1 == verification ]]; then
    if python3 "$repo/verification/aeneas/golden.py" compare \
        "$PWD/Zerocopy" "$repo/target/aeneas/rendered-golden" \
        > "$backup/mutated-compare.log" 2>&1; then
        echo "Fuzzy comparison accepted an incorrect translated min" >&2
        exit 1
    fi
    if ! grep -q 'Aeneas goldens differ' "$backup/mutated-compare.log"; then
        cat "$backup/mutated-compare.log" >&2
        exit 1
    fi
    echo "Confirmed: fuzzy comparison rejects an incorrect translated min"
fi
if lake build Required > "$backup/mutated-build.log" 2>&1; then
    echo "Proofs accepted a min implementation with its comparison reversed" >&2
    exit 1
fi
if ! grep -Eq '(error: Proofs[.]lean:|Proofs[.]lean:.*error)' "$backup/mutated-build.log"; then
    cat "$backup/mutated-build.log" >&2
    exit 1
fi
echo "Confirmed: the proofs reject an incorrect translated min"
cp "$backup/Funs.lean" Zerocopy/Funs.lean
lake build
lake env lean -DwarningAsError=true Check.lean
)
check_workspace golden-verification
check_workspace verification
