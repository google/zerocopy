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
cp Required.lean "$backup/Required.lean"
cp Zerocopy/Funs.lean "$backup/Funs.lean"
restore() {
    cp "$backup/Proofs.lean" Proofs.lean
    cp "$backup/Required.lean" Required.lean
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

# Exercise the actual command expansion, not just its underlying WP predicates.
reject_contract() {
    local description=$1
    cat >> Proofs.lean
    if lake build Required > "$backup/contract-build.log" 2>&1; then
        echo "Contract syntax accepted $description" >&2; exit 1
    fi
    if ! grep -Eq '(error: Proofs[.]lean:|Proofs[.]lean:.*error)' "$backup/contract-build.log" ||
        ! grep -q 'unsolved goals' "$backup/contract-build.log" ||
        ! grep -q '⊢ False' "$backup/contract-build.log"; then
        cat "$backup/contract-build.log" >&2; exit 1
    fi
    echo "Confirmed: contract syntax rejects $description"
    cp "$backup/Proofs.lean" Proofs.lean
}
reject_contract "panic under a total contract" <<'LEAN'
namespace Zerocopy.Proofs
contract panic_control
  for (Result.fail Error.panic : Result Nat)
  requires h : True
  ensures _ => True
  proof:
    simp
end Zerocopy.Proofs
LEAN
reject_contract "divergence under a total contract" <<'LEAN'
namespace Zerocopy.Proofs
contract divergence_control
  for (Result.div : Result Nat)
  ensures _ => True
  proof:
    simp
end Zerocopy.Proofs
LEAN
reject_contract "panic under a partial contract" <<'LEAN'
namespace Zerocopy.Proofs
partial contract partial_panic_control
  for (Result.fail Error.panic : Result Nat)
  ensures _ => True
  proof:
    simp
end Zerocopy.Proofs
LEAN
reject_contract "an incorrect successful return under a partial contract" <<'LEAN'
namespace Zerocopy.Proofs
partial contract partial_return_control
  for Result.ok (0 : Nat)
  ensures ret => ret = 1
  proof:
    simp
end Zerocopy.Proofs
LEAN

# The caller must actually have its callee theorem available during elaboration.
python3 - <<'PY'
from pathlib import Path
p = Path("Proofs.lean")
s = p.read_text()
old = 'contract padding_lt_alignment '
if s.count(old) != 1:
    raise SystemExit("Callee theorem negative control no longer matches")
p.write_text(s.replace(old, 'contract unavailable_padding_lt_alignment '))
PY
if lake build Proofs > "$backup/dependency-build.log" 2>&1; then
    echo "Caller proof accepted an unavailable callee theorem" >&2
    exit 1
fi
if ! grep -q 'Unknown identifier.*padding_lt_alignment' "$backup/dependency-build.log"; then
    cat "$backup/dependency-build.log" >&2; exit 1
fi
echo "Confirmed: caller proof rejects an unavailable callee theorem"
cp "$backup/Proofs.lean" Proofs.lean

# A private alias outside the proof namespace must not hide a callee reference.
python3 - <<'PY'
from pathlib import Path
p = Path("Proofs.lean")
s = p.read_text()
alias = '''end Zerocopy.Proofs
namespace DependencyControl
private def padding_alias := Zerocopy.Proofs.padding_lt_alignment
end DependencyControl
namespace Zerocopy.Proofs

'''
call = 'step with padding_lt_alignment size self.align hpow'
if s.count('contract pad_to_align_spec ') != 1 or s.count(call) != 1:
    raise SystemExit("Private helper dependency control no longer matches")
s = s.replace('contract pad_to_align_spec ', alias + 'contract pad_to_align_spec ')
p.write_text(s.replace(call, 'step with DependencyControl.padding_alias size self.align hpow'))
PY
lake build Required > "$backup/helper-build.log" 2>&1 || {
    cat "$backup/helper-build.log" >&2; exit 1;
}
lake env lean -DwarningAsError=true Check.lean > "$backup/helper-check.log" 2>&1 || {
    cat "$backup/helper-check.log" >&2; exit 1;
}
echo "Confirmed: dependency audit follows a private helper outside the proof namespace"

# Terms remain valid when an edge is omitted; the dependency audit must catch it.
python3 - <<'PY'
from pathlib import Path
p = Path("Required.lean")
s = p.read_text()
old = '(`Zerocopy.Proofs.pad_to_align_spec, #[`Zerocopy.Proofs.padding_lt_alignment])'
if s.count(old) != 1:
    raise SystemExit("Undeclared dependency negative control no longer matches")
p.write_text(s.replace(old, '(`Zerocopy.Proofs.pad_to_align_spec, #[])'))
PY
lake build Required > "$backup/undeclared-build.log" 2>&1 || {
    cat "$backup/undeclared-build.log" >&2; exit 1;
}
if lake env lean Check.lean > "$backup/undeclared-check.log" 2>&1; then
    echo "Dependency audit accepted an undeclared proof reference" >&2; exit 1
fi
if ! grep -q 'undeclared proof dependency.*padding_lt_alignment' "$backup/undeclared-check.log"; then
    cat "$backup/undeclared-check.log" >&2; exit 1
fi
echo "Confirmed: dependency audit rejects an undeclared proof reference"
cp "$backup/Required.lean" Required.lean
cp "$backup/Proofs.lean" Proofs.lean

python3 - <<'PY'
from pathlib import Path
p = Path("Required.lean")
s = p.read_text()
old = '(`Zerocopy.Proofs.max_spec, #[])'
if s.count(old) != 1:
    raise SystemExit("Unused dependency negative control no longer matches")
p.write_text(s.replace(old, '(`Zerocopy.Proofs.max_spec, #[`Zerocopy.Proofs.min_spec])'))
PY
lake build Required > "$backup/unused-build.log" 2>&1 || {
    cat "$backup/unused-build.log" >&2; exit 1;
}
if lake env lean Check.lean > "$backup/unused-check.log" 2>&1; then
    echo "Dependency audit accepted an unused proof dependency" >&2; exit 1
fi
if ! grep -q 'unused proof dependency.*min_spec' "$backup/unused-check.log"; then
    cat "$backup/unused-check.log" >&2; exit 1
fi
echo "Confirmed: dependency audit rejects an unused proof dependency"
cp "$backup/Required.lean" Required.lean

python3 - <<'PY'
from pathlib import Path
p = Path("Zerocopy/Funs.lean")
s = p.read_text()
old = 'ok (i2 &&& mask)'
if s.count(old) != 1:
    raise SystemExit("Callee model negative control no longer matches")
p.write_text(s.replace(old, 'ok i'))
PY
if lake build Required > "$backup/callee-model-build.log" 2>&1; then
    echo "Proof chain accepted an incorrect translated padding callee" >&2; exit 1
fi
if ! grep -Eq '(error: Proofs[.]lean:|Proofs[.]lean:.*error)' "$backup/callee-model-build.log"; then
    cat "$backup/callee-model-build.log" >&2; exit 1
fi
echo "Confirmed: proof chain rejects an incorrect translated padding callee"
cp "$backup/Funs.lean" Zerocopy/Funs.lean

# These mutations satisfy earlier weak bounds but violate the exact contracts.
reject_model() {
    local description=$1
    python3 - "$2" "$3" <<'PYCONTROL'
from pathlib import Path
import sys
p = Path("Zerocopy/Funs.lean")
s = p.read_text()
old, new = sys.argv[1:]
if s.count(old) != 1:
    raise SystemExit("Strong model negative control no longer matches")
p.write_text(s.replace(old, new))
PYCONTROL
    if lake build Required > "$backup/strong-model-build.log" 2>&1; then
        echo "Proofs accepted $description" >&2; exit 1
    fi
    if ! grep -Eq '(error: Proofs[.]lean:|Proofs[.]lean:.*error)' "$backup/strong-model-build.log"; then
        cat "$backup/strong-model-build.log" >&2; exit 1
    fi
    echo "Confirmed: exact contracts reject $description"
    cp "$backup/Funs.lean" Zerocopy/Funs.lean
}
reject_model "always-zero padding" 'ok (i2 &&& mask)' 'ok 0#usize'
reject_model "always-zero round-down" 'ok (n &&& mask)' 'ok 0#usize'
reject_model "an incorrect shallow-padding flag" \
    'statically_shallow_unpadded := (static_padding = 0#usize)' \
    'statically_shallow_unpadded := true'
reject_model "a changed DST layout" \
    'layout.SizeInfo.SliceDst _ => ok (0#usize, self.size_info)' \
    'layout.SizeInfo.SliceDst _ => ok (0#usize, layout.SizeInfo.Sized 0#usize)'

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
s, count = re.subn(r'contract min_spec\b.*?(?=\n(?:theorem|contract|partial contract) |\nend Zerocopy.Proofs)',
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

# The earlier round-down contract is true, but too weak for current obligations.
cat > "$backup/weaker-round.lean" <<'LEAN'
contract round_down_spec (n : Usize) (align : NonZeroUsize)
  for util.round_down_to_next_multiple_of_alignment n align
  requires h : (align.val : Nat).isPowerOfTwo
  ensures m => m ≤ n ∧ m.val % align.val.val = 0
  proof:
    have hpos := Nat.pos_of_isPowerOfTwo h
    unfold util.round_down_to_next_multiple_of_alignment
    simp only [core.num.nonzero.NonZero.get, bind_ok]
    step
    step
    step with UScalar.sub_bv_spec as ⟨mask, hval, hle, hbv⟩
    simp only [lift, bind_ok, WP.spec_ok]
    have hexact := Arithmetic.round_down_exact n align.val mask h hval
    obtain ⟨hbound, haligned, _, _⟩ :=
      Arithmetic.round_down_properties _ _ _ hpos hexact
    exact ⟨(UScalar.le_equiv _ _).mpr hbound, haligned⟩
LEAN
python3 - "$backup/weaker-round.lean" <<'PYCONTROL'
from pathlib import Path
import re
import sys
p = Path("Proofs.lean")
s, count = re.subn(
    r'contract round_down_spec\b.*?(?=\n(?:theorem|contract|partial contract) |\nend Zerocopy.Proofs)',
    Path(sys.argv[1]).read_text(), p.read_text(), flags=re.S)
if count != 1:
    raise SystemExit("Weaker round-down control no longer matches")
p.write_text(s)
PYCONTROL
lake build Proofs > "$backup/weaker-proof-build.log" 2>&1 || {
    cat "$backup/weaker-proof-build.log" >&2; exit 1;
}
if lake build Required > "$backup/weaker-required-build.log" 2>&1; then
    echo "Required obligations accepted the earlier weak round-down contract" >&2; exit 1
fi
if ! grep -Eq '(error: Required[.]lean:|Required[.]lean:.*error)' "$backup/weaker-required-build.log"; then
    cat "$backup/weaker-required-build.log" >&2; exit 1
fi
echo "Confirmed: a valid weaker contract fails independent required-type checks"
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
