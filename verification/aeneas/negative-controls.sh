#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Run after run.sh. Mutate generated scratch files, never checked-in sources.
# Feature-specific controls activate when their native Lean modules are present.
set -euo pipefail
cd "$(dirname "$0")/../.."
repo=$PWD
tools_dir=${AENEAS_TOOLCHAIN_DIR:-"$repo/target/aeneas/toolchain"}
export PATH="$tools_dir/lean/bin:$PATH"
check_workspace() (
cd "$repo/target/aeneas/$1"
echo "Testing failure controls in $1"
backup=$(mktemp -d)
python3 - "$backup" <<'PYBACKUP'
from pathlib import Path
import shutil, sys
root = Path(sys.argv[1])
files = [Path("Required.lean"), Path("SpecPrelude.lean"), Path("Obligations.lean"),
         Path("Zerocopy/Funs.lean"), *Path(".").glob("Proofs*.lean"),
         *Path("Proofs").rglob("*.lean")]
if Path("SupportTests.lean").exists():
    files.append(Path("SupportTests.lean"))
for source in files:
    destination = root / source
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, destination)
PYBACKUP
restore_files() {
    python3 - "$backup" <<'PYRESTORE'
from pathlib import Path
import shutil, sys
for source in Path(sys.argv[1]).rglob("*.lean"):
    shutil.copyfile(source, source.relative_to(sys.argv[1]))
PYRESTORE
}
cleanup() {
    restore_files
    rm -f NegativeControl.lean
    rm -rf "$backup"
}
trap cleanup EXIT

expect_failure() {
    local description=$1 log=$2
    shift 2
    if "$@" > "$backup/$log" 2>&1; then
        echo "Negative control accepted $description" >&2; exit 1
    fi
    if ! grep -q 'error:' "$backup/$log"; then
        cat "$backup/$log" >&2; exit 1
    fi
    echo "Confirmed: rejected $description"
}
build_required() {
    lake build Required
}
audit() {
    lake env lean -DwarningAsError=true Check.lean
}
restore_build() {
    restore_files
    lake build Required > "$backup/restore-build.log" 2>&1 || {
        cat "$backup/restore-build.log" >&2; exit 1;
    }
}

# Establish a valid baseline so a missing artifact cannot satisfy a control.
lake build > "$backup/baseline-build.log" 2>&1 || {
    cat "$backup/baseline-build.log" >&2; exit 1;
}
audit > "$backup/baseline-audit.log" 2>&1 || {
    cat "$backup/baseline-audit.log" >&2; exit 1;
}

if [[ $1 == verification ]]; then
    echo '-- Harmless generated-comment difference' >> Zerocopy/Funs.lean
    python3 "$repo/verification/aeneas/golden.py" compare \
        "$PWD/Zerocopy" "$repo/verification/aeneas/golden"
    lake build Required > "$backup/comment-build.log" 2>&1 || {
        cat "$backup/comment-build.log" >&2; exit 1;
    }
    audit
    echo "Confirmed: comment drift passes comparison and live proofs"
    restore_build
fi

# Ordinary theorems must establish the proposition expanded by the spec command.
# These run even before the optional standalone contract syntax is introduced.
reject_spec() {
    local description=$1
    cat > NegativeControl.lean <<'LEAN'
import SpecsSyntax
open Aeneas Aeneas.Std
LEAN
    cat >> NegativeControl.lean
    expect_failure "$description" spec-build.log lake env lean -DwarningAsError=true NegativeControl.lean
    if ! grep -q 'unsolved goals' "$backup/spec-build.log" ||
        ! grep -q '⊢ False' "$backup/spec-build.log"; then
        cat "$backup/spec-build.log" >&2; exit 1
    fi
    rm NegativeControl.lean
}
reject_spec "panic under a total spec" <<'LEAN'
namespace NegativeControl
spec panic
  for (Result.fail Error.panic : Result Nat)
  ensures _ => True
theorem attempted : panic := by simp [panic]
end NegativeControl
LEAN
reject_spec "divergence under a total spec" <<'LEAN'
namespace NegativeControl
spec diverging
  for (Result.div : Result Nat)
  ensures _ => True
theorem attempted : diverging := by simp [diverging]
end NegativeControl
LEAN
reject_spec "panic under a partial spec" <<'LEAN'
namespace NegativeControl
partial spec panic
  for (Result.fail Error.panic : Result Nat)
  ensures _ => True
theorem attempted : panic := by simp [panic]
end NegativeControl
LEAN
reject_spec "an incorrect successful return under a partial spec" <<'LEAN'
namespace NegativeControl
partial spec wrong_return
  for Result.ok (0 : Nat)
  ensures out => out = 1
theorem attempted : wrong_return := by simp [wrong_return]
end NegativeControl
LEAN
reject_spec "divergence under a total mathematical-view spec" <<'LEAN'
namespace NegativeControl
spec diverging
  for (Result.div : Result Nat)
  refines id to 0
theorem attempted : diverging := by simp [diverging]
end NegativeControl
LEAN
reject_spec "an incorrect mathematical view" <<'LEAN'
namespace NegativeControl
spec wrong_view
  for Result.ok (0 : Nat)
  refines Nat.succ to 0
  ensures out => out = 0
theorem attempted : wrong_view := by simp [wrong_view]
end NegativeControl
LEAN

if [[ -f Contracts.lean ]]; then
    cat > NegativeControl.lean <<'LEAN'
import Contracts
open Aeneas Aeneas.Std
namespace NegativeControl
contract panic
  for (Result.fail Error.panic : Result Nat)
  ensures _ => True
  proof:
    simp
end NegativeControl
LEAN
    expect_failure "panic under the standalone total contract syntax" contract-build.log lake env lean -DwarningAsError=true NegativeControl.lean
    if ! grep -q '⊢ False' "$backup/contract-build.log"; then
        cat "$backup/contract-build.log" >&2; exit 1
    fi
    rm NegativeControl.lean
fi

if [[ -f SupportTests.lean ]] && grep -q 'def counterBody' SupportTests.lean; then
    reject_loop() {
        local description=$1
        python3 - "$2" "$3" <<'PYCONTROL'
from pathlib import Path
import sys
p = Path("SupportTests.lean")
s = p.read_text()
old, new = sys.argv[1:]
if s.count(old) != 1:
    raise SystemExit("Indexed-loop negative control no longer matches")
p.write_text(s.replace(old, new))
PYCONTROL
        expect_failure "$description" loop-build.log lake build SupportTests
        cp "$backup/SupportTests.lean" SupportTests.lean
    }
    reject_loop "a stationary loop index" 's.2 + 1#usize' 's.2 + 0#usize'
    reject_loop "an incorrect loop prefix step" 's.1 + 1, j' 's.1 + 2, j'
    reject_loop "continuing a loop past its end" 'if s.2 < n then' 'if s.2 ≤ n then'
    lake build SupportTests > "$backup/loop-restore-build.log" 2>&1 || {
        cat "$backup/loop-restore-build.log" >&2; exit 1;
    }
fi

# Registered proofs are theorems of their corresponding Specs proposition.
min_module=$(python3 - <<'PYCONTROL'
from pathlib import Path
import re
paths = [Path("Proofs.lean"), *Path("Proofs").rglob("*.lean")]
old = 'theorem min_spec : Zerocopy.Specs.min_spec := by'
matched = [p for p in paths if old in p.read_text()]
if len(matched) != 1:
    raise SystemExit("Specification type control no longer matches")
p = matched[0]
s = p.read_text()
start = s.index(old)
body = start + len(old)
# Native proof declarations start in column zero. Stop before the next
# declaration or registration, preserving padding/round-down in early stages.
boundary = re.search(r'(?m)^(?:(?:(?:private|noncomputable) +)?'
                     r'(?:theorem|def|abbrev)|attribute|register_spec_step|end)\b|^@\[',
                     s[body:])
if boundary is None:
    raise SystemExit("Cannot isolate the min theorem declaration")
end = body + boundary.start()
p.write_text(s[:start] + 'theorem min_spec : True := by trivial\n\n' + s[end:])
module = str(p.with_suffix('')).replace('/', '.')
Path('NegativeControl.lean').write_text('import ' + module + '\nimport Specs\n' +
    'example : Zerocopy.Specs.min_spec := @Zerocopy.Proofs.min_spec\n')
print(module)
PYCONTROL
)
# Compile just its owning module: callers of min may otherwise fail before
# the independent type check is reached. This is the same example as Required.
lake build "+$min_module" > "$backup/min-module-build.log" 2>&1 || {
    cat "$backup/min-module-build.log" >&2; exit 1;
}
expect_failure "an unrelated registered theorem in place of the inline min spec" wrong-type-build.log lake env lean NegativeControl.lean
if ! grep -qi 'type mismatch' "$backup/wrong-type-build.log" ||
    ! grep -q 'min_spec' "$backup/wrong-type-build.log"; then
    cat "$backup/wrong-type-build.log" >&2; exit 1
fi
rm NegativeControl.lean
restore_build

python3 - <<'PYCONTROL'
from pathlib import Path
paths = [Path("Proofs.lean"), *Path("Proofs").rglob("*.lean")]
old = 'theorem min_spec : Zerocopy.Specs.min_spec := by'
matched = [p for p in paths if old in p.read_text()]
if len(matched) != 1:
    raise SystemExit("Proof declaration-kind control no longer matches")
p = matched[0]
p.write_text(p.read_text().replace(old, 'def min_spec : Zerocopy.Specs.min_spec := by'))
PYCONTROL
lake build Required > "$backup/definition-build.log" 2>&1 || {
    cat "$backup/definition-build.log" >&2; exit 1;
}
expect_failure "a definition in place of a registered theorem" definition-audit.log audit
if ! grep -q 'Missing required theorem.*min_spec' "$backup/definition-audit.log"; then
    cat "$backup/definition-audit.log" >&2; exit 1
fi
restore_build

# A caller must actually use the available callee theorem during elaboration.
# The diagnostic graph is derived from Lean terms; it has no manual edge list.
if grep -q 'step with padding_lt_alignment' Proofs.lean; then
    audit > "$backup/dependency-baseline-audit.log" 2>&1 || {
        cat "$backup/dependency-baseline-audit.log" >&2; exit 1;
    }
    python3 - "$backup/padding-callers.json" <<'PYCONTROL'
from pathlib import Path
import json, sys
# This is an oracle for the fixed handwritten Proofs.lean fixture, not a
# general Lean parser. Only canonical, column-zero specification theorem
# headers own indented controlled invocations. Unknown syntax fails closed.
import re
source = Path("Proofs.lean").read_text()
marker = 'step with padding_lt_alignment'
header = re.compile(r'^theorem ([A-Za-z_][A-Za-z0-9_]*) : '
                    r'Zerocopy\.Specs\.([A-Za-z_][A-Za-z0-9_]*) := by$')
owner = None
scope = False
callers = set()
seen = set()
for line in source.splitlines():
    if line == 'namespace Zerocopy.Proofs':
        if scope:
            raise SystemExit("Nested canonical proof namespace in dependency fixture")
        scope = True
        owner = None
    elif line.startswith(('namespace ', 'end ')):
        scope = False
        owner = None
    elif line and not line[0].isspace() and not line.startswith('--'):
        owner = None
        match = header.fullmatch(line)
        if match and scope:
            name, spec = match.groups()
            if name != spec or name in seen:
                raise SystemExit("Noncanonical or duplicate theorem in dependency fixture")
            seen.add(name)
            owner = 'Zerocopy.Proofs.' + name
    if marker in line:
        if (owner is None or not scope or line.count(marker) != 1 or
                re.match(r'^[ \t]+step with padding_lt_alignment(?:[ \t]|$)', line) is None):
            raise SystemExit("Unowned or malformed padding invocation in dependency fixture")
        callers.add(owner)
if not callers:
    raise SystemExit("Padding dependency control has no source callers")
callers = sorted(callers)
edges = json.loads(Path("proof-dependencies.json").read_text())
actual = sorted(entry["theorem"] for entry in edges
                if "Zerocopy.Proofs.padding_lt_alignment" in entry["depends_on"])
if actual != callers:
    raise SystemExit("Dependency graph does not match independently known source callers")
Path(sys.argv[1]).write_text(json.dumps(callers))
PYCONTROL
    python3 - <<'PYCONTROL'
from pathlib import Path
paths = [Path("Proofs.lean"), *Path("Proofs").rglob("*.lean")]
old = 'theorem padding_lt_alignment :'
matched = [p for p in paths if old in p.read_text()]
if len(matched) != 1:
    raise SystemExit("Callee theorem control no longer matches")
p = matched[0]
p.write_text(p.read_text().replace(old, 'theorem unavailable_padding_lt_alignment :'))
PYCONTROL
    expect_failure "an unavailable callee theorem" callee-build.log lake build Proofs
    if ! grep -q 'Unknown identifier.*padding_lt_alignment' "$backup/callee-build.log"; then
        cat "$backup/callee-build.log" >&2; exit 1
    fi
    restore_build
    python3 - <<'PYCONTROL'
from pathlib import Path
p = Path("Proofs.lean")
s = p.read_text()
alias = """namespace DependencyControl
open Zerocopy Zerocopy.Proofs
private def padding_alias := Zerocopy.Proofs.padding_lt_alignment
theorem padding_proxy : Zerocopy.Specs.padding_lt_alignment := by exact padding_alias
end DependencyControl

"""
obligations = Path("Obligations.lean")
source = obligations.read_text()
imports_end = source.index('@[expose] public section')
source = source[:imports_end] + 'public import Proofs.Util\n' + source[imports_end:]
obligations.write_text(source + '\n' + alias)
imports_end = s.index('@[expose] public section')
s = s[:imports_end] + 'public import Obligations\n' + s[imports_end:]
s = s.replace('step with padding_lt_alignment', 'step with DependencyControl.padding_proxy')
p.write_text(s)
PYCONTROL
    lake build Required > "$backup/helper-build.log" 2>&1 || {
        cat "$backup/helper-build.log" >&2; exit 1;
    }
    audit > "$backup/helper-audit.log" 2>&1 || {
        cat "$backup/helper-audit.log" >&2; exit 1;
    }
    python3 - "$backup/padding-callers.json" <<'PYCONTROL'
from pathlib import Path
import json, sys
edges = json.loads(Path("proof-dependencies.json").read_text())
expected = json.loads(Path(sys.argv[1]).read_text())
actual = sorted(entry["theorem"] for entry in edges
                if "Zerocopy.Proofs.padding_lt_alignment" in entry["depends_on"])
if actual != expected:
    raise SystemExit("Dependency graph missed the callee reached through an auxiliary private helper")
PYCONTROL
    echo "Confirmed: dependency reporting follows a private helper in an auxiliary native module"
    python3 - <<'PYCONTROL'
from pathlib import Path
import re
source = Path("Proofs/Util.lean").read_text()
header = 'theorem padding_lt_alignment : Zerocopy.Specs.padding_lt_alignment := by'
start = source.index(header) + len(header)
boundary = re.search(r'(?m)^(?:(?:(?:private|noncomputable) +)?'
                     r'(?:theorem|def|abbrev)|attribute|register_spec_step|end)\b|^@\[', source[start:])
if boundary is None:
    raise SystemExit("Cannot isolate the independent padding proof")
body = source[start:start + boundary.start()]
path = Path("Obligations.lean")
old = 'private def padding_alias := Zerocopy.Proofs.padding_lt_alignment'
if path.read_text().count(old) != 1:
    raise SystemExit("Auxiliary proof alias control no longer matches")
path.write_text(path.read_text().replace(old,
    'private theorem padding_alias : Zerocopy.Specs.padding_lt_alignment := by' + body))
PYCONTROL
    lake build Required > "$backup/independent-helper-build.log" 2>&1 || {
        cat "$backup/independent-helper-build.log" >&2; exit 1;
    }
    audit > "$backup/independent-helper-audit.log" 2>&1 || {
        cat "$backup/independent-helper-audit.log" >&2; exit 1;
    }
    python3 - "$backup/padding-callers.json" <<'PYCONTROL'
from pathlib import Path
import json, sys
edges = json.loads(Path("proof-dependencies.json").read_text())
expected = set(json.loads(Path(sys.argv[1]).read_text()))
present = {entry["theorem"] for entry in edges}
actual = {entry["theorem"] for entry in edges
          if "Zerocopy.Proofs.padding_lt_alignment" in entry["depends_on"]}
if not expected <= present or actual:
    raise SystemExit("Dependency graph reported a callee replaced by an independent auxiliary proof")
PYCONTROL
    echo "Confirmed: dependency reporting omits a callee replaced by an independent auxiliary proof"
    restore_build
fi

# Data-only Rust layout inputs are the only additional admitted axioms. Even an
# unused private helper in another configured proof module must be audited.
helper=Proofs.lean
if [[ -f Proofs/Util.lean ]]; then helper=Proofs/Util.lean; fi
cat >> "$helper" <<'LEAN'
namespace UnrelatedControl
set_option warningAsError false in
private theorem unused_helper : True := by sorry
end UnrelatedControl
LEAN
lake build Required > "$backup/private-helper-build.log" 2>&1 || {
    cat "$backup/private-helper-build.log" >&2; exit 1;
}
expect_failure "an admitted unused private proof helper" private-helper-audit.log audit
if ! grep -q 'unused_helper.*unapproved axiom.*sorryAx' "$backup/private-helper-audit.log"; then
    cat "$backup/private-helper-audit.log" >&2; exit 1
fi
restore_build

# The native-module roster covers auxiliary files too, even when neither their
# declarations nor their namespace occur in a registered proof.
cat >> SpecPrelude.lean <<'LEAN'
namespace UnrelatedControl
axiom unused_auxiliary_fact : True
end UnrelatedControl
LEAN
lake build Required > "$backup/auxiliary-axiom-build.log" 2>&1 || {
    cat "$backup/auxiliary-axiom-build.log" >&2; exit 1;
}
expect_failure "an unused unapproved axiom in a native auxiliary module" auxiliary-axiom-audit.log audit
if ! grep -q 'unapproved axiom.*UnrelatedControl.unused_auxiliary_fact' "$backup/auxiliary-axiom-audit.log"; then
    cat "$backup/auxiliary-axiom-audit.log" >&2; exit 1
fi
restore_build

cat >> Proofs.lean <<'LEAN'
namespace UnrelatedControl
axiom unused_fact : True
end UnrelatedControl
LEAN
lake build Required > "$backup/unused-axiom-build.log" 2>&1 || {
    cat "$backup/unused-axiom-build.log" >&2; exit 1;
}
expect_failure "an unused unapproved axiom outside the proof namespace" unused-axiom-audit.log audit
if ! grep -q 'unapproved axiom.*UnrelatedControl.unused_fact' "$backup/unused-axiom-audit.log"; then
    cat "$backup/unused-axiom-audit.log" >&2; exit 1
fi
restore_build

cat >> Proofs.lean <<'LEAN'
namespace UnrelatedControl
set_option warningAsError false in
theorem admitted : True := by sorry
end UnrelatedControl
LEAN
lake build Required > "$backup/sorry-build.log" 2>&1 || {
    cat "$backup/sorry-build.log" >&2; exit 1;
}
expect_failure "an admitted proof" sorry-audit.log audit
if ! grep -q 'unapproved axiom.*sorryAx' "$backup/sorry-audit.log"; then
    cat "$backup/sorry-audit.log" >&2; exit 1
fi
restore_build

# Generated conversion witnesses receive the same admission audit.
python3 - <<'PYCONTROL'
from pathlib import Path
p = Path("Required.lean")
s = p.read_text()
old = 'using @Zerocopy.Proofs.min_spec'
if s.count(old) != 1:
    raise SystemExit("Required witness admission control no longer matches")
s = s.replace('check_contract Zerocopy.Obligations.min_spec ' + old,
    'set_option warningAsError false in\n' +
    'check_contract Zerocopy.Obligations.min_spec using (by sorry : Zerocopy.Obligations.min_spec)')
p.write_text(s)
PYCONTROL
lake build Required > "$backup/required-sorry-build.log" 2>&1 || {
    cat "$backup/required-sorry-build.log" >&2; exit 1;
}
expect_failure "an admitted required-contract witness" required-sorry-audit.log audit
if ! grep -q 'unapproved axiom.*sorryAx' "$backup/required-sorry-audit.log"; then
    cat "$backup/required-sorry-audit.log" >&2; exit 1
fi
restore_build

cat > NegativeControl.lean <<'LEAN'
import Proofs
import Obligations
import RequiredContracts
namespace UnrelatedControl
theorem min_spec : True := by trivial
end UnrelatedControl
check_contract Zerocopy.Obligations.min_spec using UnrelatedControl.min_spec
LEAN
expect_failure "an unrelated True theorem as an independent required contract" unrelated-build.log lake env lean NegativeControl.lean
rm NegativeControl.lean

# Once arithmetic postconditions are strengthened, a valid earlier weak
# round-down contract must fail the independently written required proposition.
if [[ -f Arithmetic.lean ]] && grep -q 'round_down_properties' Proofs/Util.lean; then
    cat > NegativeControl.lean <<'LEAN'
import Proofs
import Obligations
import RequiredContracts
open Aeneas Aeneas.Std Zerocopy Zerocopy.Proofs
namespace WeakerControl
theorem round_down_spec (n : Usize) (align : NonZeroUsize)
    (h : (align.val : Nat).isPowerOfTwo) :
    util.round_down_to_next_multiple_of_alignment n align
      ⦃ m => m ≤ n ∧ m.val % align.val.val = 0 ⦄ := by
  apply WP.spec_mono (Zerocopy.Proofs.round_down_spec n align h)
  intro m hm
  exact ⟨hm.1, hm.2.2.1⟩
end WeakerControl
LEAN
    lake env lean -DwarningAsError=true NegativeControl.lean > "$backup/weaker-build.log" 2>&1 || {
        cat "$backup/weaker-build.log" >&2; exit 1;
    }
    cat >> NegativeControl.lean <<'LEAN'
check_contract Zerocopy.Obligations.round_down_spec using WeakerControl.round_down_spec
LEAN
    expect_failure "a valid weaker round-down contract as the independent required contract" weaker-required.log lake env lean NegativeControl.lean
    rm NegativeControl.lean
fi

reject_model() {
    local description=$1 old=$2 new=$3 target=${4:-}
    python3 - "$old" "$new" "$target" <<'PYCONTROL'
from pathlib import Path
import sys
p = Path("Zerocopy/Funs.lean")
s = p.read_text()
old, new, target = sys.argv[1:]
start, end = 0, len(s)
if target:
    start = s.index('def ' + target)
    end = s.find('/-- ', start)
    if end < 0:
        end = len(s)
part = s[start:end]
if part.count(old) != 1:
    raise SystemExit("Model negative control no longer matches")
p.write_text(s[:start] + part.replace(old, new) + s[end:])
PYCONTROL
    expect_failure "$description" model-build.log build_required
    cp "$backup/Zerocopy/Funs.lean" Zerocopy/Funs.lean
}
if [[ -f Arithmetic.lean ]] && grep -q 'padding_properties' Proofs/Util.lean; then
    reject_model "always-zero padding under the exact arithmetic spec" 'ok (i2 &&& mask)' 'ok 0#usize'
fi
if [[ -f Arithmetic.lean ]] && grep -q 'round_down_properties' Proofs/Util.lean; then
    reject_model "always-zero round-down under the exact arithmetic spec" 'ok (n &&& mask)' 'ok 0#usize'
fi
if [[ -f LayoutMath.lean ]]; then
    if grep -q 'def layout.DstLayout.pad_to_align' Zerocopy/Funs.lean &&
        grep -q 'statically_shallow_unpadded := (padding = 0#usize)' Zerocopy/Funs.lean; then
        reject_model "an incorrect shallow-padding flag" \
            'statically_shallow_unpadded := (padding = 0#usize)' \
            'statically_shallow_unpadded := true' 'layout.DstLayout.pad_to_align'
    fi
    if grep -q 'Usize.checked_add offset tsl.offset' Zerocopy/Funs.lean &&
        grep -q 'theorem extend_spec :' Proofs.lean; then
        reject_model "conflating physical offset with the size base" \
            'Usize.checked_add offset tsl.offset' \
            'Usize.checked_add offset tsl.size_base' 'layout.DstLayout.extend'
    fi
    if grep -q 'def layout.DstLayout.pad_to_align' Zerocopy/Funs.lean &&
        grep -q 'util.padding_needed_for trailing.size_base size_align' Zerocopy/Funs.lean; then
        reject_model "dropping inner rounding under outer packing" \
            'util.padding_needed_for trailing.size_base size_align' \
            'util.padding_needed_for trailing.size_base self.align' 'layout.DstLayout.pad_to_align'
    fi
fi

python3 - <<'PYCONTROL'
from pathlib import Path
p = Path("Zerocopy/Funs.lean")
s = p.read_text()
if s.count("if i > i1") != 1:
    raise SystemExit("Min negative control no longer matches generated output")
p.write_text(s.replace("if i > i1", "if i < i1"))
PYCONTROL
if [[ $1 == verification ]]; then
    if python3 "$repo/verification/aeneas/golden.py" compare \
        "$PWD/Zerocopy" "$repo/verification/aeneas/golden" \
        > "$backup/mutated-compare.log" 2>&1; then
        echo "Fuzzy comparison accepted an incorrect translated min" >&2; exit 1
    fi
    if ! grep -q 'Aeneas goldens differ' "$backup/mutated-compare.log"; then
        cat "$backup/mutated-compare.log" >&2; exit 1
    fi
    echo "Confirmed: fuzzy comparison rejects an incorrect translated min"
fi
expect_failure "a min implementation with its comparison reversed" min-build.log build_required
restore_build
lake build
audit
)
check_workspace golden-verification
check_workspace verification
