#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Run after run.sh. Mutate generated scratch files, never checked-in sources.
# Capabilities select control families; a missing selected fixture is an error.
set -euo pipefail
cd "$(dirname "$0")/../.."
repo=$PWD
source verification/aeneas/toolchain.sh
tools_dir=${AENEAS_TOOLCHAIN_DIR:-"$repo/target/aeneas/toolchain"}
export PATH="$tools_dir/lean/bin:$PATH"
# Golden and live projects have separate generated sources, caches, and
# backups. Each subshell restores its own project even when a control fails.
check_workspace() (
cd "$repo/target/aeneas/$1"
echo "Testing failure controls in $1"
# Every temporary source has one lifecycle: it must be absent before the
# suite starts and is removed on exit. Use the same roster for both decisions
# so cleanup cannot delete a source that belonged to an earlier editor session.
control_files=(
    NegativeControl.lean WeakOutcome.lean
    RoundingConstructorControl.lean RoundingDomainControl.lean
    Zerocopy/ScopeControl.lean Zerocopy/ShapeControl.lean Zerocopy/ModelControl.lean
    Proofs/WitnessOwnerControl.lean Proofs/PaddingDependencyControl.lean
)
for fixture in "${control_files[@]}"; do
    # A dangling symlink also belongs to somebody else; -e alone misses it.
    [[ ! -e "$fixture" && ! -L "$fixture" ]] || {
        echo "Negative control fixture already exists: $fixture" >&2; exit 1;
    }
done
backup=$(mktemp -d)
python3 - "$backup" <<'PYBACKUP'
from pathlib import Path
import shutil, sys
root = Path(sys.argv[1])
files = [Path("bindings.json"), Path("Required.lean"), Path("Specs.lean"), Path("ModelShapes.lean"), Path("Models.lean"),
         Path("SpecPrelude.lean"), Path("Obligations.lean"),
         Path("Zerocopy/Funs.lean"), Path("Zerocopy/FunsExternal.lean"),
         *Path(".").glob("Proofs*.lean"),
         *Path("Proofs").rglob("*.lean")]
for name in ("ModelSupport", "LayoutModel", "MathViews", "SupportTests", "Corollaries",
             "LayoutModelDomainTests", "OutcomeTests"):
    if Path(name + ".lean").exists():
        files.append(Path(name + ".lean"))
for source in files:
    destination = root / source
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, destination)
PYBACKUP
# Restore baseline source bytes between control stages. Lake then
# rebuilds from those sources; restoring an old .olean could conceal a mutation.
# Lake's --old mode ignores changed imports. Rewrite even unchanged local
# sources so their proofs are checked again against the restored definitions.
# Keeping their old timestamps could replay proofs from a different model.
restore_files() {
    python3 - "$backup" <<'PYRESTORE'
from pathlib import Path
import shutil, sys
root = Path(sys.argv[1])
for source in [*root.rglob("*.lean"), root / "bindings.json"]:
    shutil.copyfile(source, source.relative_to(root))
PYRESTORE
}
cleanup() {
    restore_files
    rm -f "${control_files[@]}"
    rm -rf "$backup"
}
trap cleanup EXIT

# This helper checks command failure, not its semantic cause. Each control
# must also establish its valid baseline and inspect the expected diagnostic.
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
    aeneas_lake build Required
}
audit() {
    aeneas_lake env lean -DwarningAsError=true Check.lean
}
# The positive module proves TModel authoring and concrete forward shapes first.
# Reject raw-type/dictionary shape dependencies in a separate source environment.
aeneas_lake build ModelTests > "$backup/type-only-shapes-positive.log" 2>&1 || {
    cat "$backup/type-only-shapes-positive.log" >&2; exit 1;
}
shape_fixture="$repo/verification/aeneas/tests/type-only-shapes/reject-raw-parameter.lean"
expect_failure "raw generic parameter in a type-only model shape" type-only-shapes-negative.log \
    aeneas_lake env lean --root="$(dirname "$shape_fixture")" -DwarningAsError=true "$shape_fixture"
if ! grep -Fq 'Unknown identifier `T`' "$backup/type-only-shapes-negative.log"; then
    echo "Type-only shape fixture failed outside its intended authoring boundary" >&2
    cat "$backup/type-only-shapes-negative.log" >&2; exit 1
fi
# A semantic mutation must remain a well-formed generated program. Only its
# dependent proofs should fail; a parser/type error cannot establish sensitivity.
check_model_mutant() {
    local description=$1 target=${2:-Zerocopy.Funs}
    aeneas_lake build "+$target" > "$backup/model-well-formed.log" 2>&1 || {
        echo "Malformed model negative control: $description" >&2
        cat "$backup/model-well-formed.log" >&2; exit 1;
    }
}
# Reuse the verified root mapping instead of parsing model declaration syntax
# a second time. Missing/invalid manifests are errors, never absent capabilities.
has_binding() {
    local present
    present=$(python3 - "$@" <<'PYCONTROL'
from pathlib import Path
import json, sys
manifest = json.loads(Path("bindings.json").read_text())
models = manifest["bindings"]
if (manifest.get("version") != 3 or manifest.get("mode") != "verified-live"
        or not isinstance(models, dict) or not all(
        isinstance(key, str) and isinstance(value, dict) and value.get("kind") in ("function", "type") and isinstance(value.get("raw"), str) for key, value in models.items())):
    raise SystemExit("Invalid verified model bindings for failure controls")
kind = sys.argv[1]
raw = sys.argv[2] if len(sys.argv) == 3 else None
if kind not in ("function", "type") or len(sys.argv) not in (2, 3):
    raise SystemExit("Invalid binding capability request")
print("yes" if any(entry["kind"] == kind and (raw is None or entry["raw"] == raw)
                   for entry in models.values()) else "no")
PYCONTROL
) || { echo "Cannot determine model capability" >&2; exit 1; }
    [[ $present == yes ]]
}
has_model() {
    has_binding function "Zerocopy.$1"
}
# A constrained mathematical value can still break an operation promise or its
# required raw input domain. Probe the unchanged constructor source fence in an
# isolated module so reorganizing helper proofs does not change these controls.
rounding_control="$repo/verification/aeneas/tests/rounding_model_controls.py"
rounding_capability=$(python3 "$rounding_control" capability) || exit 1
if [[ $rounding_capability == yes ]]; then
    aeneas_lake build +Models +SpecsSyntax +Zerocopy.Funs > "$backup/rounding-operation-baseline.log" 2>&1 || {
        cat "$backup/rounding-operation-baseline.log" >&2; exit 1;
    }
    python3 "$rounding_control" write-probes
    for fixture in RoundingConstructorControl RoundingDomainControl; do
        aeneas_lake env lean -DwarningAsError=true "$fixture.lean" > "$backup/$fixture-baseline.log" 2>&1 || {
            echo "Malformed or false rounding behavior baseline: $fixture" >&2
            cat "$backup/$fixture-baseline.log" >&2; exit 1;
        }
    done
    reject_rounding_decoder() {
        local mutation=$1 description=$2 target=$3
        python3 "$rounding_control" mutate "$mutation"
        # Proof fields must be correct; a malformed decoder cannot establish
        # sensitivity of its operation promise or independently fixed domain.
        check_model_mutant "$description" Models
        if [[ $mutation == constant ]]; then
            aeneas_lake env lean -DwarningAsError=true RoundingDomainControl.lean \
                > "$backup/rounding-constant-domain.log" 2>&1 || {
                echo "Constant rounding mutant did not preserve the required input" >&2
                cat "$backup/rounding-constant-domain.log" >&2; exit 1;
            }
        fi
        expect_failure "$description" "rounding-$mutation-behavior.log" \
            aeneas_lake env lean -DwarningAsError=true "$target.lean"
        python3 "$rounding_control" check-failure "$mutation" "$backup/rounding-$mutation-behavior.log"
        cp "$backup/Models.lean" Models.lean
        aeneas_lake build +Models > "$backup/rounding-$mutation-restore.log" 2>&1 || {
            cat "$backup/rounding-$mutation-restore.log" >&2; exit 1;
        }
    }
    reject_rounding_decoder constant "a valid constant rounding pair breaking new(2,1)'s output promise" RoundingConstructorControl
    reject_rounding_decoder none "an always-reject rounding decoder excluding a required positive getter input" RoundingDomainControl
fi
restore_build() {
    restore_files
    aeneas_lake build Required > "$backup/restore-build.log" 2>&1 || {
        cat "$backup/restore-build.log" >&2; exit 1;
    }
}

# Establish a valid baseline so a missing artifact cannot satisfy a control.
aeneas_lake build > "$backup/baseline-build.log" 2>&1 || {
    cat "$backup/baseline-build.log" >&2; exit 1;
}
audit > "$backup/baseline-audit.log" 2>&1 || {
    cat "$backup/baseline-audit.log" >&2; exit 1;
}

# An opaque helper must not conceal an adapter which discards forbidden
# failures. This mutation leaves NonZero::get's returned value unchanged, so
# ordinary functional proofs alone would not detect the unsupported dependency.
# Its backend-like namespace must not hide its actual downstream module owner.
python3 - <<'PYCONTROL'
from pathlib import Path
p = Path("Zerocopy/FunsExternal.lean")
s = p.read_text()
start = "@[simp] def core.num.nonzero.NonZero.get"
body = "(x : core.num.nonzero.NonZero T Inner) : Result T := .ok x.val"
if s.count(start) != 1 or s.count(body) != 1:
    raise SystemExit("Failure erasure control no longer matches")
helper = ("opaque Aeneas.Std.hiddenFailureErasure : Option Unit :=\n"
          "  Aeneas.Std.Option.ofResult (Result.fail .undef : Result Unit)\n\n")
s = s.replace(start, helper + start)
s = s.replace(body, "(x : core.num.nonzero.NonZero T Inner) : Result T :=\n"
              "  match Aeneas.Std.hiddenFailureErasure with\n"
              "  | none => .ok x.val\n"
              "  | some _ => .ok x.val")
p.write_text(s)
PYCONTROL
check_model_mutant "failure erasure hidden behind an opaque helper" Zerocopy.FunsExternal
expect_failure "failure erasure hidden behind an opaque helper" unsafe-erasure-audit.log audit
if ! grep -Fq 'unsupported failure erasure' "$backup/unsafe-erasure-audit.log"; then
    cat "$backup/unsafe-erasure-audit.log" >&2; exit 1
fi
restore_build

# Exercise the translator's call filtering with real Rust producers. The bad
# functions are compiled for inspection only; executing them would be Rust UB.
if has_model util.safety_checks.checked_bool; then
    "$repo/verification/aeneas/tests/producer-controls.sh" "$PWD"
fi

# Each storage interpretation must reject its bad inputs even when safe callers
# never take that branch. First establish that the mutation still compiles, then
# require the independent complete-definition audit to reject it.
if has_model util.safety_checks.checked_bool; then
    for mutation in boolean copy offset; do
        # These leaves are external interpretations, not annotated Rust roots:
        # bindings.json therefore cannot answer whether their controls apply.
        if [[ $mutation == offset ]] && ! grep -q '^def util\.copy_unchecked_at ' Zerocopy/FunsExternal.lean; then continue; fi
        python3 - "$mutation" <<'PYCONTROL'
from pathlib import Path
import sys
p = Path("Zerocopy/FunsExternal.lean")
s = p.read_text()
if sys.argv[1] == 'boolean':
    start = s.index('noncomputable def util.transmute_unchecked')
    end = s.index('\n\n', start)
    before = s[start:end]
    after = before.replace('else forbiddenExecution', 'else .ok (cast hd.symm false)', 1)
elif sys.argv[1] == 'copy':
    start = s.index('def util.copy_unchecked')
    end = s.index('\n\n', start)
    before = s[start:end]
    after = before.replace('else forbiddenExecution', 'else .ok dst', 1)
else:
    start = s.index('def util.copy_unchecked_at')
    end = s.index('\n\n', start)
    before = s[start:end]
    after = before.replace('else forbiddenExecution', 'else .ok dst', 1)
if before == after:
    raise SystemExit('Storage boundary control no longer matches')
p.write_text(s[:start] + after + s[end:])
PYCONTROL
        check_model_mutant "permitted bad $mutation input" Zerocopy.FunsExternal
        expect_failure "permitted bad $mutation input" storage-guard-audit.log audit
        if ! grep -Eq 'Boolean conversion changed|byte copy changed|offset copy changed' "$backup/storage-guard-audit.log"; then
            cat "$backup/storage-guard-audit.log" >&2; exit 1
        fi
        expect_failure "permitted bad $mutation input" storage-guard-proof.log \
            aeneas_lake env lean -DwarningAsError=true SafetyTests.lean
        restore_build
    done
fi

# Harmless extracted-function imports are ordinary acyclic dependencies.
# Their presence cannot replace the independently authored outcome expectation.
if [[ -f ModelSupport.lean ]]; then
    for transitive in false true; do
        python3 - "$transitive" <<'PYCONTROL'
from pathlib import Path
import sys
support = Path("ModelSupport.lean")
source = support.read_text()
marker = '@[expose] public section'
if source.count(marker) != 1:
    raise SystemExit("Compiled support import control requires the exact support header boundary")
if sys.argv[1] == 'true':
    helper = Path("SpecPrelude.lean")
    text = helper.read_text()
    if text.count(marker) != 1:
        raise SystemExit("Compiled support import control requires the exact helper header boundary")
    helper.write_text(text.replace(marker, 'public import «Zerocopy».Funs\n' + marker))
    imported = '«SpecPrelude»'
else:
    imported = '«Zerocopy».Funs'
support.write_text(source.replace(marker, 'public import ' + imported + '\n' + marker))
PYCONTROL
        aeneas_lake build Required > "$backup/support-import-build.log" 2>&1 || {
            echo "Malformed compiled support import control" >&2
            cat "$backup/support-import-build.log" >&2; exit 1;
        }
        audit > "$backup/support-import-audit.log" 2>&1 || {
            echo "Harmless support function import rejected (transitive=$transitive)" >&2
            cat "$backup/support-import-audit.log" >&2; exit 1;
        }
        echo "Confirmed: harmless support function import accepted (transitive=$transitive)"
        restore_build
    done
fi

# Every independent conversion must exist in the generated checking module.
# These are well-formed modules with the canonical proof and Specs check intact.
reject_witness() {
    local mutation=$1 description=$2 diagnostic=$3
    python3 - "$mutation" <<'PYCONTROL'
from pathlib import Path
import sys
p = Path("Required.lean")
s = p.read_text()
command = 'check_contract Zerocopy.Obligations.min_spec using @Zerocopy.Proofs.min_spec\n'
if s.count(command) != 1:
    raise SystemExit("Independent witness coverage control no longer matches")
mutation = sys.argv[1]
replacement = ''
# Preserve the independently typed adequacy theorem when testing the later
# concrete witness audit, so a missing earlier check cannot mask the failure.
checked_context = ('namespace IndependentWitnessControl\n' + command +
    'end IndependentWitnessControl\n'
    'theorem Zerocopy.Obligations.min_spec_adequate :\n'
    '  contract_adequacy% Zerocopy.Specs.min_spec implies Zerocopy.Obligations.min_spec :=\n'
    '  IndependentWitnessControl.Zerocopy.Obligations.min_spec_adequate\n')
if mutation == 'wrong-kind':
    replacement = (checked_context +
        'def Zerocopy.Obligations.min_spec_checked : Zerocopy.Obligations.min_spec :=\n'
        '  IndependentWitnessControl.Zerocopy.Obligations.min_spec_checked\n')
elif mutation == 'wrong-type':
    replacement = checked_context + 'theorem Zerocopy.Obligations.min_spec_checked : True := by trivial\n'
elif mutation == 'missing-rows':
    example = 'example : Zerocopy.Specs.min_spec := @Zerocopy.Proofs.min_spec\n'
    if s.count(example) != 1 or 'def requiredTheorems ' in s:
        raise SystemExit("Compiled specification scope control no longer matches")
    s = s.replace(example, '') + '\ndef requiredTheorems : Array Name := #[]\n'
elif mutation == 'wrong-owner':
    proof = Path("Proofs/WitnessOwnerControl.lean")
    imported = 'import Proofs\n'
    if proof.exists() or s.count(imported) != 1:
        raise SystemExit("Independent witness ownership fixture no longer matches")
    # Keep the successful checking context in a separate owning module.
    # Importing normalization infrastructure into Proofs would change the
    # elaboration context of its existing raw and mathematical proofs.
    imports = ''.join(line + '\n' for line in s.splitlines()
                      if line.startswith('import '))
    normalizers = ''.join(line + '\n' for line in s.splitlines()
                          if line.startswith('attribute [local contract_simps] '))
    proof.parent.mkdir(exist_ok=True)
    proof.write_text(imports + 'open Lean\n\n' + normalizers + command)
    s = s.replace(imported, imported + 'import Proofs.WitnessOwnerControl\n')
elif mutation != 'missing':
    raise SystemExit("Unknown independent witness coverage mutation")
p.write_text(s.replace(command, replacement))
PYCONTROL
    aeneas_lake build Required > "$backup/witness-build.log" 2>&1 || {
        echo "Malformed independent witness control: $description" >&2
        cat "$backup/witness-build.log" >&2; exit 1;
    }
    expect_failure "$description" witness-audit.log audit
    if ! grep -Fq "$diagnostic" "$backup/witness-audit.log"; then
        cat "$backup/witness-audit.log" >&2; exit 1;
    fi
    rm -f Proofs/WitnessOwnerControl.lean
    restore_build
}
reject_witness missing "an omitted independent conversion" \
    "Missing arbitrary-outcome required theorem Zerocopy.Obligations.min_spec_adequate"
reject_witness wrong-kind "a definition replacing the independent theorem" \
    "Missing independent required theorem Zerocopy.Obligations.min_spec_checked"
reject_witness wrong-type "an independent theorem with an unrelated type" \
    "Zerocopy.Obligations.min_spec_checked does not prove its independent required proposition"
reject_witness wrong-owner "an independent witness declared in a proof module" \
    "Zerocopy.Obligations.min_spec_adequate must be declared in the required checks module"
reject_witness missing-rows "omitted check rows hidden by an empty legacy roster" \
    "Missing arbitrary-outcome required theorem Zerocopy.Obligations.min_spec_adequate"

# Imported lookalikes, nested compiler helpers and mutable tags do not choose
# coverage. Only immediate proposition definitions owned by Specs are roots.
python3 - <<'PYCONTROL'
from pathlib import Path
required = Path("Required.lean")
required.write_text(required.read_text() + '''
namespace Zerocopy.Specs
def importedScopeLookalike : Prop := True
end Zerocopy.Specs
''')
specs = Path("Specs.lean")
specs.write_text(specs.read_text() + '''
namespace Zerocopy.Specs.min_spec
def nestedScopeHelper : Prop := True
end Zerocopy.Specs.min_spec
''')
PYCONTROL
aeneas_lake build Required > "$backup/scope-helper-build.log" 2>&1 || {
    cat "$backup/scope-helper-build.log" >&2; exit 1;
}
audit > "$backup/scope-helper-audit.log" 2>&1 || {
    cat "$backup/scope-helper-audit.log" >&2; exit 1;
}
echo "Confirmed: scope excludes imported and nested helpers"
restore_build

# Move valid propositions to an imported model module. Everything still builds,
# but an empty generated Specs module must not manufacture a zero-proof audit.
python3 - <<'PYCONTROL'
from pathlib import Path
other = Path("Zerocopy/ScopeControl.lean")
if other.exists():
    raise SystemExit("Compiled scope control fixture already exists")
specs = Path("Specs.lean")
other.write_bytes(specs.read_bytes())
specs.write_text('module\npublic import Zerocopy.ScopeControl\n')
PYCONTROL
aeneas_lake build Required > "$backup/empty-scope-build.log" 2>&1 || {
    echo "Malformed empty compiled scope control" >&2
    cat "$backup/empty-scope-build.log" >&2; exit 1;
}
expect_failure "an empty owned specification scope" empty-scope-audit.log audit
if ! grep -Fq 'No compiled inline specifications were found' "$backup/empty-scope-audit.log"; then
    cat "$backup/empty-scope-audit.log" >&2; exit 1;
fi
restore_files
rm Zerocopy/ScopeControl.lean
restore_build

# Every present source specification must equal its owned compiled call in
# both models. Preserve valid canonical proofs/callers so omitted roots reach
# the audit; removing a generated row cannot erase a present source fence.
reject_binding_image() {
    local mutation=$1 description=$2 diagnostic=$3
    python3 - "$mutation" <<'PYCONTROL'
from pathlib import Path
import json, re, sys
mutation = sys.argv[1]
manifest_path = Path("bindings.json")
manifest = json.loads(manifest_path.read_text())
models = manifest["bindings"]
if (manifest.get("version") != 3 or manifest.get("mode") != "verified-live"
        or not isinstance(models, dict) or not all(
        isinstance(key, str) and isinstance(value, dict) and value.get("kind") in ("function", "type") and isinstance(value.get("raw"), str) for key, value in models.items())):
    raise SystemExit("Invalid verified model bindings for binding-image controls")
keys = [key for key, value in models.items() if value["kind"] == "function" and value["raw"] == "Zerocopy.util.min"]
if len(keys) != 1:
    raise SystemExit("Binding-image control requires a unique min mapping")
if mutation == "missing-map":
    del models[keys[0]]
    # Keep the admission roster internally consistent so this control reaches
    # the independent compiled-root coverage check it is intended to challenge.
    for stage in manifest.get("admission", {}).get("stages", {}).values():
        stage["roots"].remove(keys[0])
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
elif mutation == "duplicate-map":
    if [entry["raw"] for entry in models.values()].count("Zerocopy.util.max") != 1:
        raise SystemExit("Binding-image duplicate control requires a unique max mapping")
    models[keys[0]]["raw"] = "Zerocopy.util.max"
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
elif mutation in ("missing-spec", "duplicate-spec"):
    p = Path("Specs.lean")
    s = p.read_text()
    fence = re.compile(r'(?m)^check_model_inputs Zerocopy\.util\.min with 0 type parameters\n'
        r'aeneas_spec_begin\n'
        r'spec min_spec\b[^\n]*\n(?:(?!^aeneas_spec_(?:begin|end)\b).)*?'
        r'^aeneas_spec_end\n'
        r'check_spec_binding Zerocopy\.Specs\.min_spec for Zerocopy\.util\.min with 2\n',
        re.S | re.M)
    matches = list(fence.finditer(s))
    if len(matches) != 1 or 'for @Zerocopy.util.min ' not in matches[0].group():
        raise SystemExit("Binding-image control requires the unique complete min fence/command")
    match = matches[0]
    block = match.group()
    if mutation == "missing-spec":
        other = Path("Zerocopy/ScopeControl.lean")
        marker = '@[expose] public section'
        start = s.find('aeneas_spec_begin\n')
        if (other.exists() or start < 0 or s.count(marker) != 1
                or s[:start].count('namespace Zerocopy.Specs\n') != 1
                or s.count('end Zerocopy.Specs\n') != 1):
            raise SystemExit("Binding-image carrier module boundary no longer matches")
        # Reuse this stage's module/import/open preamble without importing Specs.
        other.write_text(s[:start] + block + '\nend Zerocopy.Specs\n')
        s = s[:match.start()] + s[match.end():]
        s = s.replace(marker, 'public import Zerocopy.ScopeControl\n' + marker)
        required = Path("Required.lean")
        rows = required.read_text()
        for row in ('example : Zerocopy.Specs.min_spec := @Zerocopy.Proofs.min_spec\n',
                    'check_contract Zerocopy.Obligations.min_spec using @Zerocopy.Proofs.min_spec\n'):
            if rows.count(row) != 1:
                raise SystemExit("Binding-image min checking row no longer matches")
            rows = rows.replace(row, '')
        required.write_text(rows)
    else:
        name = 'bindingImageDuplicate'
        if name in s or block.count('spec min_spec') != 1:
            raise SystemExit("Binding-image duplicate specification fixture already exists")
        duplicate = block.replace('spec min_spec', 'spec ' + name).replace(
            'check_spec_binding Zerocopy.Specs.min_spec ',
            'check_spec_binding Zerocopy.Specs.' + name + ' ')
        s = s[:match.end()] + '\n' + duplicate + s[match.end():]
    p.write_text(s)
else:
    raise SystemExit("Unknown binding-image control mutation")
PYCONTROL
    aeneas_lake build Required > "$backup/binding-image-build.log" 2>&1 || {
        echo "Malformed binding-image control: $description" >&2
        cat "$backup/binding-image-build.log" >&2; exit 1;
    }
    expect_failure "$description" binding-image-audit.log audit
    if ! grep -Eq "$diagnostic" "$backup/binding-image-audit.log"; then
        cat "$backup/binding-image-audit.log" >&2; exit 1;
    fi
    restore_files
    rm -f Zerocopy/ScopeControl.lean
    restore_build
    audit > "$backup/binding-image-restore-audit.log" 2>&1 || {
        cat "$backup/binding-image-restore-audit.log" >&2; exit 1;
    }
}
reject_binding_image missing-spec "a Rust root moved out of the owned Specs scope" \
    'Function binding for zerocopy::util::min does not name a compiled inline specification'
reject_binding_image missing-map "a compiled root missing from the binding image" \
    'Compiled inline specification models disagree with bindings: missing .*; unexpected .*Zerocopy[.]util[.]min'
reject_binding_image duplicate-map "two Rust bindings assigned the same model" \
    'Model bindings repeat model Zerocopy[.]util[.]max'
reject_binding_image duplicate-spec "two owned specifications targeting the same model" \
    'Compiled inline specifications repeat model Zerocopy[.]util[.]min'

# Type coverage is audited by the production Check, independently of function
# checks. Keep every model and proof well formed before accepting a rejection.
reject_model_image() {
    local mutation=$1 description=$2 diagnostic=$3
    python3 - "$mutation" <<'PYCONTROL'
from pathlib import Path
import json, sys
manifest_path = Path("bindings.json")
manifest = json.loads(manifest_path.read_text())
entries = manifest.get("bindings")
if (manifest.get("version") != 3 or manifest.get("mode") != "verified-live"
        or not isinstance(entries, dict)):
    raise SystemExit("Invalid verified model binding table for failure controls")
mutation = sys.argv[1]
rounding = "zerocopy::layout::RoundingAlignAndPhase"
error = "zerocopy::layout::MetadataCastError"
if mutation in ("missing-authored-image", "wrong-authored-model"):
    entry = entries.get(rounding)
    if not entry or entry["kind"] != "type" or not entry["authored"]:
        raise SystemExit("Authored model omission fixture no longer matches")
    if mutation == "missing-authored-image":
        del entries[rounding]
    else:
        if entry["model"] == entry["fields"]:
            raise SystemExit("Authored model control requires a distinct mathematical model")
        entry["model"] = entry["fields"]
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
elif mutation == "missing-default-image":
    entry = entries.get(error)
    if not entry or entry["kind"] != "type" or entry["authored"]:
        raise SystemExit("Default model omission fixture no longer matches")
    del entries[error]
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
elif mutation in ("moved-shapes", "moved-models"):
    module, target = (("ModelShapes", "ShapeControl") if mutation == "moved-shapes"
                      else ("Models", "ModelControl"))
    path = Path(module + ".lean")
    other = Path("Zerocopy/" + target + ".lean")
    if other.exists():
        raise SystemExit("Model ownership control fixture already exists")
    other.write_bytes(path.read_bytes())
    path.write_text('module\npublic import Zerocopy.' + target + '\n')
else:
    raise SystemExit("Unknown model-image control mutation")
PYCONTROL
    aeneas_lake build Required > "$backup/model-image-build.log" 2>&1 || {
        echo "Malformed model-image control: $description" >&2
        cat "$backup/model-image-build.log" >&2; exit 1;
    }
    expect_failure "$description" model-image-audit.log audit
    if ! grep -Eq "$diagnostic" "$backup/model-image-audit.log"; then
        cat "$backup/model-image-audit.log" >&2; exit 1;
    fi
    restore_files
    rm -f Zerocopy/ShapeControl.lean Zerocopy/ModelControl.lean
    restore_build
    audit > "$backup/model-image-restore-audit.log" 2>&1 || {
        cat "$backup/model-image-restore-audit.log" >&2; exit 1;
    }
}
# Capability selection uses the compiled source carrier, independently of the
# manifest rows whose deletion is under test. Each mutant must build first.
if grep -Eq '^(structure|inductive)[[:blank:]]+layout[.]RoundingAlignAndPhase([[:blank:]]|$)' Zerocopy/Types.lean; then
    reject_model_image wrong-authored-model "an authored model associated with the wrong shape" \
        'Compiled model .* disagrees with its Rust owner binding'
    reject_model_image missing-authored-image "an authored model omitted from the binding table" \
        'Local raw type image has no source binding: zerocopy::layout::RoundingAlignAndPhase'
fi
if grep -Eq '^(structure|inductive)[[:blank:]]+layout[.]MetadataCastError([[:blank:]]|$)' Zerocopy/Types.lean; then
    reject_model_image missing-default-image "an unannotated carrier omitted from the binding table" \
        'Local raw type image has no source binding: zerocopy::layout::MetadataCastError'
fi
# Without extracted nominal types these modules own no declarations, so moving
# their empty contents cannot violate declaration ownership. The baseline audit
# above checks that the binding table covers every extracted nominal type.
if has_binding type; then
    reject_model_image moved-shapes "model shapes moved out of their generated module" \
        'Mathematical fields and model must be owned by ModelShapes'
    reject_model_image moved-models "decoders and providers moved out of their generated module" \
        'Decoder and provider must be owned by Models'
fi

# Generic alignment reads select the ABI family. No-layout and pointer-only
# models intentionally have no such declaration and retain their earlier scope.
if grep -Fq 'def core.mem.align_of' Zerocopy/FunsExternal.lean; then
    # Run the actual ABI-checking source in an isolated environment. Required
    # proofs need not compile for a wrong pointer-width model, and removing an
    # input must reach the audit rather than merely break one of its consumers.
    python3 - <<'PYCONTROL'
from pathlib import Path
s = Path("Check.lean").read_text()
begin = '  let env ← getEnv\n'
end = '  let mut proofModules : Array ModuleIdx := #[]'
if s.count(begin) != 1 or s.count(end) != 1:
    raise SystemExit("External-input audit control boundaries no longer match")
body = s[s.index(begin):s.index(end)]
Path("NegativeControl.lean").write_text(
    'import Lean\nimport Zerocopy.FunsExternal\nopen Lean Elab Command\nrun_elab do\n' + body)
PYCONTROL
    aeneas_lake env lean -DwarningAsError=true NegativeControl.lean \
        > "$backup/abi-baseline.log" 2>&1 || {
        cat "$backup/abi-baseline.log" >&2; exit 1;
    }
    reject_abi() {
        local description=$1 mutation=$2 diagnostic=$3
        python3 - "$mutation" <<'PYCONTROL'
from pathlib import Path
import sys
p = Path("Zerocopy/FunsExternal.lean")
s = p.read_text()
def replace(old, new):
    global s
    if s.count(old) != 1:
        raise SystemExit("External-input negative control no longer matches: " + old)
    s = s.replace(old, new)
size = 'axiom Zerocopy.RustLayout.size (T : Type) : Usize'
align = 'axiom Zerocopy.RustLayout.align (T : Type) : Usize'
mutation = sys.argv[1]
if mutation in ('missing-size', 'missing-align', 'missing-both'):
    if mutation != 'missing-align':
        replace(size, '')
        replace('Zerocopy.RustLayout.size T', '0#usize')
    if mutation != 'missing-size':
        replace(align, '')
        replace('Zerocopy.RustLayout.align T', '1#usize')
        replace('core.mem.align_of (T : Type)', 'core.mem.align_of (_T : Type)')
elif mutation == 'wrong-kind':
    replace(size, 'def Zerocopy.RustLayout.size (_T : Type) : Usize := 0#usize')
elif mutation == 'wrong-signature':
    replace(size, 'axiom Zerocopy.RustLayout.size (T : Type) : Nat')
    replace('Zerocopy.RustLayout.size T', '0#usize')
elif mutation == 'ignored-align':
    replace('Zerocopy.RustLayout.align T', '1#usize')
    replace('core.mem.align_of (T : Type)', 'core.mem.align_of (_T : Type)')
elif mutation == 'ignored-size':
    replace('Zerocopy.RustLayout.size T', '0#usize')
elif mutation == 'wrong-pointer-width':
    replace('System.Platform.numBits / 8', 'System.Platform.numBits / 8 + 1')
else:
    raise SystemExit("Unknown external-input control mutation")
p.write_text(s)
PYCONTROL
        check_model_mutant "$description" Zerocopy.FunsExternal
        expect_failure "$description" abi-audit.log \
            aeneas_lake env lean -DwarningAsError=true NegativeControl.lean
        if ! grep -Fq "$diagnostic" "$backup/abi-audit.log"; then
            cat "$backup/abi-audit.log" >&2; exit 1;
        fi
        restore_files
    }
    reject_abi "a missing generic ABI size input" missing-size \
        "Missing external layout input Zerocopy.RustLayout.size"
    reject_abi "a missing generic ABI alignment input" missing-align \
        "Missing external layout input Zerocopy.RustLayout.align"
    reject_abi "both generic ABI inputs missing" missing-both \
        "Missing external layout input Zerocopy.RustLayout.size"
    reject_abi "a definition replacing an arbitrary ABI data input" wrong-kind \
        "Missing external layout input Zerocopy.RustLayout.size"
    reject_abi "an ABI data input with the wrong signature" wrong-signature \
        "External layout input Zerocopy.RustLayout.size changed its data-only signature"
    reject_abi "an alignment read ignoring its ABI input" ignored-align \
        "External alignment read changed its data-input interpretation"
    reject_abi "a generic size read ignoring its ABI input" ignored-size \
        "External size read changed its data-input interpretation"
    reject_abi "an incorrect Usize pointer-width read" wrong-pointer-width \
        "External size read changed its data-input interpretation"
    rm NegativeControl.lean
    restore_build
    audit
fi

if [[ $1 == verification ]]; then
    echo '-- Harmless generated-comment difference' >> Zerocopy/Funs.lean
    python3 "$repo/verification/aeneas/golden.py" compare \
        "$PWD/Zerocopy" "$repo/verification/aeneas/golden"
    aeneas_lake build Required > "$backup/comment-build.log" 2>&1 || {
        cat "$backup/comment-build.log" >&2; exit 1;
    }
    audit
    echo "Confirmed: comment drift passes comparison and live proofs"
    restore_build
fi

# Ordinary theorems must establish the proposition expanded by the spec command.
# Native proofs use the same total/partial semantics as the inline specs.
reject_spec() {
    local description=$1
    cat > NegativeControl.lean <<'LEAN'
import SpecsSyntax
import ModelPrelude
open Aeneas Aeneas.Std
LEAN
    cat >> NegativeControl.lean
    expect_failure "$description" spec-build.log aeneas_lake env lean -DwarningAsError=true NegativeControl.lean
    if ! grep -q 'unsolved goals' "$backup/spec-build.log" ||
        ! grep -q '⊢ False' "$backup/spec-build.log"; then
        cat "$backup/spec-build.log" >&2; exit 1
    fi
    rm NegativeControl.lean
}
reject_spec "panic under a total spec" <<'LEAN'
namespace NegativeControl
def panicking : Result Nat := .fail Error.panic
spec panic
  for @panicking with 0 type parameters
  ensures _ => True
theorem attempted : panic := by simp [panic, panicking]
end NegativeControl
LEAN
reject_spec "divergence under a total spec" <<'LEAN'
namespace NegativeControl
def divergent : Result Nat := .div
spec diverging
  for @divergent with 0 type parameters
  ensures _ => True
theorem attempted : diverging := by simp [diverging, divergent]
end NegativeControl
LEAN
reject_spec "panic under a partial spec" <<'LEAN'
namespace NegativeControl
def panicking : Result Nat := .fail Error.panic
partial spec panic
  for @panicking with 0 type parameters
  ensures _ => True
theorem attempted : panic := by simp [panic, panicking]
end NegativeControl
LEAN
reject_spec "an incorrect successful return under a partial spec" <<'LEAN'
namespace NegativeControl
def zero : Result Nat := .ok 0
partial spec wrong_return
  for @zero with 0 type parameters
  ensures out => out = 1
theorem attempted : wrong_return := by simp [wrong_return, zero, AeneasSpecs.RustModel.decode]
end NegativeControl
LEAN
reject_spec "divergence under a total mathematical-view spec" <<'LEAN'
namespace NegativeControl
def divergent : Result Nat := .div
spec diverging
  for @divergent with 0 type parameters
  ensures out => out = 0
theorem attempted : diverging := by simp [diverging, divergent]
end NegativeControl
LEAN
reject_spec "an incorrect mathematical view" <<'LEAN'
namespace NegativeControl
def zero : Result Nat := .ok 0
spec wrong_view
  for @zero with 0 type parameters
  ensures out => Nat.succ out = 0
  ensures(raw) out => out = 0
theorem attempted : wrong_view := by simp [wrong_view, zero]
end NegativeControl
LEAN


if [[ -f Loops.lean ]]; then
    [[ -f SupportTests.lean ]] || {
        echo "Indexed-loop capability requires SupportTests.lean" >&2; exit 1;
    }
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
        expect_failure "$description" loop-build.log aeneas_lake build SupportTests
        cp "$backup/SupportTests.lean" SupportTests.lean
    }
    reject_loop "a stationary loop index" 's.2 + 1#usize' 's.2 + 0#usize'
    reject_loop "an incorrect loop prefix step" 's.1 + 1, j' 's.1 + 2, j'
    reject_loop "continuing a loop past its end" 'if s.2 < n then' 'if s.2 ≤ n then'
    aeneas_lake build SupportTests > "$backup/loop-restore-build.log" 2>&1 || {
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
registration = 'register_spec_step min_spec\n'
if s.count(old) != 1 or s.count(registration) != 1:
    raise SystemExit("Specification type control requires the exact unique min theorem/registration")
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
mutated = s[:start] + 'theorem min_spec : True := by trivial\n\n' + s[end:]
p.write_text(mutated.replace(registration, ''))
module = str(p.with_suffix('')).replace('/', '.')
Path('NegativeControl.lean').write_text('import ' + module + '\nimport Specs\n' +
    'example : Zerocopy.Specs.min_spec := @Zerocopy.Proofs.min_spec\n')
print(module)
PYCONTROL
)
# Compile just its owning module: callers of min may otherwise fail before
# the independent type check is reached. This is the same example as Required.
aeneas_lake build "+$min_module" > "$backup/min-module-build.log" 2>&1 || {
    cat "$backup/min-module-build.log" >&2; exit 1;
}
expect_failure "an unrelated registered theorem in place of the inline min spec" wrong-type-build.log aeneas_lake env lean NegativeControl.lean
if ! grep -qi 'type mismatch' "$backup/wrong-type-build.log" ||
    ! grep -q 'min_spec' "$backup/wrong-type-build.log"; then
    cat "$backup/wrong-type-build.log" >&2; exit 1
fi
rm NegativeControl.lean
restore_build

min_module=$(python3 - <<'PYCONTROL'
from pathlib import Path
paths = [Path("Proofs.lean"), *Path("Proofs").rglob("*.lean")]
old = 'theorem min_spec : Zerocopy.Specs.min_spec := by'
matched = [p for p in paths if old in p.read_text()]
if len(matched) != 1:
    raise SystemExit("Proof declaration-kind control no longer matches")
p = matched[0]
s = p.read_text()
registration = 'register_spec_step min_spec\n'
if s.count(old) != 1 or s.count(registration) != 1:
    raise SystemExit("Proof declaration-kind control requires the exact unique min theorem/registration")
p.write_text(s.replace(old, 'def min_spec : Zerocopy.Specs.min_spec := by').replace(registration, ''))
print(str(p.with_suffix('')).replace('/', '.'))
PYCONTROL
)
# Keep the definition well formed while testing the earlier theorem-kind guard.
aeneas_lake build "+$min_module" > "$backup/definition-module-build.log" 2>&1 || {
    cat "$backup/definition-module-build.log" >&2; exit 1;
}
expect_failure "a definition in place of a registered theorem" definition-build.log build_required
if ! grep -Fq 'Required contract candidate must be a theorem: Zerocopy.Proofs.min_spec' "$backup/definition-build.log"; then
    cat "$backup/definition-build.log" >&2; exit 1
fi
restore_build

# Exercise dependency feedback without prescribing production proof structure.
# Select by the arithmetic extraction binding, independently of how caller
# proofs are organized. A selected missing or changed fixture must fail.
if has_model util.checks.check_arithmetic; then
    audit > "$backup/dependency-baseline-audit.log" 2>&1 || {
        cat "$backup/dependency-baseline-audit.log" >&2; exit 1;
    }
    cp proof-dependencies.json "$backup/padding-baseline.json"
    padding_dependency_fixture() {
        python3 - "$1" "$backup" <<'PYCONTROL'
from pathlib import Path
import sys
mode, backup = sys.argv[1], Path(sys.argv[2])
if mode not in ('direct', 'unavailable', 'auxiliary', 'independent'):
    raise SystemExit("Unknown padding dependency fixture")
caller = Path("Proofs/ArithmeticChecks.lean")
callee = Path("Proofs/Util.lean")
helper = Path("Proofs/PaddingDependencyControl.lean")
for fixture in (caller, callee, Path("Required.lean")):
    if not (backup / fixture).is_file():
        raise SystemExit("Selected padding dependency fixture is missing: " + str(fixture))
header = 'theorem arithmetic_checks_spec : Specs.arithmetic_checks_spec := by'
body = """
  intro len align _ _ _ _
  apply WP.spec_mono (Raw.arithmetic_checks len align)
  intro result _
  exact ⟨(), rfl, trivial⟩
"""
source = (backup / caller).read_text()
original = header + body
if source.count(original) != 1 or source.count(header) != 1:
    raise SystemExit("Selected arithmetic dependency fixture is missing or changed")
callee_source = (backup / callee).read_text()
callee_header = 'theorem padding_lt_alignment : Zerocopy.Specs.padding_lt_alignment := by'
registration = 'register_spec_step padding_lt_alignment\n'
if callee_source.count(callee_header) != 1 or callee_source.count(registration) != 1:
    raise SystemExit("Selected canonical padding fixture is missing or changed")
callee_body, separator, _ = callee_source.partition(callee_header)[2].partition('\n' + registration)
if not separator or callee_body.count('Raw.padding_lt_alignment') != 1:
    raise SystemExit("Independent padding transport requires its exact Raw reference")
reference = 'Zerocopy.Proofs.padding_lt_alignment'
required = (backup / 'Required.lean').read_text()
if mode in ('auxiliary', 'independent'):
    alias = 'private def padding_alias := Zerocopy.Proofs.padding_lt_alignment\n'
    if mode == 'independent':
        alias = ('private theorem padding_alias : Zerocopy.Specs.padding_lt_alignment := by' +
                 callee_body.replace('Raw.padding_lt_alignment',
                                     'Zerocopy.Proofs.Raw.padding_lt_alignment') + '\n')
    helper.write_text("""module
public import Proofs.Util
@[expose] public section
open Aeneas Aeneas.Std AeneasSpecs Zerocopy.Proofs
namespace PaddingDependencyControl
""" + alias + """theorem padding_proxy : Zerocopy.Specs.padding_lt_alignment := by exact padding_alias
end PaddingDependencyControl
""")
    import_at = '@[expose] public section'
    if source.count(import_at) != 1:
        raise SystemExit("Selected arithmetic module framing is missing or changed")
    source = source.replace(import_at, 'public import Proofs.PaddingDependencyControl\n' + import_at)
    # Check traverses configured native modules. Include this scratch helper
    # in that same boundary; its namespace alone must not grant admission.
    audit_header = 'def auditModuleNames : Array Name := #['
    if required.count(audit_header) != 1:
        raise SystemExit("Selected audit module fixture is missing or changed")
    required = required.replace(audit_header, audit_header + '`Proofs.PaddingDependencyControl, ')
    reference = 'PaddingDependencyControl.padding_proxy'
wrapped = (header + '\n  exact And.left (show Specs.arithmetic_checks_spec ∧ '
           'Specs.padding_lt_alignment from\n    ⟨(by\n' +
           ''.join('    ' + line + '\n' for line in body.splitlines()[1:]) +
           '    ), ' + reference + '⟩)\n')
caller.write_text(source.replace(original, wrapped))
Path('Required.lean').write_text(required)
if mode == 'unavailable':
    callee_source = callee_source.replace(callee_header,
        'theorem unavailable_padding_lt_alignment : Zerocopy.Specs.padding_lt_alignment := by')
    callee_source = callee_source.replace(registration, '')
callee.write_text(callee_source)
PYCONTROL
    }
    check_padding_dependency() {
        python3 - "$1" "$backup/padding-baseline.json" <<'PYCONTROL'
from pathlib import Path
import json, sys
mode = sys.argv[1]
caller = 'Zerocopy.Proofs.arithmetic_checks_spec'
callee = 'Zerocopy.Proofs.padding_lt_alignment'
def dependencies(path):
    entries = [entry for entry in json.loads(Path(path).read_text()) if entry['theorem'] == caller]
    if len(entries) != 1:
        raise SystemExit("Dependency graph lacks its exact arithmetic caller")
    return set(entries[0]['depends_on'])
baseline = dependencies(sys.argv[2])
if callee in baseline:
    raise SystemExit("Original arithmetic fixture already references the canonical padding root")
expected = baseline | {callee} if mode == 'present' else baseline
if mode not in ('present', 'absent') or dependencies('proof-dependencies.json') != expected:
    raise SystemExit("Dependency graph does not match the controlled canonical padding edge")
PYCONTROL
    }
    padding_dependency_fixture direct
    aeneas_lake build Required > "$backup/dependency-direct-build.log" 2>&1 || {
        cat "$backup/dependency-direct-build.log" >&2; exit 1;
    }
    audit > "$backup/dependency-direct-audit.log" 2>&1 || {
        cat "$backup/dependency-direct-audit.log" >&2; exit 1;
    }
    check_padding_dependency present
    echo "Confirmed: dependency reporting retains the direct canonical callee"
    padding_dependency_fixture unavailable
    aeneas_lake build +Proofs.Util > "$backup/callee-owner-build.log" 2>&1 || {
        echo "Malformed callee control: renamed owning Util module did not compile" >&2
        cat "$backup/callee-owner-build.log" >&2; exit 1;
    }
    expect_failure "an unavailable canonical callee theorem" callee-build.log aeneas_lake build +Proofs.ArithmeticChecks
    if ! grep -q 'Unknown identifier.*padding_lt_alignment' "$backup/callee-build.log"; then
        cat "$backup/callee-build.log" >&2; exit 1
    fi
    restore_build
    padding_dependency_fixture auxiliary
    aeneas_lake build Required > "$backup/helper-build.log" 2>&1 || {
        cat "$backup/helper-build.log" >&2; exit 1;
    }
    audit > "$backup/helper-audit.log" 2>&1 || {
        cat "$backup/helper-audit.log" >&2; exit 1;
    }
    check_padding_dependency present
    echo "Confirmed: dependency reporting follows a private helper in an auxiliary native module"
    padding_dependency_fixture independent
    aeneas_lake build Required > "$backup/independent-helper-build.log" 2>&1 || {
        cat "$backup/independent-helper-build.log" >&2; exit 1;
    }
    audit > "$backup/independent-helper-audit.log" 2>&1 || {
        cat "$backup/independent-helper-audit.log" >&2; exit 1;
    }
    check_padding_dependency absent
    echo "Confirmed: dependency reporting omits a callee replaced by an independent auxiliary proof"
    rm -f Proofs/PaddingDependencyControl.lean
    restore_build
    audit > "$backup/dependency-restored-audit.log" 2>&1 || {
        cat "$backup/dependency-restored-audit.log" >&2; exit 1;
    }
    check_padding_dependency absent
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
aeneas_lake build Required > "$backup/private-helper-build.log" 2>&1 || {
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
aeneas_lake build Required > "$backup/auxiliary-axiom-build.log" 2>&1 || {
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
aeneas_lake build Required > "$backup/unused-axiom-build.log" 2>&1 || {
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
aeneas_lake build Required > "$backup/sorry-build.log" 2>&1 || {
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
    'theorem Zerocopy.Obligations.min_spec_adequate :\n' +
    '  contract_adequacy% Zerocopy.Specs.min_spec implies Zerocopy.Obligations.min_spec := by sorry\n' +
    'theorem Zerocopy.Obligations.min_spec_checked : Zerocopy.Obligations.min_spec :=\n' +
    '  required_contract_instance% Zerocopy.Proofs.min_spec with Zerocopy.Obligations.min_spec_adequate')
p.write_text(s)
PYCONTROL
aeneas_lake build Required > "$backup/required-sorry-build.log" 2>&1 || {
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
expect_failure "an unrelated True theorem as an independent required contract" unrelated-build.log aeneas_lake env lean NegativeControl.lean
rm NegativeControl.lean

# Once arithmetic postconditions are strengthened, a valid earlier weak
# round-down contract must fail the independently written required proposition.
if [[ -f Arithmetic.lean ]]; then
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
  apply WP.spec_mono (Zerocopy.Proofs.Raw.round_down_spec n align h)
  intro m hm
  exact ⟨hm.1, hm.2.2.1⟩
end WeakerControl
LEAN
    aeneas_lake env lean -DwarningAsError=true NegativeControl.lean > "$backup/weaker-build.log" 2>&1 || {
        cat "$backup/weaker-build.log" >&2; exit 1;
    }
    cat >> NegativeControl.lean <<'LEAN'
check_contract Zerocopy.Obligations.round_down_spec using WeakerControl.round_down_spec
LEAN
    expect_failure "a valid weaker round-down contract as the independent required contract" weaker-required.log aeneas_lake env lean NegativeControl.lean
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
    check_model_mutant "$description"
    expect_failure "$description" model-build.log build_required
    cp "$backup/Zerocopy/Funs.lean" Zerocopy/Funs.lean
}
if [[ -f Arithmetic.lean ]]; then
    reject_model "always-zero padding under the exact arithmetic spec" 'ok (i2 &&& mask)' 'ok 0#usize'
    reject_model "always-zero round-down under the exact arithmetic spec" 'ok (n &&& mask)' 'ok 0#usize'
fi
if has_model layout.DstLayout.pad_to_align; then
    # Both the earlier sized-only contract and normalized layout contract check
    # this flag. Generated scalar variable names are not a capability boundary.
    shallow_flag=$(python3 - <<'PYCONTROL'
from pathlib import Path
import re
s = Path("Zerocopy/Funs.lean").read_text()
start = s.index('def layout.DstLayout.pad_to_align')
end = s.find('/-- ', start)
if end < 0:
    end = len(s)
matches = re.findall(r'statically_shallow_unpadded := \([A-Za-z_][A-Za-z0-9_]* = 0#usize\)', s[start:end])
if len(matches) != 1:
    raise SystemExit("Shallow-padding flag negative control no longer matches")
print(matches[0])
PYCONTROL
)
    reject_model "an incorrect shallow-padding flag" "$shallow_flag" \
        'statically_shallow_unpadded := true' 'layout.DstLayout.pad_to_align'
fi
if has_model layout.DstLayout.extend; then
    # Field extension identifies full normalized composition. Earlier stages
    # contain only a sized-padding contract, without the recursive DST rule.
    reject_model "conflating physical offset with the size base" \
        'Usize.checked_add offset tsl.offset' \
        'Usize.checked_add offset tsl.size_base' 'layout.DstLayout.extend'
    reject_model "dropping inner rounding under outer packing" \
        'util.padding_needed_for trailing.size_base size_align' \
        'util.padding_needed_for trailing.size_base self.align' 'layout.DstLayout.pad_to_align'
fi

restore_build

# Independent expectations must reject a genuinely proven weaker contract.
reject_weak_outcome() {
    local description=$1
    cat > NegativeControl.lean
    # Check the candidate proof alone first; malformed Lean is no witness.
    sed '/^check_contract /d' NegativeControl.lean > WeakOutcome.lean
    aeneas_lake env lean -DwarningAsError=true WeakOutcome.lean > "$backup/weak-outcome-valid.log" 2>&1 || {
        cat "$backup/weak-outcome-valid.log" >&2; exit 1;
    }
    rm WeakOutcome.lean
    expect_failure "$description" weak-outcome-check.log \
        aeneas_lake env lean -DwarningAsError=true NegativeControl.lean
    rm NegativeControl.lean
}
reject_predicate() {
    local name=$1 replacement=$2 module=$3
    python3 - "$name" "$replacement" <<'PYCONTROL'
from pathlib import Path
import re, sys
p = Path("LayoutModel.lean")
s = p.read_text()
pattern = r'(?ms)^(def ' + re.escape(sys.argv[1]) + r'\b.*?: Prop :=).*?(?=^def )'
s, count = re.subn(pattern, lambda m: 'set_option linter.unusedVariables false in\n' + m[1] + ' ' + sys.argv[2] + '\n\n', s)
if count != 1:
    raise SystemExit("Outcome predicate negative control no longer matches")
p.write_text(s)
PYCONTROL
    check_model_mutant "a changed mathematical predicate $name" LayoutModel
    # The predicate's module was rebuilt above. Compile the test source itself:
    # Lake's --old mode can reuse its output despite the changed import.
    expect_failure "a changed mathematical predicate $name" outcome-test.log \
        aeneas_lake env lean -DwarningAsError=true "$module.lean"
    if ! grep -Fq "$module.lean:" "$backup/outcome-test.log"; then
        cat "$backup/outcome-test.log" >&2; exit 1;
    fi
    restore_files
}
if has_model layout.DstLayout.validate_cast_and_convert_metadata; then
    [[ -f OutcomeTests.lean ]] || {
        echo "Outcome capability requires OutcomeTests.lean" >&2; exit 1;
    }
    reject_weak_outcome "a termination-only cast contract" <<'LEAN'
import Proofs
import Obligations
import RequiredContracts
open Aeneas Aeneas.Std Zerocopy Zerocopy.Proofs AeneasContracts

namespace CastWeakContractControls
def terminationOnly : Prop :=
  ∀ (self : layout.DstLayout) (addr length : Usize) (side : layout.CastType),
    0 < self.align.val.val → addr.val + length.val ≤ Usize.max →
    (match self.size_info with
      | .Sized _ => True
      | .SliceDst t => 0 < t.size_rounding_align_and_phase._0.val.val ∧ 0 < t.elem_size.val) →
    ∃ r, layout.DstLayout.validate_cast_and_convert_metadata self addr length side = .ok r

theorem terminationOnly_proof : terminationOnly := by
  intro self addr length side ha hroom ht
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (Zerocopy.Proofs.Raw.validate_cast_spec self addr length side ha hroom ht)
  exact ⟨r, hr⟩
end CastWeakContractControls

-- Expected rejection; delete only this line for the positive proof-validity stage.
check_contract Zerocopy.Obligations.validate_cast_spec using CastWeakContractControls.terminationOnly_proof
LEAN
    reject_predicate castSpec True OutcomeTests
    restore_build
fi

if has_model layout.DstLayout.metadata_for_exact_size; then
    [[ -f OutcomeTests.lean ]] || {
        echo "Outcome capability requires OutcomeTests.lean" >&2; exit 1;
    }
    reject_weak_outcome "a termination-only metadata contract" <<'LEAN'
import Proofs
import Obligations
import RequiredContracts
open Aeneas Aeneas.Std Zerocopy Zerocopy.Proofs AeneasContracts

namespace MetadataWeakContractControls
def terminationOnly : Prop :=
  ∀ (self : layout.DstLayout) (size : Usize), 0 < self.align.val.val →
    (match self.size_info with
      | .Sized _ => True
      | .SliceDst t => t.elem_size.val ≠ 0 → 0 < t.size_rounding_align_and_phase._0.val.val) →
    ∃ r, layout.DstLayout.metadata_for_exact_size self size = .ok r

theorem terminationOnly_proof : terminationOnly := by
  intro self size ha ht
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (Zerocopy.Proofs.Raw.metadata_exact_spec self size ha ht)
  exact ⟨r, hr⟩
end MetadataWeakContractControls

-- Expected rejection; delete only this line for the positive proof-validity stage.
check_contract Zerocopy.Obligations.metadata_exact_spec using MetadataWeakContractControls.terminationOnly_proof
LEAN
    reject_predicate metadataSpec True OutcomeTests
    restore_build
fi

# Positive examples keep supported constructor preconditions inhabited.
if has_model layout.DstLayout.for_repr_c_struct; then
    [[ -f LayoutModelDomainTests.lean ]] || {
        echo "Constructor capability requires LayoutModelDomainTests.lean" >&2; exit 1;
    }
    for predicate in alignmentDomain canonicalLayout constructionDomain; do
        reject_predicate "$predicate" False LayoutModelDomainTests
    done
    restore_build
fi

python3 - <<'PYCONTROL'
from pathlib import Path
p = Path("Zerocopy/Funs.lean")
s = p.read_text()
if s.count("if i > i1") != 1:
    raise SystemExit("Min negative control no longer matches generated output")
p.write_text(s.replace("if i > i1", "if i < i1"))
PYCONTROL
check_model_mutant "a min implementation with its comparison reversed"
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
aeneas_lake build
audit
)
case "${1:-}" in
    "")
        [[ $# == 0 ]] || { echo "Usage: $0 [golden-verification|verification]" >&2; exit 1; }
        check_workspace golden-verification
        check_workspace verification
        ;;
    golden-verification|verification)
        [[ $# == 1 ]] || { echo "Usage: $0 [golden-verification|verification]" >&2; exit 1; }
        check_workspace "$1"
        ;;
    *) echo "Usage: $0 [golden-verification|verification]" >&2; exit 1 ;;
esac
