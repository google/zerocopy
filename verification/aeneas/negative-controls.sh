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
tools_dir=${AENEAS_TOOLCHAIN_DIR:-"$repo/target/aeneas/toolchain"}
export PATH="$tools_dir/lean/bin:$PATH"
check_workspace() (
cd "$repo/target/aeneas/$1"
echo "Testing failure controls in $1"
[[ ! -e Zerocopy/ScopeControl.lean ]] || {
    echo "Compiled scope control fixture already exists" >&2; exit 1;
}
[[ ! -e Proofs/WitnessOwnerControl.lean ]] || {
    echo "Independent witness ownership fixture already exists" >&2; exit 1;
}
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
    rm -f NegativeControl.lean WeakOutcome.lean Zerocopy/ScopeControl.lean Zerocopy/ShapeControl.lean Zerocopy/ModelControl.lean Proofs/WitnessOwnerControl.lean
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
# A semantic mutation must remain a well-formed generated program. Only its
# dependent proofs should fail; a parser/type error cannot establish sensitivity.
check_model_mutant() {
    local description=$1 target=${2:-Zerocopy.Funs}
    lake build "+$target" > "$backup/model-well-formed.log" 2>&1 || {
        echo "Malformed model negative control: $description" >&2
        cat "$backup/model-well-formed.log" >&2; exit 1;
    }
}
# Reuse the verified root mapping instead of parsing model declaration syntax
# a second time. Missing/invalid manifests are errors, never absent capabilities.
has_model() {
    local present
    present=$(python3 - "$1" <<'PYCONTROL'
from pathlib import Path
import json, sys
manifest = json.loads(Path("bindings.json").read_text())
models = manifest["bindings"]
if (manifest.get("version") != 3 or manifest.get("mode") != "verified-live"
        or not isinstance(models, dict) or not all(
        isinstance(key, str) and isinstance(value, dict) and value.get("kind") in ("function", "type") and isinstance(value.get("raw"), str) for key, value in models.items())):
    raise SystemExit("Invalid verified model bindings for failure controls")
print("yes" if "Zerocopy." + sys.argv[1] in [entry["raw"] for entry in models.values() if entry["kind"] == "function"] else "no")
PYCONTROL
) || { echo "Cannot determine model capability" >&2; exit 1; }
    [[ $present == yes ]]
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

# Keep the source mutation well formed before requiring the compiled import
# audit to reject it. Quoted spellings resolve to the same actual Lean Names.
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
        lake build Required > "$backup/support-import-build.log" 2>&1 || {
            echo "Malformed compiled support import control" >&2
            cat "$backup/support-import-build.log" >&2; exit 1;
        }
        expect_failure "a quoted forbidden support import (transitive=$transitive)" support-import-audit.log audit
        if ! grep -Fq 'ModelSupport cannot depend on decoder, specification, proof, or extracted function module: Zerocopy.Funs' "$backup/support-import-audit.log"; then
            cat "$backup/support-import-audit.log" >&2; exit 1;
        fi
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
if mutation == 'wrong-kind':
    replacement = ('namespace IndependentWitnessControl\n' + command +
        'end IndependentWitnessControl\n'
        'def Zerocopy.Obligations.min_spec_checked : Zerocopy.Obligations.min_spec :=\n'
        '  IndependentWitnessControl.Zerocopy.Obligations.min_spec_checked\n')
elif mutation == 'wrong-type':
    replacement = 'theorem Zerocopy.Obligations.min_spec_checked : True := by trivial\n'
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
    lake build Required > "$backup/witness-build.log" 2>&1 || {
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
    "Missing independent required theorem Zerocopy.Obligations.min_spec_checked"
reject_witness wrong-kind "a definition replacing the independent theorem" \
    "Missing independent required theorem Zerocopy.Obligations.min_spec_checked"
reject_witness wrong-type "an independent theorem with an unrelated type" \
    "Zerocopy.Obligations.min_spec_checked does not prove its independent required proposition"
reject_witness wrong-owner "an independent witness declared in a proof module" \
    "Zerocopy.Obligations.min_spec_checked must be declared in the required checks module"
reject_witness missing-rows "omitted check rows hidden by an empty legacy roster" \
    "Missing independent required theorem Zerocopy.Obligations.min_spec_checked"

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
lake build Required > "$backup/scope-helper-build.log" 2>&1 || {
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
lake build Required > "$backup/empty-scope-build.log" 2>&1 || {
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

# The Rust-derived binding image must equal actual owned specification calls.
# Preserve valid canonical proofs/callers so omitted roots reach the audit.
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
    lake build Required > "$backup/binding-image-build.log" 2>&1 || {
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
    'Compiled inline specification models disagree with bindings: missing .*Zerocopy[.]util[.]min'
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
    lake build Required > "$backup/model-image-build.log" 2>&1 || {
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
        'Raw nominal types disagree with source bindings: missing .*RoundingAlignAndPhase'
fi
if grep -Eq '^(structure|inductive)[[:blank:]]+layout[.]MetadataCastError([[:blank:]]|$)' Zerocopy/Types.lean; then
    reject_model_image missing-default-image "an unannotated carrier omitted from the binding table" \
        'Raw nominal types disagree with source bindings: missing .*MetadataCastError'
fi
reject_model_image moved-shapes "model shapes moved out of their generated module" \
    'Mathematical fields and model must be owned by ModelShapes'
reject_model_image moved-models "decoders and providers moved out of their generated module" \
    'Decoder and provider must be owned by Models'

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
    lake env lean -DwarningAsError=true NegativeControl.lean \
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
            lake env lean -DwarningAsError=true NegativeControl.lean
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
    lake build Required > "$backup/comment-build.log" 2>&1 || {
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
    expect_failure "$description" spec-build.log lake env lean -DwarningAsError=true NegativeControl.lean
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
s = p.read_text()
registration = 'register_spec_step min_spec\n'
if s.count(old) != 1 or s.count(registration) != 1:
    raise SystemExit("Proof declaration-kind control requires the exact unique min theorem/registration")
p.write_text(s.replace(old, 'def min_spec : Zerocopy.Specs.min_spec := by').replace(registration, ''))
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
# The fixed source fixture has no padding callers in the encoding-only stages.
# The final layout proofs explicitly call the canonical padding wrapper. That
# invocation selects the oracle, which rejects malformed or unowned calls.
if grep -Fq 'step with Zerocopy.Proofs.padding_lt_alignment' Proofs.lean; then
    audit > "$backup/dependency-baseline-audit.log" 2>&1 || {
        cat "$backup/dependency-baseline-audit.log" >&2; exit 1;
    }
    python3 - "$backup/padding-callers.json" <<'PYCONTROL'
from pathlib import Path
import json, sys
# This is an oracle for the fixed handwritten Proofs.lean fixture. Raw bodies
# retain explicit canonical callee calls; their same-name canonical wrappers
# must invoke those bodies. Unknown or unowned calls fail closed.
import re
source = Path("Proofs.lean").read_text()
marker = 'step with Zerocopy.Proofs.padding_lt_alignment'
header = re.compile(r'^theorem ([A-Za-z_][A-Za-z0-9_]*) :$')
owner = None
scope = False
callers = set()
seen = set()
for line in source.splitlines():
    if line == 'namespace Zerocopy.Proofs.Raw':
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
            name = match[1]
            if name in seen:
                raise SystemExit("Duplicate raw theorem in dependency fixture")
            seen.add(name)
            owner = name
    if marker in line:
        if (owner is None or not scope or line.count(marker) != 1 or
                re.match(r'^[ \t]+step with Zerocopy[.]Proofs[.]padding_lt_alignment(?:[ \t]|$)', line) is None):
            raise SystemExit("Unowned or malformed padding invocation in dependency fixture")
        callers.add(owner)
if not callers:
    raise SystemExit("Padding dependency control has no source callers")
for name in callers:
    wrapper = re.search(r'(?m)^theorem ' + re.escape(name) + r' : Zerocopy[.]Specs[.]'
        + re.escape(name) + r' := by\n(.*?)(?=^register_spec_step )', source, re.S)
    if wrapper is None or re.search(r'\bRaw[.]' + re.escape(name) + r'\b', wrapper[1]) is None:
        raise SystemExit("Raw padding caller lacks its exact canonical wrapper: " + name)
# Trace the fixed handwritten fixture's declaration references independently
# of the kernel report. Canonical roots stop traversal, just as Check's graph
# records a registered callee separately; Raw helpers remain traversable.
declaration = re.compile(r"^(?:(?:private|noncomputable) +)*(?:theorem|def|abbrev) "
                         r"([A-Za-z_][A-Za-z0-9_']*)\b")
boundary = re.compile(r'^(?:(?:(?:private|noncomputable) +)*(?:theorem|def|abbrev)|'
                      r'namespace|end|attribute|register_spec_step|macro|set_option)\b|^@\[')
nodes = {}
roots = set()
for path in [Path("Proofs.lean"), *sorted(Path("Proofs").rglob("*.lean"))]:
    lines = path.read_text().splitlines()
    scope = None
    index = 0
    while index < len(lines):
        line = lines[index]
        if line.startswith('namespace '):
            scope = line[len('namespace '):]
            index += 1
            continue
        if line.startswith('end '):
            scope = None
            index += 1
            continue
        match = declaration.match(line)
        if match is None:
            index += 1
            continue
        name = match[1]
        stop = index + 1
        while stop < len(lines) and not boundary.match(lines[stop]):
            stop += 1
        if scope not in ('Zerocopy.Proofs', 'Zerocopy.Proofs.Raw'):
            raise SystemExit("Unsupported declaration scope in padding dependency fixture")
        key = scope + '.' + name
        if key in nodes:
            raise SystemExit("Duplicate declaration in padding dependency fixture: " + key)
        nodes[key] = (scope, '\n'.join(lines[index:stop]))
        if line == 'theorem ' + name + ' : Zerocopy.Specs.' + name + ' := by':
            roots.add(key)
        index = stop
references = {}
for node, (scope, text) in nodes.items():
    text = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    used = set()
    for token in re.findall(r"(?<![A-Za-z0-9_'.])[A-Za-z_][A-Za-z0-9_']*"
                            r"(?:[.][A-Za-z_][A-Za-z0-9_']*)*", text):
        if token in nodes:
            used.add(token)
        elif token.startswith('Raw.') and 'Zerocopy.Proofs.' + token in nodes:
            used.add('Zerocopy.Proofs.' + token)
        elif '.' not in token and scope + '.' + token in nodes:
            used.add(scope + '.' + token)
    references[node] = used - {node}
target = 'Zerocopy.Proofs.padding_lt_alignment'
if target not in roots:
    raise SystemExit("Missing canonical padding root in dependency fixture")
dependent_roots = set()
for root in roots - {target}:
    pending = list(references[root])
    visited = set()
    while pending:
        node = pending.pop()
        if node == target:
            dependent_roots.add(root)
            break
        if node in roots or node in visited:
            continue
        visited.add(node)
        pending.extend(references[node])
if not {'Zerocopy.Proofs.' + name for name in callers} <= dependent_roots:
    raise SystemExit("Source dependency closure missed a directly owned padding call")
callers = sorted(dependent_roots)
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
old = 'theorem padding_lt_alignment : Zerocopy.Specs.padding_lt_alignment := by'
matched = [p for p in paths if old in p.read_text()]
if len(matched) != 1:
    raise SystemExit("Callee theorem control no longer matches")
p = matched[0]
s = p.read_text()
registration = 'register_spec_step padding_lt_alignment\n'
if (p != Path("Proofs/Util.lean") or s.count(old) != 1 or s.count(registration) != 1):
    raise SystemExit("Callee control requires the exact unique Util padding theorem/registration")
p.write_text(s.replace(old,
    'theorem unavailable_padding_lt_alignment : Zerocopy.Specs.padding_lt_alignment := by').replace(registration, ''))
PYCONTROL
    lake build +Proofs.Util > "$backup/callee-owner-build.log" 2>&1 || {
        echo "Malformed callee control: renamed owning Util module did not compile" >&2
        cat "$backup/callee-owner-build.log" >&2; exit 1;
    }
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
s = s.replace('step with Zerocopy.Proofs.padding_lt_alignment',
              'step with DependencyControl.padding_proxy')
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
reference = 'Raw.padding_lt_alignment'
if body.count(reference) != 1 or re.search(r'(?<![A-Za-z0-9_.])Raw[.]padding_lt_alignment\b', body) is None:
    raise SystemExit("Independent padding wrapper transport requires its exact unique Raw reference")
body = body.replace(reference, 'Zerocopy.Proofs.Raw.padding_lt_alignment')
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
    lake env lean -DwarningAsError=true WeakOutcome.lean > "$backup/weak-outcome-valid.log" 2>&1 || {
        cat "$backup/weak-outcome-valid.log" >&2; exit 1;
    }
    rm WeakOutcome.lean
    expect_failure "$description" weak-outcome-check.log \
        lake env lean -DwarningAsError=true NegativeControl.lean
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
    expect_failure "a changed mathematical predicate $name" outcome-test.log \
        lake build "+$module"
    if ! grep -Fq "error: $module.lean:" "$backup/outcome-test.log"; then
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
lake build
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
