"""Regenerate two PR94 audit inputs; no compiler/build or exporter-main execution.

Python 3.10+. Arguments: pinned source checkout/export, NEW output directory.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("source", type=Path)
parser.add_argument("output", type=Path)
args = parser.parse_args()
capture = args.source.resolve() / "experiments/opsem/cargo-workspace-capture"
output = args.output.resolve()
if output.exists():
    raise SystemExit("Output must be a new directory; preserve any prior result")

spec = importlib.util.spec_from_file_location("extractor94", capture / "extract_and_link_charon_h3.py")
extractor = importlib.util.module_from_spec(spec)
spec.loader.exec_module(extractor)
document = json.loads((capture / "artifacts/client_direct_mir_inspector_strongest.ullbc").read_text(encoding="utf-8"))
extractor.validate_h3_native_inspector_adapter_domain(document)

def encode(doc):
    return extractor.build_amir_v3_package(
        "client_direct_mir_inspector", 3, 11,
        extractor.translate_h3_native_client_inspector_closure_ullbc(doc),
    )

baseline = encode(document)
retained = (capture / "artifacts/charon_h3_native_client_inspector_closure.amir").read_bytes()
if baseline != retained:
    raise SystemExit("Baseline differs from retained PR94 artifact; no output written")
mutant = copy.deepcopy(document)
local = mutant["translated"]["fun_decls"][4]["body"]["Unstructured"]["locals"]["locals"][2]
old_type = copy.deepcopy(local["ty"])
local["ty"] = {"HashConsedValue": [990002, {"Literal": {"UInt": "U64"}}]}
changed = encode(mutant)
try:
    extractor.validate_h3_native_inspector_adapter_domain(mutant)
except ValueError as error:
    strict = {"rejected": True, "reason": str(error)}
else:
    strict = {"rejected": False}

audit_source = '''import AnnealResearch.PR92AuditCounterexamples

set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 1600000

namespace Audit94
open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.OpenHashMultiCrateR5R6R9R10
open AnnealResearch.CharonNativeAndControlsR3R4

def mismatchedHeaderQ4 : PostRunEndorsedArtifactRecord :=
  { r6EndorsedClientAppRecord with packageBytes :=
      r5ClientAppOpenHashBytes.take 7 ++ [0, 0] ++ r5ClientAppOpenHashBytes.drop 9 }

theorem endorsement_still_accepts_inconsistent_header_fingerprint :
    mismatchedHeaderQ4.packageBytes.getD 7 0 = 0 ∧
    mismatchedHeaderQ4.packageBytes.getD 8 0 = 0 ∧
    mismatchedHeaderQ4.expectedFp16 = (45, 98) ∧
    verifyPostRunEndorsedArtifactBoundQ4 mismatchedHeaderQ4 = true := by decide

def uncheckedLocalMutantBytes : List Nat := MUTANT_BYTES

theorem charon_gate_accepts_unchecked_local_type_change :
    uncheckedLocalMutantBytes ≠ charonNativeClientInspectorClosureAmirBytes ∧
    isAdmittedPackageBytes uncheckedLocalMutantBytes = true ∧
    verifyCharonNativeInspectorClosureQ6 uncheckedLocalMutantBytes = true := by decide

#print axioms endorsement_still_accepts_inconsistent_header_fingerprint
#print axioms charon_gate_accepts_unchecked_local_type_change
end Audit94
'''.replace("MUTANT_BYTES", str(list(changed)))

result = {
    "source_commit": "35bd34bf1fcd1fd77a3b996d7dbf3773d6aa6318",
    "qualification": "Supplied ULLBC AST mutation, not a new compiled Rust program",
    "function_index": 4, "local_index": 2, "previous_type": old_type,
    "new_type": local["ty"], "baseline_matches_retained": baseline == retained,
    "baseline_length": len(baseline), "mutant_length": len(changed),
    "baseline_sha256": hashlib.sha256(baseline).hexdigest(),
    "mutant_sha256": hashlib.sha256(changed).hexdigest(),
    "export_changed": baseline != changed, "optional_strict_validator": strict,
    "audit_source_sha256": hashlib.sha256(audit_source.encode()).hexdigest(),
}
expected = (
    "fafd26afcc9a0f1d7e87a85846cda92edc97d690ee472932d6a49595a43b2c77",
    "5342601cf574a1aa4dbc93ed73857f63de8d54e9f6ef125506222e2b0922e66a",
    "7339cf960c2e3f25ea2925ff8749a9a8874990ad0652cd1ceefdf02167bae0da",
)
actual = (result["baseline_sha256"], result["mutant_sha256"], result["audit_source_sha256"])
if actual != expected or len(changed) != 1019 or not strict["rejected"]:
    raise SystemExit("PR94 replay differs from recorded subject; no output written")
output.mkdir(parents=True, exist_ok=False)
(output / "Audit94.lean").write_bytes(audit_source.encode("utf-8"))
(output / "unchecked-local-mutant.amir").write_bytes(changed)
(output / "translator-probe.json").write_bytes((json.dumps(result, indent=2) + "\n").encode("utf-8"))
print(json.dumps(result, indent=2))
