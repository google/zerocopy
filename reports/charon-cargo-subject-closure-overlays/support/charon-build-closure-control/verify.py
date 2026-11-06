#!/usr/bin/env python3
"""Verify retained Charon artifacts without rerunning the toolchain."""
import json
from pathlib import Path
from probe import ART, OUT, sha, projection

result = json.loads(OUT.read_text())
assert len(result["cases"]) == 10
for case in result["cases"]:
    llbc = ART / (case["label"] + ".llbc")
    assert llbc.exists()
    assert sha(llbc) == case["llbc_sha256"] == result["artifact_sha256"][llbc.name]
    assert projection(llbc) == case["projection"]
    assert case["exit"] == 0
assert result["wrong_unit_rejection"] == "wrong compilation unit: expected app_closure, got app_closure_cli"
assert result["cases"][0]["projection"]["crate_name"] == "app_closure"
assert result["cases"][9]["projection"]["crate_name"] == "app_closure_cli"
assert result["cases"][0]["source_sha256"]["dep_path/src/lib.rs"] != result["cases"][5]["source_sha256"]["dep_path/src/lib.rs"]
assert result["const_body_differs"]["build-env"] and result["const_body_differs"]["build-source"]
assert result["macro_body_differs"]["proc-env"]
assert result["root_body_differs"]["include-str"] and result["root_body_differs"]["rustc-env"]
assert "core::num::wrapping_mul" in result["cases"][6]["projection"]["function_names"]
print("verified 10 retained cases, hashes, projections, closure changes, and wrong-unit rejection")
