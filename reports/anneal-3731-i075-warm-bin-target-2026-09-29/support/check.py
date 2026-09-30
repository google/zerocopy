#!/usr/bin/env python3
"""Read-only, relocation-safe check of the retained warm binary-target evidence."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
RESULT = json.loads((HERE / "results.json").read_text())

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

metadata = json.loads((HERE.parent / "REPORT.json").read_text())
tool_pin, probe_pin, result_pin = (subject["identity"] for subject in metadata["subjects"])
assert probe_pin == {"artifact": "support/probe.py", "sha256": sha(HERE / "probe.py")}
assert result_pin == {"artifact": "support/results.json", "sha256": sha(HERE / "results.json")}
for name, info in RESULT["tools"].items():
    assert tool_pin[f"{name}_sha256"] == info["sha256"]

assert RESULT["parent_reference_head"] == "641f55cfd54fcd3c6ba0de67643a62a29df4f3a1"
assert len(RESULT["runs"]) == 2 and RESULT["work_removed"]
assert RESULT["owned_scratch_bytes_before_cleanup"] < 100 * 1024**2
assert {k: sha(HERE / "fixture" / k) for k in RESULT["fixture"]} == RESULT["fixture"]
# Recorded external tool paths/hashes are provenance; this checker only reads package files.
base, repeat = RESULT["runs"]
assert [x["label"] for x in RESULT["runs"]] == ["baseline", "warm_repeat"]
assert base["environment"]["CARGO_TARGET_DIR"] == repeat["environment"]["CARGO_TARGET_DIR"]
assert base["cwd"] == repeat["cwd"]
assert base["argv"][:4] == repeat["argv"][:4]
assert base["argv"][6:] == repeat["argv"][6:]
assert base["dest_path"] != repeat["dest_path"]
assert all(x["environment"]["CARGO_INCREMENTAL"] == "0" and
           x["environment"]["CARGO_NET_OFFLINE"] == "true" and
           x["environment"]["CARGO_BUILD_JOBS"] == "1" and
           x["environment"]["RAYON_NUM_THREADS"] == "1" and
           x["environment"]["RUSTFLAGS"] is None for x in RESULT["runs"])

for x, expected_crate in ((base, "subject_matrix_cli"), (repeat, "subject_matrix_cli")):
    label = x["label"]
    assert x["exit_code"] == 0 and x["guard_stop"] is None and x["dest_exists"]
    assert x["elapsed_seconds"] < 60
    assert x["argv"][4:6] == ["--dest-file", x["dest_path"]]
    assert x["argv"][-9:] == ["--manifest-path", str(Path(x["cwd"]) / "Cargo.toml"),
                               "--bin", "subject_matrix_cli", "--offline", "--locked", "-j", "1", "-v"]
    assert x["dest_path"].endswith("/i075-warm-bin-target/" + label + ".llbc")
    for stream in ("stdout", "stderr"):
        assert sha(HERE / "raw" / f"{label}.{stream}") == x[f"{stream}_sha256"]
    stderr = (HERE / "raw" / f"{label}.stderr").read_text()
    driver_crates = re.findall(r"charon-driver rustc --crate-name ([^\s]+)", stderr)
    assert driver_crates == x["driver_crates"] and set(driver_crates) == \
           {"subject_matrix", "subject_matrix_cli"}
    assert "Compiling subject_matrix" in stderr and "Finished `dev` profile" in stderr
    artifact = HERE / "artifacts" / f"{label}.llbc"
    assert sha(artifact) == x["dest_sha256"]
    parsed = json.loads(artifact.read_text())
    assert parsed["charon_version"] == "0.1.210"
    assert parsed["translated"]["crate_name"] == expected_crate == x["crate_name"]
    assert parsed["has_errors"] is False and x["has_errors"] is False
    for sample in [x["preflight"], *x["samples"]]:
        assert sample["memory_estimate_percent"] >= 20
        assert sample["free_disk_bytes"] >= 10 * 1024**3
        assert sample["owned_scratch_bytes"] <= 100 * 1024**2
        assert sample.get("rss_kib", 0) <= 1024 * 1024
        assert sample.get("seconds", 0) <= 60
assert base["driver_crates"] == ["subject_matrix", "subject_matrix_cli"]
assert repeat["driver_crates"] == ["subject_matrix", "subject_matrix_cli"]
warm_stderr = (HERE / "raw" / "warm_repeat.stderr").read_text()
assert re.search(r"Dirty subject_matrix .*couldn't read metadata for file `[^`]+/libsubject_matrix-[^`]+\.rlib`", warm_stderr)
assert "Fresh subject_matrix" not in warm_stderr
print("PASS: warm --bin subject_matrix_cli re-invoked two units and produced the requested binary")
