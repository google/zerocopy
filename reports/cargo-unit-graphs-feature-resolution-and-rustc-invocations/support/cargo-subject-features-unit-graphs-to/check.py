#!/usr/bin/env python3
"""Check retained offline Cargo evidence without launching Cargo or needing toolchains."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
R = json.loads((ROOT / "results.json").read_text())
RAW = ROOT / "raw"
LABELS = ("metadata-default", "metadata-feature", "metadata-filter-host", "metadata-filter-windows",
          "unit-build", "unit-feature", "unit-release", "unit-test", "unit-target",
          "build-cold", "build-warm", "build-feature", "test-no-run")
VERSIONS = ("pinned", "stable", "newer")
EXPECTED_TOOLS = {
    "pinned": {
        "cargo_sha256": "71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1",
        "rustc_sha256": "2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc",
        "cargo_commit": "fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef",
        "rustc_commit": "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1",
    },
    "stable": {
        "cargo_sha256": "778478868dbfe74960e49329bb5813d2f5ba95c8bfb1f37cd626c62cb26a214a",
        "rustc_sha256": "2814fb55fb9cfb3eef5848a8104d77e3de7fd95394661144a12ee90cd4405340",
        "cargo_commit": "797e8a9bca276c1c9f9f738d2a20f484fa4eea9d",
        "rustc_commit": "48a229ceaefd4985c50990b14116b6d856af0985",
    },
    "newer": {
        "cargo_sha256": "a59fccc480f931538408a17c2c2daae588da33d5196a38c526761db36a18ec66",
        "rustc_sha256": "29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d",
        "cargo_commit": "3d7cf6e937d6127d0f49881bf689c560b36d35c4",
        "rustc_commit": "5c543b0b8c73c7b72bc8284ced4fb22ead15734d",
    },
}

def sha(data): return hashlib.sha256(data).hexdigest()
def cell(v, label): return next(c for c in R["cells"] if c["version"] == v and c["label"] == label)
def raw(v, label, stream): return (RAW / f"{v}--{label}.{stream}").read_bytes()
def obj(v, label): return json.loads(raw(v, label, "stdout"))
def units(v, label): return obj(v, label)["units"]
def named_unit(v, label, package, target, mode="build", features=None):
    found = [u for u in units(v, label) if package in u["pkg_id"] and u["target"]["name"] == target
             and u["mode"] == mode and (features is None or u["features"] == features)]
    assert len(found) == 1, (v, label, package, target, mode, features, len(found))
    return found[0]

assert len(R["cells"]) == 39
assert {(c["version"], c["label"]) for c in R["cells"]} == {(v, l) for v in VERSIONS for l in LABELS}
for name, digest in R["fixture_sha256"].items():
    assert sha((ROOT / "fixture" / name).read_bytes()) == digest, name
assert sha((ROOT / "fixture" / "Cargo.lock").read_bytes()) == R["lock_sha256"]
for c in R["cells"]:
    for stream in ("stdout", "stderr"):
        b = raw(c["version"], c["label"], stream)
        assert sha(b) == c[stream + "_sha256"] and len(b) == c[stream + "_bytes"]
    a = c["admission"]
    assert a["reclaimable_percent"] > 20 and a["disk_free_bytes"] > 1_073_741_824
    assert a["scratch_bytes"] < 100_000_000 and not c["timed_out"]
    expect = 101 if c["version"] == "stable" and c["label"].startswith("unit-") else 0
    assert c["exit_code"] == expect, (c["version"], c["label"], c["exit_code"])
for v, t in R["tools"].items():
    assert "cargo_version" in t and "rustc_version" in t
    expected = EXPECTED_TOOLS[v]
    assert t["cargo_sha256"] == expected["cargo_sha256"]
    assert t["rustc_sha256"] == expected["rustc_sha256"]
    assert expected["cargo_commit"] in t["cargo_version"]
    assert expected["rustc_commit"] in t["rustc_version"]

# R348: observable subject projection distinguishes context, profile, mode, platform.
for v in ("pinned", "newer"):
    build = obj(v, "unit-build")
    assert len(build["units"]) == 6 and len(build["roots"]) == 2
    named_unit(v, "unit-build", "probe-dep", "probe_dep", features=["host"])
    named_unit(v, "unit-build", "probe-dep", "probe_dep", features=["normal"])
    named_unit(v, "unit-build", "probe-app", "build-script-build", mode="run-custom-build")
    assert all(u["profile"]["name"] == "release" for u in units(v, "unit-release"))
    assert any(u["profile"]["name"] == "dev" for u in units(v, "unit-build"))
    named_unit(v, "unit-test", "probe-app", "probe_app", mode="test")
    named_unit(v, "unit-test", "probe-app", "probe_app", mode="build")
    target = named_unit(v, "unit-target", "probe-app", "probe_app")
    assert target["platform"] == "aarch64-apple-darwin"
    assert named_unit(v, "unit-target", "probe-dep", "probe_dep", features=["host"])["platform"] is None
    assert named_unit(v, "unit-target", "probe-dep", "probe_dep", features=["normal"])["platform"] == "aarch64-apple-darwin"
    assert "trim_paths" not in units("pinned", "unit-build")[0]["profile"]
    assert all(u["profile"]["trim_paths"] == "none" for u in units("newer", "unit-build"))
for label in LABELS:
    if label.startswith("unit-"):
        assert b"only accepted on the nightly channel" in raw("stable", label, "stderr")

# R349: metadata has one feature list per package; unit graph retains two contexts.
for v in VERSIONS:
    for label in ("metadata-default", "metadata-feature", "metadata-filter-host", "metadata-filter-windows"):
        meta = obj(v, label)
        assert meta["version"] == 1
        dep = next(n for n in meta["resolve"]["nodes"] if "probe-dep" in n["id"])
        assert dep["features"] == ["dev", "host", "normal", "targeted"]
    assert any("probe-opt" in n["id"] for n in obj(v, "metadata-feature")["resolve"]["nodes"])
for v in ("pinned", "newer"):
    assert len(units(v, "unit-feature")) == 7
    assert any("probe-opt" in u["pkg_id"] for u in units(v, "unit-feature"))
    named_unit(v, "unit-test", "probe-dep", "probe_dep", features=["dev", "normal"])
    named_unit(v, "unit-test", "probe-dep", "probe_dep", features=["host"])
for label in ("metadata-default", "metadata-feature", "metadata-filter-host", "metadata-filter-windows"):
    norm = []
    for v in VERSIONS:
        j = obj(v, label)
        j.pop("target_directory"); j.pop("build_directory")
        norm.append(j)
    assert norm[0] == norm[1] == norm[2], label

# R352: planned graph versus executed commands; stable/newer output kept separate.
for v in VERSIONS:
    cold = raw(v, "build-cold", "stderr").decode()
    warm = raw(v, "build-warm", "stderr").decode()
    running = [line for line in cold.splitlines() if " Running `" in line]
    assert len(running) == 6 and sum(" --crate-name " in x for x in running) == 5
    assert sum(" --crate-name " not in x for x in running) == 1
    assert any("CARGO_CRATE_NAME=build_script_build" in x for x in running)
    assert any("PROBE_BUILD_TAG=host" in x and "--extern probe_dep=" in x for x in running)
    assert not any(" Running `" in line for line in warm.splitlines())
    assert "Fresh probe-dep" in warm and "Fresh probe-app" in warm
    assert "--extern probe_dep=" in cold
assert "-Z embed-metadata=no" in raw("newer", "build-cold", "stderr").decode()
assert "-Z embed-metadata=no" not in raw("pinned", "build-cold", "stderr").decode()
assert "unused-externs-silent" in raw("newer", "build-cold", "stderr").decode()
for v in ("pinned", "newer"):
    assert len(units(v, "unit-build")) == 6
    assert any(u["mode"] == "run-custom-build" for u in units(v, "unit-build"))
for label in ("unit-build", "unit-feature", "unit-release", "unit-test", "unit-target"):
    a, b = obj("pinned", label), obj("newer", label)
    for u in b["units"]: assert u["profile"].pop("trim_paths") == "none"
    assert a == b, label

print("PASS: 39 raw cells, resource bounds, R348 subject projection, R349 metadata/contexts, R352 plan/invocations")
