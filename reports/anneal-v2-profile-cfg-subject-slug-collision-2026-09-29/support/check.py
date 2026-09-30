#!/usr/bin/env python3
"""Read-only check of the retained profile/cfg slug and LLBC contrast."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PACKAGE = "anneal-v2-profile-cfg-subject-slug-collision-2026-09-29"
META = json.loads((HERE.parent / "REPORT.json").read_text())
DATA = json.loads((HERE / "results.json").read_text())

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def scalars(node):
    if isinstance(node, dict):
        if "Unsigned" in node and node["Unsigned"][0] == "U32":
            yield node["Unsigned"][1]
        for value in node.values():
            yield from scalars(value)
    elif isinstance(node, list):
        for value in node:
            yield from scalars(value)

def project(path):
    d = json.loads(path.read_text())
    t = d["translated"]
    bodies = {}
    for decl in t["fun_decls"]:
        if decl["item_meta"]["is_local"]:
            name = "::".join(part["Ident"][0] for part in decl["item_meta"]["name"]
                             if "Ident" in part)
            body = json.dumps(decl["body"], sort_keys=True, separators=(",", ":")).encode()
            bodies[name] = {"sha256": hashlib.sha256(body).hexdigest(),
                            "u32_literals": list(scalars(decl["body"]))}
    files = [{"name": row["name"], "contents_sha256": hashlib.sha256(
        row["contents"].encode()).hexdigest()} for row in t["files"]]
    return {"sha256": sha(path), "bytes": path.stat().st_size,
            "crate_name": t["crate_name"], "has_errors": d["has_errors"],
            "local_bodies": bodies, "files": files}

def diff(a, b, path="$ "):
    path = path.rstrip()
    if type(a) != type(b):
        return {path: [a, b]}
    if isinstance(a, dict):
        out = {}
        for key in sorted(set(a) | set(b)):
            next_path = path + "." + key
            if key not in a:
                out[next_path] = [None, b[key]]
            elif key not in b:
                out[next_path] = [a[key], None]
            else:
                out.update(diff(a[key], b[key], next_path))
        return out
    if isinstance(a, list):
        if len(a) != len(b):
            return {path + ".length": [len(a), len(b)]}
        out = {}
        for i, (left, right) in enumerate(zip(a, b)):
            out.update(diff(left, right, f"{path}[{i}]"))
        return out
    return {} if a == b else {path: [a, b]}

subject = DATA["source_identity"]
assert sha(HERE / "probe.py") == META["subjects"][2]["identity"]["probe_sha256"]
assert sha(HERE / "fixture/src/lib.rs") == subject["fixture_source_sha256"] == META["subjects"][2]["identity"]["fixture_source_sha256"]
for file, key in (("fixture/Cargo.toml", "fixture_manifest_sha256"),
                  ("fixture/Cargo.lock", "fixture_lock_sha256"),
                  ("harness/src/main.rs", "harness_main_sha256"),
                  ("harness/Cargo.toml", "harness_manifest_sha256"),
                  ("harness/Cargo.lock", "harness_lock_sha256")):
    assert sha(HERE / file) == subject[key]
assert sha(HERE / "harness/src/scanner.rs") == subject["scanner_sha256"] == META["subjects"][0]["identity"]["scanner_sha256"]
assert subject["reference_commit"] == META["subjects"][0]["identity"]["source_commit"]
assert subject["tool_sha256"] == {
    "charon": META["subjects"][1]["identity"]["charon_sha256"],
    "cargo": META["subjects"][1]["identity"]["cargo_sha256"],
    "rustc": META["subjects"][1]["identity"]["rustc_sha256"]}
fixture_path = Path(subject["fixture_manifest_path"])
assert fixture_path.is_absolute()
assert fixture_path.parts[-5:] == ("reports", PACKAGE, "support", "fixture", "Cargo.toml")
assert "#[cfg(debug_assertions)]" in (HERE / "fixture/src/lib.rs").read_text()
assert "#[cfg(probe_alt)]" in (HERE / "fixture/src/lib.rs").read_text()

assert DATA["limits"] == {"minimum_estimated_reclaimable_percent": 20.0,
                          "minimum_free_disk_bytes": 10 * 1024**3,
                          "maximum_group_rss_kib": 1024 * 1024,
                          "per_command_timeout_seconds": 60}

def check_headroom(h):
    assert h["vm_page_size"] == 16384
    assert set(h["vm_pages"]) == {"free", "inactive", "speculative"}
    estimate = round(100 * h["vm_page_size"] * sum(h["vm_pages"].values()) /
                     h["physical_memory_bytes"], 3)
    assert estimate == h["estimated_reclaimable_percent"] >= 20.0
    assert h["free_disk_bytes"] >= 10 * 1024**3

check_headroom(DATA["preflight"])
assert list(DATA["commands"]) == ["harness_build", "slug", "debug", "release", "cfg_alt"]
command_hashes = {label: hashlib.sha256(json.dumps(
    {key: c[key] for key in ("argv", "cwd", "environment")},
    sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    for label, c in DATA["commands"].items()}
assert command_hashes == json.loads((HERE / "command-hashes.json").read_text())
for label, c in DATA["commands"].items():
    assert c["label"] == label and c["exit"] == 0 and c["guard_reason"] is None
    assert 0 < c["elapsed_seconds"] < 60 and c["target_allocated_kib"] > 0
    check_headroom(c["preflight"])
    assert c["samples"]
    for s in c["samples"]:
        check_headroom(s)
        assert s["group_rss_kib"] <= 1024 * 1024
        assert s["elapsed_seconds"] < 60
    assert sha(HERE / "raw" / f"{label}.stdout") == c["stdout_sha256"]
    assert sha(HERE / "raw" / f"{label}.stderr") == c["stderr_sha256"]
    env = c["environment"]
    assert env["CARGO_INCREMENTAL"] == "0" and env["CARGO_BUILD_JOBS"] == "1"
    assert env["CARGO_NET_OFFLINE"] == "true" and env["RAYON_NUM_THREADS"] == "1"
    assert env["CARGO_PROFILE_DEV_DEBUG_ASSERTIONS"] == "true"
    assert env["CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS"] == "false"
    assert Path(env["CARGO_TARGET_DIR"]).name == ("harness-target" if label in
        ("harness_build", "slug") else "target-" + label)

slug_rows = [line.split("\t") for line in (HERE / "raw/slug.stdout").read_text().splitlines()]
assert slug_rows == DATA["slug_rows"]
assert [row[0] for row in slug_rows] == ["debug", "release", "cfg_alt"]
assert slug_rows[0][1:] == slug_rows[1][1:] == slug_rows[2][1:]
assert slug_rows[0][2] == slug_rows[0][1] + ".llbc"
assert DATA["commands"]["harness_build"]["argv"][-4:] == ["--offline", "--locked", "-j", "1"]
assert DATA["commands"]["slug"]["argv"][-1] == str(fixture_path)
assert "Finished `dev` profile" in (HERE / "raw/harness_build.stderr").read_text()

raw_llbc = {}
for label in ("debug", "release", "cfg_alt"):
    c = DATA["commands"][label]
    cmd = c["argv"]
    assert cmd[0].endswith("/.anneal-local-tools/bin/charon")
    assert cmd[1:4] == ["cargo", "--preset", "aeneas"]
    assert cmd[cmd.index("--manifest-path") + 1] == str(fixture_path)
    assert cmd[-3:] == ["--offline", "--locked", "-v"]
    assert ("--release" in cmd) == (label == "release")
    assert c["environment"]["RUSTFLAGS"] == ("--cfg probe_alt" if label == "cfg_alt" else None)
    recorded_dest = Path(cmd[cmd.index("--dest-file") + 1])
    assert recorded_dest.is_absolute()
    assert recorded_dest.parts[-4:] == (PACKAGE, "support", "artifacts", f"{label}.llbc")
    dest = HERE / "artifacts" / f"{label}.llbc"
    assert project(dest) == DATA["artifacts"][label]
    assert DATA["artifacts"][label]["crate_name"] == "unit_key_probe"
    assert DATA["artifacts"][label]["has_errors"] is False
    assert DATA["artifacts"][label]["files"] == [{"name": {"Local": "src/lib.rs"},
        "contents_sha256": subject["fixture_source_sha256"]}]
    stderr = (HERE / "raw" / f"{label}.stderr").read_text()
    assert "charon-driver rustc --crate-name unit_key_probe" in stderr
    assert ("-C opt-level=3" in stderr) == (label == "release")
    assert ("--cfg probe_alt" in stderr) == (label == "cfg_alt")
    raw_llbc[label] = json.loads(dest.read_text())

maps = {label: DATA["artifacts"][label]["local_bodies"] for label in raw_llbc}
names = {"unit_key_probe::profile_value", "unit_key_probe::config_value"}
assert all(set(m) == names for m in maps.values())
assert [maps[x]["unit_key_probe::profile_value"]["u32_literals"] for x in
        ("debug", "release", "cfg_alt")] == [["7"], ["11"], ["7"]]
assert [maps[x]["unit_key_probe::config_value"]["u32_literals"] for x in
        ("debug", "release", "cfg_alt")] == [["23"], ["23"], ["29"]]
assert maps["debug"]["unit_key_probe::profile_value"]["sha256"] != maps["release"]["unit_key_probe::profile_value"]["sha256"]
assert maps["debug"]["unit_key_probe::config_value"]["sha256"] == maps["release"]["unit_key_probe::config_value"]["sha256"]
assert maps["debug"]["unit_key_probe::profile_value"]["sha256"] == maps["cfg_alt"]["unit_key_probe::profile_value"]["sha256"]
assert maps["debug"]["unit_key_probe::config_value"]["sha256"] != maps["cfg_alt"]["unit_key_probe::config_value"]["sha256"]
diffs = {f"debug_vs_{label}": diff(raw_llbc["debug"], raw_llbc[label])
         for label in ("release", "cfg_alt")}
assert diffs == json.loads((HERE / "llbc-diffs.json").read_text())
assert len(diffs["debug_vs_release"]) == 25 and len(diffs["debug_vs_cfg_alt"]) == 19
assert set((HERE / "artifacts").glob("*.llbc")) == {
    HERE / "artifacts" / f"{name}.llbc" for name in raw_llbc}
assert DATA["cleanup"]["work_exists_after_removal"] is False
check_headroom(DATA["cleanup"]["postrun_headroom"])
print("PASS: three profile/cfg LLBCs, one checked-in V2 slug, raw diffs, guards and cleanup")
