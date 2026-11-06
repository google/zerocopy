#!/usr/bin/env python3
"""Offline raw-backed checker for valid/malformed/restored Lake manifest probe."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
r = json.loads((ROOT / "results.json").read_text())


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def require(ok, name):
    if not ok: raise AssertionError(name)


def frames(raw):
    out = []; rest = raw
    while rest:
        require(b"\r\n\r\n" in rest, "incomplete frame header")
        h, body = rest.split(b"\r\n\r\n", 1)
        match = re.search(rb"Content-Length:\s*(\d+)", h, re.I)
        require(match is not None, "frame Content-Length")
        n = int(match.group(1))
        require(len(body) >= n, "incomplete frame body")
        out.append(json.loads(body[:n])); rest = body[n:]
    return out


expected = ["seed-build"] + [f"{p}-{action}" for p in ("valid", "malformed", "restored")
                              for action in ("setup", "batch", "server")]
expected.insert(expected.index("restored-setup"), "malformed-direct-lean")
require(r["status"] == "completed" and [x["label"] for x in r["runs"]] == expected, "run order")
require((r["lake_sha256"],r["lean_sha256"]) == (
    "9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb",
    "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"), "binary hashes")
require(r["admission"]["memory"]["fraction"] > .30 and r["admission"]["disk_free"] > 10*1024**3, "admission")
good = ROOT / "fixtures/valid-lake-manifest.json"
bad = ROOT / "fixtures/malformed-lake-manifest.json"
require(bad.read_bytes() == b"{\n" and good.read_bytes().startswith(b"{\n"), "fixture bytes")
require(sha(good) == "4cf0c1b12e990e08af5075710832c08e1df761220ab141edb2da7211cb2fd230", "fixed valid-manifest hash")
require(sha(good) == r["fixture_sha256"]["valid_manifest"] and
        sha(bad) == r["fixture_sha256"]["malformed_manifest"], "fixture manifest hashes")
require((ROOT/"preliminary/results.json").is_file(), "preliminary acquisition retained")
valid_manifest = json.loads(good.read_text())
require(valid_manifest["name"] == "consumer" and len(valid_manifest["packages"]) == 1 and
        valid_manifest["packages"][0]["type"] == "path" and
        valid_manifest["packages"][0]["name"] == "probe_dep" and
        valid_manifest["packages"][0]["dir"] == "../producer", "one local path dependency")
require((ROOT/"work/producer/Dep.lean").read_bytes() == b"def depValue : Nat := 7\n" and
        (ROOT/"work/consumer/Generated.lean").read_bytes() ==
        b"import Dep\ntheorem generatedEq : depValue = 7 := by rfl\n#eval depValue\n", "exact source bytes")
require(sha(ROOT/"work/producer/Dep.lean") == "15bbf60d162408dade43c6e618dd0d09b28c8fdeb7528c80e40329908f12b7a2" and
        sha(ROOT/"work/consumer/Generated.lean") == "086270efb5c0dc2ec7d11571e0fa6499c90f8132dda90119258e77947f58e702", "fixed source hashes")
prelim = json.loads((ROOT/"preliminary/results.json").read_text())
require(prelim["runs"][0]["env_overrides"]["LEAN_PATH"] is not None and
        all(x["env_overrides"]["LEAN_PATH"] is not None for x in prelim["runs"] if x["argv"][0].endswith("/bin/lake")),
        "preliminary LEAN_PATH confound")

by = {x["label"]:x for x in r["runs"]}
for x in r["runs"]:
    label = x["label"]
    require(x["abort"] is None and x["elapsed"] < 30 and x["resource_samples"], f"guard: {label}")
    for s in x["resource_samples"]:
        require(s["reclaimable"] >= .20 and s["disk_free"] >= 10*1024**3 and
                s["scratch_bytes"] <= 100*1024**2 and s["group_rss_kib"] <= 1200*1024,
                f"resources: {label}")
    require(x["env_overrides"]["LAKE_NO_NET"] == "1", f"offline: {label}")
    require(x["before"]["consumer/Generated.lean"]["sha256"] == r["fixture_sha256"]["consumer_source"] and
            x["before"]["producer/Dep.lean"]["sha256"] == r["fixture_sha256"]["producer_source"], f"source bytes: {label}")
    for stream in ("stdout", "stderr"):
        require(sha(ROOT/"raw"/f"{label}.{stream}") == x[f"{stream}_sha256"], f"raw: {label}/{stream}")
    if label != "seed-build":
        require(x["env_overrides"]["LAKE_NO_CACHE"] == "1" and
                x["env_overrides"]["LAKE_ARTIFACT_CACHE"] == "false", f"cache disabled: {label}")
        require(x["before"] == x["after"], f"no net local writes: {label}")
    if label != "malformed-direct-lean":
        require(x["env_overrides"]["LEAN_PATH"] is None and x["argv"][0].endswith("/bin/lake"),
                f"Lake env/argv: {label}")
    else:
        require(x["env_overrides"]["LEAN_PATH"].endswith("/producer/.lake/build/lib/lean") and
                x["argv"][-2:] == ["--json","Generated.lean"], "direct Lean control env/argv")

for left,right in zip(r["runs"],r["runs"][1:]):
    a,b = left["after"],right["before"]
    require(a.keys() == b.keys(), f"adjacent file set: {left['label']} to {right['label']}")
    changed = {k for k in a if a[k] != b[k]}
    expected_change = {"consumer/lake-manifest.json"} if (left["label"],right["label"]) in (
        ("valid-server","malformed-setup"),("malformed-direct-lean","restored-setup")) else set()
    require(changed == expected_change, f"only manifest edit: {left['label']} to {right['label']}")

require(by["seed-build"]["exit"] == 0 and len(r["seed_cache"]) > 0, "cache seed")
require(by["seed-build"]["argv"][1:] == ["--keep-toolchain","--no-ansi","build","Generated"] and
        by["seed-build"]["env_overrides"]["LAKE_ARTIFACT_CACHE"] == "true" and
        by["seed-build"]["env_overrides"]["LAKE_NO_CACHE"] == "0" and
        by["seed-build"]["env_overrides"]["LAKE_CACHE_DIR"].endswith("/work/cache"), "seed argv/cache env")
for phase in ("valid","malformed","restored"):
    manifest = bad if phase == "malformed" else good
    state = r["phases"][phase]
    require(state["manifest_sha256"] == sha(manifest), f"phase manifest: {phase}")
    require(state["producer_before"] == state["producer_after"] and
            state["cache_before"] == state["cache_after"] == r["seed_cache"],
            f"producer/cache net inventory: {phase}")
    for action in ("setup","batch","server"):
        x = by[f"{phase}-{action}"]
        require(x["cwd"].endswith("/work/consumer") and x["argv"][1:3] == ["--keep-toolchain","--no-ansi"],
                f"cwd/base argv: {phase}-{action}")
        require(x["argv"][3:5] == ["--no-build","--no-cache"], f"no-build/no-cache: {phase}-{action}")
        if action == "setup":
            require(x["argv"][5] == "setup-file" and x["argv"][6].endswith("/consumer/Generated.lean"), "setup argv")
        elif action == "batch":
            require(x["argv"][5:] == ["env","lean","--json","Generated.lean"], "batch argv")
        else:
            require(x["argv"][5] == "serve", "server argv")

for phase in ("valid","restored"):
    setup = by[f"{phase}-setup"]
    batch = by[f"{phase}-batch"]
    srv = by[f"{phase}-server"]
    require((setup["exit"],batch["exit"],srv["exit"]) == (0,0,0), f"valid exits: {phase}")
    parsed_setup = json.loads((ROOT/"raw"/f"{phase}-setup.stdout").read_text())
    require(parsed_setup["name"] == "Generated" and parsed_setup["package"] == "consumer" and
            parsed_setup["importArts"]["Dep"][0].endswith("/producer/.lake/build/lib/lean/Dep.olean"),
            f"setup content: {phase}")
    messages = [json.loads(z) for z in (ROOT/"raw"/f"{phase}-batch.stdout").read_text().splitlines()]
    require(len(messages) == 1 and messages[0]["data"] == "7", f"batch: {phase}")

for phase in ("valid","malformed","restored"):
    x = by[f"{phase}-server"]
    raw_msgs = frames((ROOT/"raw"/f"{phase}-server.stdout").read_bytes())
    require(raw_msgs == x["decoded_messages"], f"raw frames: {phase}")
    require((x["exit"],x["client_errors"]) == (0,[]), f"server exit: {phase}")
    require([m["method"] for m in x["sent_messages"]] == ["initialize","initialized","shutdown","exit"],
            f"client transcript: {phase}")
    require(x["sent_messages"][0]["id"] == 1 and x["sent_messages"][0]["params"]["rootUri"] ==
            Path(x["cwd"]).as_uri() and x["sent_messages"][2]["id"] == 2,
            f"initialize/shutdown id and root URI: {phase}")
    require(any(m.get("id") == 1 and "result" in m for m in raw_msgs) and
            any(m.get("id") == 2 and "result" in m for m in raw_msgs), f"server replies: {phase}")
    require(x["initialize_result"] in raw_msgs, f"stored init: {phase}")

for action in ("setup","batch"):
    x = by[f"malformed-{action}"]
    require(x["exit"] == 1 and (ROOT/"raw"/f"malformed-{action}.stdout").read_bytes() == b"",
            f"malformed failure: {action}")
    err = (ROOT/"raw"/f"malformed-{action}.stderr").read_text()
    require("lake-manifest.json: invalid JSON: offset 2: unexpected end of input" in err,
            f"malformed diagnostic: {action}")
warning = (ROOT/"raw/malformed-server.stderr").read_text()
require("lake-manifest.json: invalid JSON: offset 2: unexpected end of input" in warning and
        "falling back to plain `lean --server`" in warning, "server fallback warning")
require((ROOT/"raw/valid-server.stderr").read_bytes() == (ROOT/"raw/restored-server.stderr").read_bytes() == b"",
        "valid/restored server no warning")
require(by["malformed-direct-lean"]["exit"] == 0, "direct Lean exit")
direct = [json.loads(z) for z in (ROOT/"raw/malformed-direct-lean.stdout").read_text().splitlines()]
require(len(direct) == 1 and direct[0]["data"] == "7", "retained OLean direct value")
require((ROOT/"work/consumer/lake-manifest.json").read_bytes() == good.read_bytes(), "final manifest restored")
print("PASS: valid/malformed/restored setup-batch-server split, raw fallback warning, direct OLean control, exact manifest edit and resource guards")
