#!/usr/bin/env python3
"""Offline assertions over retained small-fixture evidence; never runs Lake."""

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
OBS = json.loads((HERE / "observations.json").read_text())
STATES = json.loads((HERE / "state-snapshots.json").read_text())
SOURCE = json.loads((HERE / "source-map.json").read_text())
RUNTIME = json.loads((HERE / "runtime-identity.json").read_text())
PREFIX = "20261003-synthetic-1-"


def fail(condition, reason):
    if not condition:
        raise AssertionError(reason)


rows = {r["cell"].removeprefix(PREFIX): r for r in OBS["cells"]}
fail(len(rows) == len(OBS["cells"]) == 24, "exactly 24 unique recorded cases")
fail(len(STATES["cells"]) == 20, "20 consumer snapshot pairs")
fail(SOURCE["versions"]["rc2"]["revision"] ==
     "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc", "RC2 identity")
fail(SOURCE["versions"]["final"]["revision"] ==
     "d024af099ca4bf2c86f649261ebf59565dc8c622", "final identity")
for version in ("rc2", "final"):
    fail(RUNTIME[version]["lean_git_hash"] == SOURCE["versions"][version]["revision"],
         f"{version}: runtime/source identity mismatch")
fail(RUNTIME["rc2"]["libleanshared_dylib_sha256"] !=
     RUNTIME["final"]["libleanshared_dylib_sha256"], "distinct Lean runtimes")

for version in ("rc2", "final"):
    for suffix in ("prepare", "a-normal", "b-depth", "c-root-name",
                   "d-package-order", "e-no-manifest", "f-old", "g-local-edit",
                   "h-no-op", "missing-prepare", "i-copy-healthy",
                   "j-copy-missing-artifact"):
        row = rows[f"{version}-{suffix}"]
        fail(row["abort"] is None, f"{version}-{suffix}: guard abort")
        fail(row["network_attempts"] == [] if "network_attempts" in row else True,
             f"{version}-{suffix}: network event")
        fail(row["peak_sampled_rss_mib"] < 1536, f"{version}-{suffix}: sampled RSS ceiling")
        fail(row["min_disk_free_gib"] > 10, f"{version}-{suffix}: sampled disk floor")
    for suffix in ("prepare", "a-normal", "b-depth", "c-root-name", "f-old",
                   "g-local-edit", "h-no-op", "missing-prepare", "i-copy-healthy"):
        fail(rows[f"{version}-{suffix}"]["exit"] == 0, f"{version}-{suffix}: expected success")
    for suffix in ("a-normal", "b-depth", "c-root-name", "f-old",
                   "g-local-edit", "h-no-op", "i-copy-healthy"):
        fail(rows[f"{version}-{suffix}"]["shared_attempts"] == [],
             f"{version}-{suffix}: unexpected producer mutation attempt")
    hashes = [rows[f"{version}-{suffix}"]["shared_build_traces"][0]["depHash"]
              for suffix in ("prepare", "a-normal", "b-depth", "c-root-name")]
    fail(len(set(hashes)) == 1, f"{version}: same producer trace across consumer path/name")
    for suffix in ("a-normal", "b-depth", "c-root-name", "g-local-edit", "h-no-op"):
        fail("Replayed Shared" in rows[f"{version}-{suffix}"]["stdout"],
             f"{version}-{suffix}: expected shared hash replay")
    fail("Built Client" in rows[f"{version}-g-local-edit"]["stdout"],
         f"{version}: private edit rebuild")
    fail("Replayed Client" in rows[f"{version}-h-no-op"]["stdout"],
         f"{version}: private no-op replay")
    missing = rows[f"{version}-j-copy-missing-artifact"]
    fail(missing["exit"] == 3 and len(missing["shared_attempts"]) == 1 and
         missing["shared_attempts"][0]["path"].endswith("Shared.trace.nobuild") and
         "Shared.trace.nobuild" in missing["stdout"],
         f"{version}: --no-build missing OLean failure")
    fail(missing["shared_unchanged"], f"{version}: missing producer changed")

for suffix in ("d-package-order", "e-no-manifest"):
    rc = rows[f"rc2-{suffix}"]
    fin = rows[f"final-{suffix}"]
    fail(rc["exit"] == 1 and len(rc["shared_attempts"]) == 1 and
         rc["shared_attempts"][0]["path"].endswith("lakefile.olean.lock"),
         f"RC2 {suffix}: package-local config lock")
    fail(fin["exit"] == 0 and fin["shared_attempts"] == [] and
         "Replayed Shared" in fin["stdout"],
         f"final {suffix}: consumer-owned config and shared replay")

for suffix in ("a-normal", "d-package-order", "e-no-manifest"):
    rc = rows[f"rc2-{suffix}"]
    fin = rows[f"final-{suffix}"]
    fail(any("/source/probe_shared" in t["owner"] for t in rc["config_traces"]),
         f"RC2 {suffix}: producer config trace owner")
    fail(all("/work/" in t["owner"] for t in fin["config_traces"]),
         f"final {suffix}: consumer config trace owner")

for s in STATES["cells"]:
    short = s["cell"].removeprefix(PREFIX)
    fail(short in rows and rows[short]["shared_unchanged"], f"{short}: recorded state result")
    for kind in ("shared", "pad"):
        fail(s[f"{kind}_before"] == s[f"{kind}_after"],
             f"{short}: immutable producer content/metadata changed")

print("PASS: 24 cases, 20 full immutable before/after pairs, RC2/final ownership split,"
      " hash replay, local edit/no-op, and both --no-build failure paths")
