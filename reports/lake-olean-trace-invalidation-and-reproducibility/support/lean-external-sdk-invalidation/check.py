#!/usr/bin/env python3
"""Offline consistency check for the preserved tiny RC2 SDK observation set.

No Lean installation, network, original scratch directory, or build is used.
This checks the internal evidence contract, not the authenticity of the
original executions. See REPORT.md for the observation and reproduction scope.
"""

import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = json.loads((HERE / "observations.json").read_text())


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def run(label):
    return DATA["runs"][label]


def text(label):
    return run(label)["stdout_excerpt"]


def artifact(label):
    return DATA["local_artifacts"][label]


def main():
    require(DATA["toolchain"]["revision"] ==
            "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc", "RC2 revision")
    for name, digest in DATA["fixture_sha256"].items():
        require(sha256((HERE / "fixtures" / name).read_bytes()) == digest,
                f"fixture changed: {name}")
    require(DATA["toolchain"]["lean_bin_sha256"] ==
            "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997",
            "Lean launcher identity")
    require(DATA["toolchain"]["lake_bin_sha256"] ==
            "9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb",
            "Lake launcher identity")
    require(DATA["real_bundle"]["native_aeneas_meta_dylib_sha256"] ==
            "0ffa1ca9ecf894cd4256c75a049287dd285225767c0b41ae9b2e9a3e6e7e4745",
            "native plugin identity")
    require(len(DATA["runs"]) == 20, "observation cell count")
    for label, cell in DATA["runs"].items():
        for stream in ("stdout", "stderr"):
            excerpt = cell[f"{stream}_excerpt"]
            require(sha256(excerpt.encode()) == cell[f"{stream}_excerpt_sha256"],
                    f"excerpt hash changed: {label}/{stream}")
            require(re.fullmatch(r"[0-9a-f]{64}",
                                 cell[f"{stream}_original_sha256"]) is not None,
                    f"missing original output hash: {label}/{stream}")
            require("/Users/" not in excerpt, f"private path: {label}/{stream}")
        require(cell["abort"] is None, f"guard abort: {label}")
        for key in ("immutable_trees_unchanged", "sdk_trees_unchanged"):
            if key in cell:
                require(cell[key] is True, f"shared tree changed: {label}")
        for key in ("blocked_sdk_mutations_count",
                    "blocked_immutable_mutations_count",
                    "blocked_mutations_count", "network_attempts_count"):
            if key in cell:
                require(cell[key] == 0, f"blocked mutation/network: {label}/{key}")

    leanpath = "20261003-sdk-canary-2-"
    for version in ("v1", "v2"):
        prepared = run(leanpath + f"sdk-{version}-prepare")
        require(prepared["exit"] == 0, f"SDK {version} preparation")
        token = next(iter(prepared["source_tokens_before"].values()))
        require(token["sha256"] == DATA["fixture_sha256"][f"Sdk-{version}.lean"],
                f"SDK {version} source identity")
    require(run(leanpath + "baseline-v1-build")["exit"] == 1 and
            "unknown module prefix 'Sdk'" in text(leanpath + "baseline-v1-build"),
            "LEAN_PATH-only Lake build failure")
    require("sdk-v1/.lake/build/lib/lean" in text(leanpath + "lake-env-path"),
            "Lake env included the external LEAN_PATH")
    require(run("20261003-overlay-1-baseline-v1-build")["exit"] == 1 and
            "unknown module prefix 'Sdk'" in
            text("20261003-overlay-1-baseline-v1-build"),
            "symlinked Lean launch failure")
    require(run("20261003-overlay-2-baseline-v1-build")["exit"] == 0 and
            run("20261003-overlay-2-baseline-v1-eval")["exit"] == 1 and
            "<LEAN_RC2_ROOT>/lib/lean" in
            text("20261003-overlay-2-baseline-v1-eval"),
            "copied Lean/symlinked Lake split selection")

    baseline = "20261003-overlay-3-baseline-"
    for label in ("v1-build", "v2-build", "v1-eval", "v2-eval"):
        require(run(baseline + label)["exit"] == 0, f"baseline failed: {label}")
    require(text(baseline + "v1-eval").strip().splitlines() ==
            ["10", "10", "true", "clientProof : clientValue = sdkValue"],
            "v1 semantic output")
    require(text(baseline + "v2-eval").strip().splitlines() ==
            ["10", "20", "false", "clientProof : clientValue = sdkValue"],
            "stale v2 semantic output")
    require(run(baseline + "v1-build")["source_tokens_before"] ==
            run(baseline + "v2-build")["source_tokens_before"],
            "consumer source bytes/mtimes changed during SDK switch")
    require(artifact("baseline-v1-build") == artifact("baseline-v2-build"),
            "Client OLean/trace/hash changed on SDK switch")
    require(artifact("baseline-v1-build")["depHash"] == "90b5218aeee20417",
            "unexpected Lake dependency hash")
    require(DATA["sdk_olean"]["sdk_v1_olean"]["sha256"] !=
            DATA["sdk_olean"]["sdk_v2_olean"]["sha256"],
            "SDK OLeans did not change")
    for name in ("root-name-v2-build", "identity-v2-build",
                 "baseline-v2-rebuild-after-clean"):
        label = "20261003-overlay-3-" + name
        require(run(label)["exit"] == 1 and "is false" in text(label),
                f"local invalidation did not reject false proof: {name}")
    require(run("20261003-overlay-3-baseline-local-clean")["exit"] == 0,
            "private clean failed")

    coherent = "20261003-112910-"
    for name in ("prefix", "build", "setup"):
        require(run(coherent + name)["exit"] == 0,
                f"coherent launcher {name} failed")
    require(text(coherent + "prefix").strip().endswith("/view"),
            "copied Lake did not select the SDK view")
    require("libaeneas_AeneasMeta.dylib" in text(coherent + "build") and
            "dyld[" in text(coherent + "build"), "native loader line missing")
    require("libaeneas_AeneasMeta.dylib" in
            json.dumps(json.loads(text(coherent + "setup"))),
            "native setup plugin missing")
    require(all(DATA["coherent_view_integrity"][key] is True for key in
                ("view_and_sdk_content_metadata_unchanged",
                 "archive_tree_metadata_unchanged",
                 "selected_shared_artifact_hashes_unchanged")),
            "coherent view integrity")
    require(DATA["coherent_view_integrity"]["copied_lean_bytes"] == 49968 and
            DATA["coherent_view_integrity"]["copied_lake_bytes"] == 51840,
            "launcher sizes")
    print("offline evidence check passed: 20 cells, fixtures, stale proof, controls, launchers, native load")


if __name__ == "__main__":
    main()
