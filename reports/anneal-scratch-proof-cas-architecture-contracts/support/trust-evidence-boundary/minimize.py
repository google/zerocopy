#!/usr/bin/env python3
"""Publish only allowlisted, redacted fields from this synthetic fixture."""
import argparse
import hashlib
import json
from pathlib import Path


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--raw", type=Path, required=True)
    ap.add_argument("--policy", type=Path, required=True)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    raw_bytes = a.raw.read_bytes()
    raw = json.loads(raw_bytes)
    work = str(a.work.resolve())
    token = raw["synthetic_token"]

    def redact(s):
        return s.replace(work, "$WORK").replace(token, "<REDACTED_SYNTHETIC_TOKEN>")

    runs = []
    for item in raw["runs"]:
        keep = {"label": item["label"], "exit": item["exit"],
                "seconds": item["seconds"],
                "stdout_sha256_raw": sha_bytes(item["stdout"].encode()),
                "stderr_sha256_raw": sha_bytes(item["stderr"].encode())}
        if item["label"] == "cargo-check-execute":
            keep["diagnostic_excerpts"] = [redact(line) for line in
                item["stderr"].splitlines() if "BUILD_DIAGNOSTIC" in line or
                "PROC_MACRO_DIAGNOSTIC" in line]
        if item["label"] == "lean-compile-execute":
            diagnostics = [json.loads(line) for line in item["stdout"].splitlines()]
            keep["diagnostic_data"] = [redact(d["data"]) for d in diagnostics]
        runs.append(keep)
    before = raw["inspect"]["source_hashes"]
    after = raw["inspect"]["workspace_files_after_metadata"]
    selected_build_artifacts = {}
    fixture = a.work.resolve() / "fixture"
    for p in sorted((fixture / "target/debug/deps").glob("*")):
        if p.is_file() and p.suffix in (".dylib", ".rmeta"):
            selected_build_artifacts[str(p.relative_to(fixture))] = {
                "sha256": sha_bytes(p.read_bytes()), "bytes": p.stat().st_size}
    lock = fixture / "Cargo.lock"
    if lock.exists():
        selected_build_artifacts["Cargo.lock"] = {
            "sha256": sha_bytes(lock.read_bytes()), "bytes": lock.stat().st_size}
    minimized = {
        "subjects": raw["subjects"],
        "policy_sha256": sha_bytes(a.policy.read_bytes()),
        "raw_results_sha256_local_only": sha_bytes(raw_bytes),
        "source_hashes_initial": before,
        "selected_build_artifacts": selected_build_artifacts,
        "inspect_only": {
            "workspace_file_hashes_unchanged": before == after,
            "effects_markers_before": raw["inspect"]["markers_before"],
            "effects_markers_after_metadata": raw["inspect"]["markers_after_metadata"],
            "lean_source_sha256": raw["lean_inspect"]["sha256"],
        },
        "runs": runs,
        "after_rust": raw["after_rust"],
        "after_lean": raw["after_lean"],
        "inside_cargo_markers": raw["inside_cargo_markers"],
        "local_loopback_datagrams": raw["local_loopback_datagrams"],
        "authority_observation": raw["authority_observation"],
        "redaction": {
            "workspace_root": "$WORK",
            "synthetic_token": "<REDACTED_SYNTHETIC_TOKEN>",
            "cargo_metadata_stdout": "hash only; contains absolute paths",
            "raw_result": "retained only in owned local scratch",
        },
    }
    a.out.write_text(json.dumps(minimized, indent=2) + "\n")


if __name__ == "__main__":
    main()
