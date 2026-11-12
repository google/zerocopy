#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical verification of Level 1, Level 2, and Level 3 determinism and early-cutoff properties."""

import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import time

LEAN = pathlib.Path("/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
CAPTURE = pathlib.Path("/tmp/ref_research_stack221_perf/mvp_src/target/release/anneal-rustc-capture")
SYSROOT = pathlib.Path("/usr/local/google/home/joshlf/.rustup/toolchains/nightly-2026-05-31-x86_64-unknown-linux-gnu")
STARNIX_FIXTURE = pathlib.Path("/tmp/ref_research_stack221_perf/fixtures/starnix")
BASELINE_ARTIFACTS = pathlib.Path("/tmp/anneal-mvp-starnix-installed-final/baseline-artifacts")
MVP_SRC = pathlib.Path("/tmp/ref_research_stack221_perf/mvp_src")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    return sha256_bytes(path.read_bytes())


def run_capture_in_stage(stage_dir: pathlib.Path, modifier=None):
    rust_dir = stage_dir / "rust"
    shutil.copytree(STARNIX_FIXTURE / "source", rust_dir)
    if modifier is not None:
        modifier(rust_dir)
    out_dir = stage_dir / "capture"
    out_dir.mkdir(parents=True, exist_ok=True)
    source_files = sorted(rust_dir.glob("*.rs"))
    cmd = [
        str(CAPTURE),
        "capture",
        "--crate-root",
        str(rust_dir / "lib.rs"),
        "--crate-name",
        "ebpf_core",
        "--edition",
        "2024",
        "--target",
        "x86_64-unknown-linux-gnu",
        "--out-dir",
        str(out_dir),
        "--sysroot",
        str(SYSROOT),
        "--select",
        "api::apply_endianness",
    ]
    for sf in source_files:
        cmd.extend(["--source-file", str(sf)])
    env = {"PATH": "/usr/bin:/bin", "LD_LIBRARY_PATH": str(SYSROOT / "lib")}
    t0 = time.perf_counter()
    proc = subprocess.run(cmd, cwd=rust_dir, env=env, capture_output=True, text=True, check=True)
    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    capture_json_bytes = (out_dir / "capture.json").read_bytes()
    captured_lean_bytes = (out_dir / "Captured.lean").read_bytes()
    return {
        "elapsed_ms": elapsed_ms,
        "capture_json_sha256": sha256_bytes(capture_json_bytes),
        "captured_lean_sha256": sha256_bytes(captured_lean_bytes),
        "capture_json": json.loads(capture_json_bytes),
        "captured_lean": captured_lean_bytes.decode("utf-8"),
        "stdout": proc.stdout,
    }


def normalize_capture_json(manifest: dict, stage_rust_dir: str) -> bytes:
    """Normalize staging-path fields in capture.json so content hash is stage-independent."""
    norm = json.loads(json.dumps(manifest))
    prefix = stage_rust_dir.rstrip("/") + "/"
    if norm["configuration"]["crate_root"].startswith(prefix):
        norm["configuration"]["crate_root"] = norm["configuration"]["crate_root"][len(prefix):]
    norm["configuration"]["declared_source_files"] = [
        p[len(prefix):] if p.startswith(prefix) else p
        for p in norm["configuration"]["declared_source_files"]
    ]
    for sf in norm["source_files"]:
        if sf["path"].startswith(prefix):
            sf["path"] = sf["path"][len(prefix):]
    return json.dumps(norm, sort_keys=True, separators=(",", ":")).encode("utf-8")


def test_capture_determinism_and_cutoff():
    print("=== Test 1 & 2: Capture Determinism & Unrelated-Edit Early Cutoff ===")
    baseline_captured_lean_sha = sha256_file(BASELINE_ARTIFACTS / "capture/Captured.lean")
    baseline_capture_json = json.loads((BASELINE_ARTIFACTS / "capture/capture.json").read_text())

    results = {}
    with tempfile.TemporaryDirectory(prefix="stageA_") as dir_a, \
         tempfile.TemporaryDirectory(prefix="stageB_") as dir_b:
        path_a = pathlib.Path(dir_a)
        path_b = pathlib.Path(dir_b)

        res_a = run_capture_in_stage(path_a / "clean")
        res_b = run_capture_in_stage(path_b / "clean")

        norm_a = sha256_bytes(normalize_capture_json(res_a["capture_json"], str((path_a / "clean/rust").resolve())))
        norm_b = sha256_bytes(normalize_capture_json(res_b["capture_json"], str((path_b / "clean/rust").resolve())))

        # Scenario 2a: Comment / whitespace edit in api.rs and verifier.rs
        def edit_comments(rust_dir: pathlib.Path):
            for fname in ["api.rs", "verifier.rs"]:
                p = rust_dir / fname
                p.write_text(p.read_text() + "\n// Unrelated comment added for caching test\n   \n")

        res_comment = run_capture_in_stage(path_a / "comment_edit", edit_comments)

        # Scenario 2b: Unrelated function body edit in verifier.rs and api.rs
        def edit_unrelated_fn_body_safe(rust_dir: pathlib.Path):
            a = rust_dir / "api.rs"
            a_text = a.read_text()
            a_mod = a_text.replace("pub fn bits(&self) -> usize {", "pub fn bits(&self) -> usize { let _unused_local = 42usize;")
            assert a_mod != a_text
            a.write_text(a_mod)

            v = rust_dir / "verifier.rs"
            v_text = v.read_text()
            v_mod = v_text.replace(
                "fn popcount_u64(mut x: u64) -> usize {",
                "fn popcount_u64(mut x: u64) -> usize { let _extra_temp = x.wrapping_add(1);",
                1,
            )
            assert v_mod != v_text
            v.write_text(v_mod)

        res_unrelated_body = run_capture_in_stage(path_a / "unrelated_body", edit_unrelated_fn_body_safe)

        # Scenario 2c: Adding a brand new function in verifier.rs vs api.rs
        def add_new_fn_in_verifier(rust_dir: pathlib.Path):
            v = rust_dir / "verifier.rs"
            v.write_text(v.read_text() + "\npub fn newly_added_unrelated_verifier_helper(x: u64) -> u64 { x.wrapping_add(7) }\n")

        res_new_fn_verifier = run_capture_in_stage(path_a / "new_fn_verifier", add_new_fn_in_verifier)

        def add_new_fn_in_api_after(rust_dir: pathlib.Path):
            a = rust_dir / "api.rs"
            a.write_text(a.read_text() + "\npub fn newly_added_unrelated_api_helper(x: u64) -> u64 { x.wrapping_sub(3) }\n")

        res_new_fn_api_after = run_capture_in_stage(path_a / "new_fn_api_after", add_new_fn_in_api_after)

        def add_new_fn_in_api_before(rust_dir: pathlib.Path):
            a = rust_dir / "api.rs"
            a.write_text("pub fn early_helper(x: u64) -> u64 { x }\n" + a.read_text())

        res_new_fn_api_before = run_capture_in_stage(path_a / "new_fn_api_before", add_new_fn_in_api_before)

        results = {
            "baseline_captured_lean_sha256": baseline_captured_lean_sha,
            "stageA_clean": {
                "raw_capture_json_sha256": res_a["capture_json_sha256"],
                "norm_capture_json_sha256": norm_a,
                "captured_lean_sha256": res_a["captured_lean_sha256"],
                "matches_baseline_captured_lean": res_a["captured_lean_sha256"] == baseline_captured_lean_sha,
            },
            "stageB_clean": {
                "raw_capture_json_sha256": res_b["capture_json_sha256"],
                "norm_capture_json_sha256": norm_b,
                "captured_lean_sha256": res_b["captured_lean_sha256"],
                "norm_capture_json_matches_stageA": norm_a == norm_b,
                "raw_capture_json_matches_stageA": res_a["capture_json_sha256"] == res_b["capture_json_sha256"],
                "captured_lean_matches_stageA": res_a["captured_lean_sha256"] == res_b["captured_lean_sha256"],
            },
            "comment_edit": {
                "raw_capture_json_sha256": res_comment["capture_json_sha256"],
                "captured_lean_sha256": res_comment["captured_lean_sha256"],
                "captured_lean_matches_clean": res_comment["captured_lean_sha256"] == baseline_captured_lean_sha,
            },
            "unrelated_fn_body_edit": {
                "raw_capture_json_sha256": res_unrelated_body["capture_json_sha256"],
                "captured_lean_sha256": res_unrelated_body["captured_lean_sha256"],
                "captured_lean_matches_clean": res_unrelated_body["captured_lean_sha256"] == baseline_captured_lean_sha,
            },
            "new_fn_in_verifier": {
                "raw_capture_json_sha256": res_new_fn_verifier["capture_json_sha256"],
                "captured_lean_sha256": res_new_fn_verifier["captured_lean_sha256"],
                "captured_lean_matches_clean": res_new_fn_verifier["captured_lean_sha256"] == baseline_captured_lean_sha,
                "diff_preview": "" if res_new_fn_verifier["captured_lean"] == res_a["captured_lean"] else res_new_fn_verifier["captured_lean"][:300],
            },
            "new_fn_in_api_after": {
                "raw_capture_json_sha256": res_new_fn_api_after["capture_json_sha256"],
                "captured_lean_sha256": res_new_fn_api_after["captured_lean_sha256"],
                "captured_lean_matches_clean": res_new_fn_api_after["captured_lean_sha256"] == baseline_captured_lean_sha,
                "diff_preview": "" if res_new_fn_api_after["captured_lean"] == res_a["captured_lean"] else res_new_fn_api_after["captured_lean"][:300],
            },
            "new_fn_in_api_before": {
                "raw_capture_json_sha256": res_new_fn_api_before["capture_json_sha256"],
                "captured_lean_sha256": res_new_fn_api_before["captured_lean_sha256"],
                "captured_lean_matches_clean": res_new_fn_api_before["captured_lean_sha256"] == baseline_captured_lean_sha,
                "diff_preview": "" if res_new_fn_api_before["captured_lean"] == res_a["captured_lean"] else res_new_fn_api_before["captured_lean"][:300],
            },
        }
        print(json.dumps(results, indent=2))
        return results


def test_lean_olean_determinism():
    print("\n=== Test 3: Lean .olean Compilation Determinism Across Staging Directories ===")
    baseline_res = json.loads((BASELINE_ARTIFACTS / "result.json").read_text())
    baseline_olean_shas = {
        entry["module"]: entry["artifacts"][0]["sha256"]
        for entry in baseline_res["audit"]["sources"]
    }
    lock = json.loads((MVP_SRC / "trusted/lean/foundation-lock.json").read_text())
    lib_lock = json.loads((MVP_SRC / "trusted/audit/library-lock.json").read_text())

    prefix = pathlib.Path(
        subprocess.run([str(LEAN), "--print-prefix"], capture_output=True, text=True, check=True).stdout.strip()
    ).resolve()

    def build_base_artifacts():
        arts = {}
        for mod, rec in list(lock["modules"].items()) + list(lib_lock["modules"].items()):
            rel = mod.replace(".", "/")
            olean_parts = [
                str(prefix / "lib/lean" / f"{rel}.{p}")
                for p in ["olean", "olean.server", "olean.private"]
                if rec["parts"].get(p) is not None
            ]
            ir_parts = [
                str(prefix / "lib/lean" / f"{rel}.{p}")
                for p in ["ir.sig", "ir"]
                if rec["parts"].get(p) is not None
            ]
            arts[mod] = [olean_parts, ir_parts]
        return arts

    # Compile the fast modules (excluding ProductionSteps first, or including all fast ones) in two distinct temp dirs
    modules_in_topo_order = [
        ("Trusted.Mvp.Syntax", BASELINE_ARTIFACTS / "anneal/trusted/lean/Trusted/Mvp/Syntax.lean", [
            {"module": "Init.Data.BitVec.Basic", "importAll": False, "isExported": True, "isMeta": False},
            {"module": "Init.Data.List.Basic", "importAll": False, "isExported": True, "isMeta": False},
        ]),
        ("Trusted.Mvp.Semantics", BASELINE_ARTIFACTS / "anneal/trusted/lean/Trusted/Mvp/Semantics.lean", [
            {"module": "Trusted.Mvp.Syntax", "importAll": False, "isExported": True, "isMeta": False},
        ]),
        ("Trusted.Mvp", BASELINE_ARTIFACTS / "anneal/trusted/lean/Trusted/Mvp.lean", [
            {"module": "Trusted.Mvp.Semantics", "importAll": False, "isExported": True, "isMeta": False},
        ]),
        ("Trusted", BASELINE_ARTIFACTS / "anneal/trusted/lean/Trusted.lean", [
            {"module": "Trusted.Mvp", "importAll": False, "isExported": True, "isMeta": False},
        ]),
        ("Captured", BASELINE_ARTIFACTS / "capture/Captured.lean", [
            {"module": "Trusted.Mvp", "importAll": False, "isExported": True, "isMeta": False},
        ]),
        ("Endianness", BASELINE_ARTIFACTS / "authored/Endianness.lean", [
            {"module": "Init.Data.BitVec.Lemmas", "importAll": False, "isExported": True, "isMeta": False},
        ]),
        ("Spec", BASELINE_ARTIFACTS / "authored/Spec.lean", [
            {"module": "Trusted.Mvp", "importAll": False, "isExported": True, "isMeta": False},
            {"module": "Endianness", "importAll": False, "isExported": True, "isMeta": False},
        ]),
        ("Expected", BASELINE_ARTIFACTS / "generated/Expected.lean", [
            {"module": "Trusted.Mvp", "importAll": False, "isExported": True, "isMeta": False},
            {"module": "Captured", "importAll": False, "isExported": True, "isMeta": False},
            {"module": "Spec", "importAll": False, "isExported": True, "isMeta": False},
        ]),
    ]

    stage_hashes = {}
    for label in ["stage_alpha", "stage_beta_deep/nested/dir"]:
        with tempfile.TemporaryDirectory(prefix="lean_det_") as tmp:
            stage = pathlib.Path(tmp) / label
            stage.mkdir(parents=True, exist_ok=True)
            arts = build_base_artifacts()
            mod_hashes = {}
            for mod, src_orig, imports in modules_in_topo_order:
                rel = mod.replace(".", "/")
                src_staged = stage / "target-src" / f"{rel}.lean"
                src_staged.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src_orig, src_staged)
                setup_path = stage / f"{mod}.setup.json"
                setup_obj = {
                    "name": mod,
                    "isModule": False,
                    "imports": imports,
                    "importArts": arts,
                    "dynlibs": [],
                    "plugins": [],
                    "options": {},
                }
                setup_path.write_text(json.dumps(setup_obj))
                out_olean = stage / "target-lib" / f"{rel}.olean"
                out_olean.parent.mkdir(parents=True, exist_ok=True)
                cmd = [
                    "anneal-lean-run", "--mode", "file", "--concurrency", "4", "--",
                    str(LEAN),
                    "-j1",
                    "-M2048",
                    "-t0",
                    "-DElab.async=false",
                    "-Ddebug.skipKernelTC=false",
                    "--setup",
                    str(setup_path),
                    "-o",
                    str(out_olean),
                    str(src_staged),
                ]
                subprocess.run(cmd, cwd=stage, check=True, capture_output=True)
                # Check which companion files exist
                emitted_parts = []
                for part in ["olean", "olean.server", "olean.private", "ir.sig", "ir", "ilean"]:
                    cand = out_olean.parent / f"{out_olean.stem}.{part}"
                    if cand.exists():
                        emitted_parts.append(part)
                sha = sha256_file(out_olean)
                mod_hashes[mod] = {
                    "sha256": sha,
                    "emitted_parts": emitted_parts,
                    "matches_baseline_result_json": sha == baseline_olean_shas[mod],
                    "size_bytes": out_olean.stat().st_size,
                }
                arts[mod] = [[str(out_olean)], []]
            stage_hashes[label] = mod_hashes

    comparison = {}
    for mod, _, _ in modules_in_topo_order:
        ha = stage_hashes["stage_alpha"][mod]["sha256"]
        hb = stage_hashes["stage_beta_deep/nested/dir"][mod]["sha256"]
        h_base = baseline_olean_shas[mod]
        comparison[mod] = {
            "stage_alpha_sha256": ha,
            "stage_beta_sha256": hb,
            "baseline_sha256": h_base,
            "alpha_eq_beta": ha == hb,
            "alpha_eq_baseline": ha == h_base,
            "emitted_parts": stage_hashes["stage_alpha"][mod]["emitted_parts"],
            "size_bytes": stage_hashes["stage_alpha"][mod]["size_bytes"],
        }
    print(json.dumps(comparison, indent=2))
    return comparison


if __name__ == "__main__":
    r12 = test_capture_determinism_and_cutoff()
    r3 = test_lean_olean_determinism()
    out_path = pathlib.Path("/tmp/ref_research_stack221_perf/track6/support/determinism_results.json")
    out_path.write_text(json.dumps({"level1_2": r12, "level3": r3}, indent=2))
