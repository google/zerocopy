#!/usr/bin/env python3
"""Small, private-target Charon build-input closure and unit-identity probe."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
FIX = HERE / "fixture"
OUT = HERE / "raw-results.json"
ART = HERE / "artifacts"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
BIN = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
LIB = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/lib"
CHARON = TOOLS / "bin/charon"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def tree(root):
    return {str(p.relative_to(root)): sha(p) for p in sorted(root.rglob("*")) if p.is_file()}


def projection(path):
    doc = json.loads(path.read_text())
    tr = doc["translated"]
    functions = {}
    all_functions = []
    for fun in tr.get("fun_decls", []):
        if not fun:
            continue
        name = "::".join(part["Ident"][0] for part in fun["item_meta"]["name"] if "Ident" in part)
        all_functions.append(name)
        functions[name] = hashlib.sha256(json.dumps(fun.get("body"), sort_keys=True).encode()).hexdigest()
    return {"crate_name": tr["crate_name"], "has_errors": doc["has_errors"],
            "body_sha256": functions, "function_names": all_functions,
            "files": [f["name"] for f in tr.get("files", [])]}


def require_unit(record, expected):
    actual = record["projection"]["crate_name"]
    if actual != expected:
        raise ValueError(f"wrong compilation unit: expected {expected}, got {actual}")


def run_case(work, number, label, edit=None, overrides=None, flags=None, long_path=False):
    # All ordinary source roots have identical-length paths so the build-script
    # CARGO_MANIFEST_DIR input does not accidentally vary across isolated edits.
    name = f"src-{number:02d}" + ("-longer" if long_path else "")
    src = work / name
    shutil.copytree(FIX, src)
    if edit:
        rel, old, new = edit
        file = src / rel
        before = file.read_text()
        assert old in before
        file.write_text(before.replace(old, new))
    target = work / f"target-{number:02d}"
    dest = ART / f"{label}.llbc"
    extra = {"BUILD_VALUE": "7", "PROC_VALUE": "3", "PROBE_ENV": "A"}
    extra.update(overrides or {})
    env = dict(os.environ)
    env.update(extra)
    env.update({"RUSTUP_HOME": str(TOOLS / "rustup"), "CARGO_HOME": str(TOOLS / "cargo"),
                "CARGO_TARGET_DIR": str(target), "CARGO_BUILD_JOBS": "1",
                "CARGO_INCREMENTAL": "0", "RAYON_NUM_THREADS": "1",
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1",
                "PATH": os.pathsep.join([str(BIN), str(TOOLS / "bin"), env.get("PATH", "")]),
                "DYLD_LIBRARY_PATH": os.pathsep.join([str(LIB), str(LIB / "rustlib/aarch64-apple-darwin/lib")])})
    cmd = [str(CHARON), "cargo", "--preset", "aeneas", "--dest-file", str(dest), "--",
           "--manifest-path", str(src / "Cargo.toml"), "--package", "app_closure",
           *(flags or ["--lib"]), "--offline", "--locked", "-v"]
    start = time.monotonic()
    proc = subprocess.run(cmd, cwd=src, env=env, capture_output=True, text=True, timeout=60)
    generated = list(target.rglob("generated.rs"))
    record = {"label": label, "source_dir": name, "source_sha256": tree(src),
              "target_dir": target.name, "argv": [s.replace(str(work), "$WORK").replace(str(HERE), "$REPORT") for s in cmd],
              "environment_inputs": extra, "exit": proc.returncode,
              "seconds": round(time.monotonic() - start, 4),
              "stdout": proc.stdout.replace(str(work), "$WORK"),
              "stderr": proc.stderr.replace(str(work), "$WORK").replace(str(TOOLS), "$TOOLS"),
              "driver_units": re.findall(r"Running `[^\n]*charon-driver rustc --crate-name ([^ ]+)", proc.stderr),
              "generated_rs": [p.read_text() for p in generated],
              "llbc_sha256": sha(dest) if dest.exists() else None,
              "projection": projection(dest) if dest.exists() else None}
    assert proc.returncode == 0 and record["projection"] and not record["projection"]["has_errors"], label
    return record


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()
    work = args.work.resolve()
    assert not work.exists(), "choose an absent owned work directory"
    assert shutil.disk_usage(work.parent).free >= 15 * (1 << 30), "15 GiB free-disk guard"
    work.mkdir()
    ART.mkdir(exist_ok=True)
    for file in ART.glob("*.llbc"):
        file.unlink()
    cases = [
        run_case(work, 0, "baseline"),
        run_case(work, 1, "build-env", overrides={"BUILD_VALUE": "8"}),
        run_case(work, 2, "proc-env", overrides={"PROC_VALUE": "4"}),
        run_case(work, 3, "rustc-env", overrides={"PROBE_ENV": "AA"}),
        run_case(work, 4, "include-str", edit=("app/src/payload.txt", "payload-A", "payload-AB")),
        run_case(work, 5, "path-dependency", edit=("dep_path/src/lib.rs", "wrapping_add(11)", "wrapping_add(12)")),
        run_case(work, 6, "proc-source", edit=("proc_local/src/lib.rs", "x.wrapping_add({delta})", "x.wrapping_mul({delta})")),
        run_case(work, 7, "build-source", edit=("app/build.rs", "{value} + {path_len}", "{value} * 2 + {path_len}")),
        run_case(work, 8, "source-path", long_path=True),
        run_case(work, 9, "bin-unit", flags=["--bin", "app_closure_cli"]),
    ]
    baseline = cases[0]
    require_unit(baseline, "app_closure")
    for rec in cases[1:9]:
        require_unit(rec, "app_closure")
    assert {"build_script_build", "proc_local", "dep_path", "app_closure"}.issubset(set(baseline["driver_units"]))
    base_bodies = baseline["projection"]["body_sha256"]
    assert "app_closure::root" in base_bodies and "app_closure::macro_generated" in base_bodies
    root_variants = {c["label"]: c["projection"]["body_sha256"].get("app_closure::root") != base_bodies["app_closure::root"] for c in cases[1:9]}
    macro_variants = {c["label"]: c["projection"]["body_sha256"].get("app_closure::macro_generated") != base_bodies["app_closure::macro_generated"] for c in cases[1:9]}
    const_variants = {c["label"]: c["projection"]["body_sha256"].get("app_closure::BUILD_SUBJECT") != base_bodies["app_closure::BUILD_SUBJECT"] for c in cases[1:9]}
    dependency_variants = {c["label"]: c["projection"]["body_sha256"].get("dep_path::dep") != base_bodies["dep_path::dep"] for c in cases[1:9]}
    wrong_unit_error = None
    try:
        require_unit(cases[9], "app_closure")
    except ValueError as exc:
        wrong_unit_error = str(exc)
    assert wrong_unit_error == "wrong compilation unit: expected app_closure, got app_closure_cli"
    assert cases[0]["generated_rs"] != cases[1]["generated_rs"]
    assert cases[0]["generated_rs"] != cases[7]["generated_rs"]
    assert cases[0]["generated_rs"] != cases[8]["generated_rs"]
    assert const_variants["build-env"] and const_variants["build-source"] and const_variants["source-path"]
    assert root_variants["rustc-env"] and root_variants["include-str"]
    # The external dependency body is opaque in this extraction: its source
    # changes while the primary crate's LLBC may stay semantically identical.
    assert cases[0]["source_sha256"]["dep_path/src/lib.rs"] != cases[5]["source_sha256"]["dep_path/src/lib.rs"]
    assert not dependency_variants["path-dependency"]
    assert macro_variants["proc-env"]
    assert "core::num::wrapping_add" in baseline["projection"]["function_names"]
    assert "core::num::wrapping_mul" in cases[6]["projection"]["function_names"]
    result = {"tool_sha256": {"charon": sha(CHARON), "cargo": sha(BIN / "cargo"), "rustc": sha(BIN / "rustc")},
              "host": "aarch64-apple-darwin", "cases": cases, "root_body_differs": root_variants,
              "macro_body_differs": macro_variants, "const_body_differs": const_variants,
              "dependency_body_differs": dependency_variants,
              "wrong_unit_rejection": wrong_unit_error,
              "artifact_sha256": {p.name: sha(p) for p in sorted(ART.glob("*.llbc"))}}
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"cases": len(cases), "root_body_differs": root_variants,
                      "macro_body_differs": macro_variants, "const_body_differs": const_variants,
                      "dependency_body_differs": dependency_variants,
                      "wrong_unit_rejection": wrong_unit_error}, indent=2))


if __name__ == "__main__":
    main()
