#!/usr/bin/env python3
"""Sequential Charon/Aeneas A-B-A, provenance, and failure-boundary probe."""

import hashlib
import json
import os
from contextlib import contextmanager
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys


HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixture"
ARTIFACTS = HERE / "artifacts"
OUT = HERE / "raw-results.json"
HANDOFF = HERE / "handoff-manifest.json"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
CHARON = TOOLS / "bin/charon"
AENEAS = TOOLS / "bin/aeneas"
RUST_BIN = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(args, cwd, env, timeout=45):
    command = [str(x) for x in args]
    result = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
    return {"command": command, "cwd_role": cwd.name, "exit_code": result.returncode,
            "stdout": result.stdout, "stderr": result.stderr}


def inventory(root):
    return {str(path.relative_to(root)): {"bytes": path.stat().st_size, "sha256": sha(path)}
            for path in sorted(root.rglob("*")) if path.is_file()}


def names(tokens):
    result = []
    for part in tokens:
        if "Ident" in part:
            result.append(part["Ident"][0])
        elif "Impl" in part:
            result.append("<impl>")
        else:
            result.append("<other>")
    return "::".join(result)


def llbc_manifest(data):
    t = data["translated"]
    seen = set()
    keyed_names = []
    for entry in t["item_names"]:
        key = json.dumps(entry["key"], sort_keys=True)
        assert key not in seen
        seen.add(key)
        keyed_names.append({"key": entry["key"], "name": names(entry["value"])})
    functions = []
    for item in t.get("fun_decls", []):
        meta = item["item_meta"]
        span = meta.get("span")
        functions.append({"id": item["def_id"], "name": names(meta["name"]),
                          "local": meta.get("is_local"), "opacity": meta.get("opacity"),
                          "body_kind": list(item["body"])[0] if isinstance(item.get("body"), dict) else str(item.get("body")),
                          "span": span.get("data") if span else None,
                          "source_text": meta.get("source_text"),
                          "attributes": meta.get("attr_info", {}).get("attributes", [])})
    return {"charon_version": data["charon_version"], "has_errors": data["has_errors"],
            "crate_name": t["crate_name"], "preset": t["options"].get("preset"),
            "dest_file": t["options"].get("dest_file"),
            "target_information": t.get("target_information"),
            "files": [{"id": x["id"], "name": x["name"], "crate_name": x["crate_name"],
                       "contents_sha256": hashlib.sha256(x["contents"].encode()).hexdigest() if x["contents"] is not None else None}
                      for x in t.get("files", [])],
            "item_names": sorted(keyed_names, key=lambda x: json.dumps(x["key"], sort_keys=True)),
            "ordered_decls": t.get("ordered_decls"), "functions": functions}


def canonical_llbc(data):
    """Only JSON object order and keyed name-map entry order are normalized."""
    copy = json.loads(json.dumps(data))
    for field in ("item_names", "short_names"):
        values = copy["translated"][field]
        keys = [json.dumps(entry["key"], sort_keys=True) for entry in values]
        assert len(keys) == len(set(keys))
        copy["translated"][field] = sorted(values, key=lambda x: json.dumps(x["key"], sort_keys=True))
    return hashlib.sha256(json.dumps(copy, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def difference_paths(left, right, path=""):
    if type(left) is not type(right):
        return [path]
    if isinstance(left, dict):
        paths = []
        for key in sorted(set(left) | set(right)):
            child = path + "/" + key
            if key not in left or key not in right:
                paths.append(child)
            else:
                paths.extend(difference_paths(left[key], right[key], child))
        return paths
    if isinstance(left, list):
        paths = [path + "/length"] if len(left) != len(right) else []
        for index, (a, b) in enumerate(zip(left, right)):
            paths.extend(difference_paths(a, b, path + "/" + str(index)))
        return paths
    return [path] if left != right else []


def lean_manifest(root):
    files = {}
    for path in sorted(root.rglob("*.lean")):
        source = path.read_text()
        declarations = [line.strip() for line in source.splitlines()
                        if re.match(r"^\s*(?:def|theorem|opaque|abbrev|structure|inductive)\s+", line)]
        imports = [line.strip() for line in source.splitlines() if re.match(r"^\s*import\s+", line)]
        origins = [line.strip() for line in source.splitlines()
                   if "source" in line.lower() or "snapshot_probe" in line.lower()]
        files[str(path.relative_to(root))] = {"sha256": sha(path), "bytes": path.stat().st_size,
                                             "imports": imports, "declaration_lines": declarations,
                                             "source_comment_lines": origins}
    return files


def handoff_manifest(runs):
    records = []
    for run_record in runs:
        manifest = run_record.get("manifest")
        if not manifest:
            records.append({"run": run_record["label"], "status": "no-new-llbc",
                            "charon_exit_code": run_record["charon"]["exit_code"]})
            continue
        lean = run_record.get("lean_manifest", {})
        funs = lean.get("Funs.lean", {})
        generated = []
        for function in manifest["functions"]:
            if not function["local"]:
                continue
            suffix = function["name"].split("::")[-1]
            candidate = [line for line in funs.get("declaration_lines", [])
                         if re.match(r"^def\s+" + re.escape(suffix) + r"(?:\s|$)", line)]
            generated.append({"rust_item": function["name"], "llbc_def_id": function["id"],
                              "source_span": function["span"],
                              "candidate_lean_declaration": candidate,
                              "relation_basis": "printed-name and Aeneas source-comment match only"})
        records.append({"run": run_record["label"], "source_sha256": run_record["source_sha256"],
                        "llbc_sha256": run_record["llbc_sha256"],
                        "llbc_has_errors": manifest["has_errors"],
                        "aeneas_exit_code": run_record.get("aeneas", {}).get("exit_code"),
                        "generated_files": run_record.get("lean_inventory", {}),
                        "module_imports": {name: item["imports"] for name, item in lean.items()},
                        "local_declarations": generated})
    return {"records": records, "scope": "illustrative lexical cross-layer inventory, not editable proof ranges"}


@contextmanager
def fixed_scratch():
    """Keep the embedded source path stable across replay runs."""
    root = HERE / "work"
    if root.exists():
        shutil.rmtree(root)
    root.mkdir()
    try:
        yield root
    finally:
        shutil.rmtree(root)


def main():
    if ARTIFACTS.exists():
        shutil.rmtree(ARTIFACTS)
    ARTIFACTS.mkdir()
    env = dict(os.environ)
    env.update({"RUSTUP_HOME": str(TOOLS / "rustup"), "CARGO_HOME": str(TOOLS / "cargo"),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1",
                "PATH": os.pathsep.join([str(RUST_BIN), str(TOOLS / "bin"), env.get("PATH", "")])})
    with fixed_scratch() as scratch:
        source = scratch / "source.rs"
        destination = scratch / "current.llbc"
        runs = []

        def extraction(label, source_fixture, expect_success=True, translate=True):
            source.write_bytes((FIXTURE / source_fixture).read_bytes())
            result = run([CHARON, "rustc", "--preset", "aeneas", "--dest-file", destination,
                          "--", source, "--crate-type", "lib", "--crate-name", "snapshot_probe",
                          "--edition", "2021"], scratch, env)
            artifact_dir = ARTIFACTS / label
            artifact_dir.mkdir()
            record = {"label": label, "source_fixture": source_fixture,
                      "source_sha256": sha(source), "charon": result,
                      "destination_exists": destination.exists(),
                      "destination_sha256": sha(destination) if destination.exists() else None}
            if expect_success:
                assert result["exit_code"] == 0 and destination.exists(), (label, result)
                copy = artifact_dir / "snapshot.llbc"
                shutil.copy2(destination, copy)
                data = json.loads(copy.read_text())
                record["llbc_sha256"] = sha(copy)
                record["llbc_bytes"] = copy.stat().st_size
                record["canonical_llbc_sha256"] = canonical_llbc(data)
                record["manifest"] = llbc_manifest(data)
                assert not data["has_errors"]
                if translate:
                    lean_dir = artifact_dir / "lean"
                    lean_dir.mkdir()
                    aeneas = run([AENEAS, "-backend", "lean", "-dest", lean_dir,
                                  "-no-progress-bar", "-split-files", "-gen-lib-entry", "-sequential",
                                  copy], scratch, env)
                    record["aeneas"] = aeneas
                    record["lean_inventory"] = inventory(lean_dir)
                    record["lean_manifest"] = lean_manifest(lean_dir)
                    assert aeneas["exit_code"] == 0 and record["lean_inventory"], (label, aeneas)
            runs.append(record)
            return record

        a1 = extraction("A1", "source-A.rs")
        a2 = extraction("A2", "source-A.rs")
        c = extraction("C-comment-only", "source-C-comment-only.rs")
        b = extraction("B", "source-B.rs")
        a3 = extraction("A3", "source-A.rs")
        before_failure_sha = sha(destination)
        bad = extraction("invalid-rust", "source-invalid.rs", expect_success=False)
        bad["prior_success_llbc_sha256"] = before_failure_sha
        assert bad["charon"]["exit_code"] != 0 and bad["destination_sha256"] == before_failure_sha
        # Charon's output after failure must be inspected, never assumed fresh.
        unsupported = extraction("unsupported-rust", "source-unsupported.rs", translate=False)
        unsupported_dir = ARTIFACTS / "unsupported-rust" / "lean"
        unsupported_dir.mkdir()
        unsupported_result = run([AENEAS, "-backend", "lean", "-dest", unsupported_dir,
                                  "-no-progress-bar", "-split-files", "-gen-lib-entry", "-sequential",
                                  ARTIFACTS / "unsupported-rust/snapshot.llbc"], scratch, env)
        unsupported["aeneas"] = unsupported_result
        unsupported["lean_inventory"] = inventory(unsupported_dir)
        unsupported["lean_manifest"] = lean_manifest(unsupported_dir)
        assert unsupported_result["exit_code"] != 0
        assert "sorry" in (unsupported_dir / "Funs.lean").read_text()
        assert "partial file" in unsupported_result["stdout"]
        raw_a1 = json.loads((ARTIFACTS / "A1/snapshot.llbc").read_text())
        raw_a2 = json.loads((ARTIFACTS / "A2/snapshot.llbc").read_text())
        raw_a3 = json.loads((ARTIFACTS / "A3/snapshot.llbc").read_text())
        a1_a2_differences = difference_paths(raw_a1, raw_a2)
        a1_a3_differences = difference_paths(raw_a1, raw_a3)
        assert all(p.startswith(("/translated/item_names/", "/translated/short_names/"))
                   for p in a1_a2_differences + a1_a3_differences)
        output = {"environment": {"python": sys.version, "platform": platform.platform(),
                                  "script_sha256": sha(__file__), "charon_sha256": sha(CHARON),
                                  "aeneas_sha256": sha(AENEAS),
                                  "rustc_version": run([RUST_BIN / "rustc", "--version", "--verbose"], scratch, env),
                                  "charon_version": run([CHARON, "version"], scratch, env),
                                  "aeneas_version": run([AENEAS, "-version"], scratch, env),
                                  "flags": ["--preset aeneas", "-backend lean", "-split-files",
                                            "-gen-lib-entry", "-sequential", "-no-progress-bar"]},
                  "runs": runs,
                  "comparisons": {
                      "A_sources_identical": a1["source_sha256"] == a2["source_sha256"] == a3["source_sha256"],
                      "A_lean_inventories_identical": a1["lean_inventory"] == a2["lean_inventory"] == a3["lean_inventory"],
                      "B_source_different": b["source_sha256"] != a1["source_sha256"],
                      "B_lean_inventory_different": b["lean_inventory"] != a1["lean_inventory"],
                      "C_source_different": c["source_sha256"] != a1["source_sha256"],
                      "C_canonical_llbc_different": c["canonical_llbc_sha256"] != a1["canonical_llbc_sha256"],
                      "C_lean_inventory_identical": c["lean_inventory"] == a1["lean_inventory"],
                      "A_canonical_llbc_identical": a1["canonical_llbc_sha256"] == a2["canonical_llbc_sha256"] == a3["canonical_llbc_sha256"],
                      "A1_A2_raw_difference_paths": a1_a2_differences,
                      "A1_A3_raw_difference_paths": a1_a3_differences,
                      "failed_charon_retained_prior_destination": bad["destination_sha256"] == before_failure_sha,
                      "unsupported_aeneas_emitted_sorry": "sorry" in (unsupported_dir / "Funs.lean").read_text(),
                  }}
        assert all(v for k, v in output["comparisons"].items() if not k.endswith("_paths")), output["comparisons"]
        handoff = handoff_manifest(runs)
    OUT.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    HANDOFF.write_text(json.dumps(handoff, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"A_raw_llbc": [r["llbc_sha256"] for r in (a1, a2, a3)],
                      "A_canonical_equal": output["comparisons"]["A_canonical_llbc_identical"],
                      "A_Lean_equal": output["comparisons"]["A_lean_inventories_identical"],
                      "invalid_rust_exit": bad["charon"]["exit_code"],
                      "unsupported_aeneas_exit": unsupported_result["exit_code"]}, sort_keys=True))


if __name__ == "__main__":
    main()
