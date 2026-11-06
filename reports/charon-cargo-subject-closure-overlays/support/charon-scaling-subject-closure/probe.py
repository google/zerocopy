#!/usr/bin/env python3
"""Bounded offline Cargo/Charon workspace, root, and input-closure matrix."""

import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
FIX = HERE / "fixture"
ART = HERE / "artifacts"
RAW = HERE / "raw-results.json"
GRAPHS = HERE / "unit-graphs.json"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
RUST_BIN = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
RUST_LIB = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/lib"
CHARON = TOOLS / "bin/charon"
CARGO = RUST_BIN / "cargo"
RUSTC = RUST_BIN / "rustc"


def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()


def sha(path):
    return sha_bytes(path.read_bytes())


def make_fixture(count):
    if FIX.exists():
        shutil.rmtree(FIX)
    (FIX / "shared/src").mkdir(parents=True)
    (FIX / "app/src").mkdir(parents=True)
    (FIX / "Cargo.toml").write_text('[workspace]\nmembers = ["app", "shared"]\nresolver = "2"\n')
    (FIX / "shared/Cargo.toml").write_text('[package]\nname = "shared_closure"\nversion = "0.1.0"\nedition = "2021"\n')
    (FIX / "shared/src/lib.rs").write_text('pub fn dep(x: u32) -> u32 { x.wrapping_add(11) }\n')
    (FIX / "app/Cargo.toml").write_text('[package]\nname = "app_closure"\nversion = "0.1.0"\nedition = "2021"\nbuild = "build.rs"\n[features]\ndefault = []\nselected = []\n[dependencies]\nshared_closure = { path = "../shared" }\n')
    (FIX / "app/build.rs").write_text('use std::{env, fs, path::PathBuf};\nfn main() {\n  println!("cargo:rerun-if-env-changed=BUILD_VALUE");\n  let value = env::var("BUILD_VALUE").unwrap_or_else(|_| "7".to_owned());\n  let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());\n  fs::write(out.join("generated.rs"), format!("pub const BUILD_VALUE: u32 = {value};\\n")).unwrap();\n}\n')
    (FIX / "app/src/payload.txt").write_text("payload-A\n")
    lines = ["include!(concat!(env!(\"OUT_DIR\"), \"/generated.rs\"));",
             'pub fn payload_len() -> usize { include_str!("payload.txt").len() }',
             '#[cfg(feature = "selected")] pub fn selected() -> u32 { BUILD_VALUE }',
             '#[cfg(not(feature = "selected"))] pub fn default_only() -> u32 { 0 }']
    for i in range(count):
        lines.append(f'pub fn leaf_{i:03}(x: u32) -> u32 {{ x.wrapping_add({i}) }}')
    for i in range(count):
        lines.append(f'pub fn node_{i:03}(x: u32) -> u32 {{ leaf_{i:03}(x).wrapping_add(shared_closure::dep(x)) }}')
    for i in range(count):
        lines.append(f'pub fn root_{i:03}(x: u32) -> u32 {{ node_{i:03}(x).wrapping_add(BUILD_VALUE) }}')
    (FIX / "app/src/lib.rs").write_text("\n".join(lines) + "\n")
    env = base_env()
    lock = subprocess.run([str(CARGO), "generate-lockfile", "--offline", "--manifest-path", str(FIX / "Cargo.toml")], cwd=FIX, env=env, capture_output=True, text=True, timeout=30)
    if lock.returncode:
        raise RuntimeError(lock.stderr)


def base_env():
    env = dict(os.environ)
    env.update({
        "RUSTUP_HOME": str(TOOLS / "rustup"), "CARGO_HOME": str(TOOLS / "cargo"),
        "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "CARGO_BUILD_JOBS": "1",
        "CARGO_INCREMENTAL": "0", "RAYON_NUM_THREADS": "1",
        "PATH": os.pathsep.join([str(RUST_BIN), str(TOOLS / "bin"), env.get("PATH", "")]),
        "DYLD_LIBRARY_PATH": os.pathsep.join([str(RUST_LIB), str(RUST_LIB / "rustlib/aarch64-apple-darwin/lib"), env.get("DYLD_LIBRARY_PATH", "")]),
    })
    return env


def hashes():
    return {str(p.relative_to(FIX)): sha(p) for p in sorted(FIX.rglob("*")) if p.is_file()}


def normalize(text, target):
    return text.replace(str(FIX), "$FIX").replace(str(target), "$TARGET").replace(str(HERE), "$REPORT")


def rss_sample(root_pid):
    p = subprocess.run(["/bin/ps", "-axo", "pid=,ppid=,rss="], capture_output=True, text=True)
    rel = {}
    for line in p.stdout.splitlines():
        f = line.split()
        if len(f) == 3 and all(x.isdigit() for x in f):
            pid, ppid, rss = map(int, f)
            rel[pid] = (ppid, rss)
    active = {root_pid}
    changed = True
    while changed:
        before = len(active)
        active.update(pid for pid, (ppid, _) in rel.items() if ppid in active)
        changed = len(active) != before
    values = [rel[pid][1] for pid in active if pid in rel]
    return (sum(values), max(values, default=0), len(values))


def run(argv, label, target, env, timeout=120):
    start = time.monotonic()
    proc = subprocess.Popen([str(x) for x in argv], cwd=FIX, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    max_tree = max_one = max_count = samples = 0
    while proc.poll() is None:
        tree, one, count = rss_sample(proc.pid)
        max_tree = max(max_tree, tree)
        max_one = max(max_one, one)
        max_count = max(max_count, count)
        samples += 1
        if time.monotonic() - start > timeout:
            proc.kill()
            raise TimeoutError(label)
        time.sleep(0.02)
    stdout, stderr = proc.communicate(timeout=10)
    return {"argv": [normalize(str(x), target) for x in argv], "exit": proc.returncode,
            "wall_seconds": round(time.monotonic() - start, 4), "samples": samples,
            "sampled_tree_rss_kib_upper": max_tree, "sampled_process_rss_kib_upper": max_one,
            "max_sampled_processes": max_count,
            "stdout": normalize(stdout, target), "stderr": normalize(stderr, target)}


def item_name(parts):
    return "::".join(p["Ident"][0] if "Ident" in p else "<" + next(iter(p)) + ">" for p in parts)


def llbc_projection(path):
    raw = json.loads(path.read_text())
    tr = raw["translated"]
    locals_ = []
    foreign = []
    for entry in tr["fun_decls"]:
        if not entry:
            continue
        meta = entry.get("item_meta") or {}
        body = entry.get("body")
        item = {"id": entry["def_id"], "name": item_name(meta.get("name", [])), "is_local": meta.get("is_local"), "span": meta.get("span"),
                "body_present": body is not None,
                "body_kind": body if isinstance(body, str) else next(iter(body)) if isinstance(body, dict) else None,
                "body_sha256": sha_bytes(json.dumps(body, sort_keys=True, separators=(",", ":")).encode()) if body is not None else None,
                "source_text": meta.get("source_text") if item_name(meta.get("name", [])).endswith(("BUILD_VALUE", "payload_len")) else None}
        (locals_ if item["is_local"] else foreign).append(item)
    return {"has_errors": raw["has_errors"], "crate_name": tr["crate_name"], "llbc_bytes": path.stat().st_size,
            "llbc_sha256": sha(path), "ordered_decls": len(tr.get("ordered_decls", [])),
            "local_functions": locals_, "foreign_functions": foreign,
            "file_manifest": [{"name": f.get("name"), "crate_name": f.get("crate_name"), "contents_sha256": sha_bytes(f["contents"].encode()) if f.get("contents") is not None else None} for f in tr.get("files", [])]}


def main():
    if shutil.disk_usage(HERE).free < 15 * (1 << 30):
        raise RuntimeError("disk guard: under 15 GiB free")
    ART.mkdir(exist_ok=True)
    records = []
    env = base_env()
    for count in (24, 192):
        make_fixture(count)
        # One selected root, a set of roots, and a full selected library.
        modes = [("one", 1), ("many", 8 if count == 24 else 32), ("whole", None)]
        if count == 192:
            modes += [("feature", None), ("build-env", None), ("payload", None)]
        for mode, roots in modes:
            if mode == "payload":
                (FIX / "app/src/payload.txt").write_text("payload-BBBBB\n")
            target = Path(tempfile.mkdtemp(prefix="charon-target-"))
            output = ART / f"n{count}-{mode}.llbc"
            output.unlink(missing_ok=True)
            flags = ["--preset", "aeneas", "--dest-file", output]
            if roots is not None:
                for i in range(roots):
                    flags += ["--start-from", f"crate::root_{i:03}"]
            cargo = ["--manifest-path", FIX / "Cargo.toml", "--package", "app_closure", "--lib", "--offline", "--locked"]
            if mode == "feature":
                cargo += ["--features", "selected"]
            argv = [CHARON, "cargo", *flags, "--", *cargo]
            case_env = dict(env, CARGO_TARGET_DIR=str(target), BUILD_VALUE="9" if mode == "build-env" else "7")
            try:
                invocation = run(argv, f"n{count}-{mode}", target, case_env)
                result = {"case": f"n{count}-{mode}", "function_count": count, "roots": roots,
                          "feature_selected": mode == "feature", "build_value": case_env["BUILD_VALUE"],
                          "input_hashes": hashes(), "target_size_bytes": sum(p.stat().st_size for p in target.rglob("*") if p.is_file()),
                          "invocation": invocation}
                if output.exists():
                    result["llbc"] = llbc_projection(output)
                records.append(result)
                RAW.write_text(json.dumps({"records": records}, indent=2, sort_keys=True) + "\n")
                if invocation["exit"] != 0 or not output.exists() or result["llbc"]["has_errors"]:
                    raise RuntimeError(f"failed {result['case']}: {invocation['stderr'][-1000:]}")
            finally:
                shutil.rmtree(target)
        if count == 24:
            (HERE / "fixture-24-lib.rs").write_bytes((FIX / "app/src/lib.rs").read_bytes())
        else:
            (HERE / "fixture-192-lib.rs").write_bytes((FIX / "app/src/lib.rs").read_bytes())
    # The same workspace can select its dependency crate as the primary unit.
    # Also preserve what a multi-package selection does at this Charon pin.
    for mode, selection in (("shared-lib", ["--package", "shared_closure", "--lib"]),
                            ("workspace-libs", ["--workspace", "--lib"])):
        target = Path(tempfile.mkdtemp(prefix="charon-target-"))
        output = ART / f"n192-{mode}.llbc"
        output.unlink(missing_ok=True)
        argv = [CHARON, "cargo", "--preset", "aeneas", "--dest-file", output, "--",
                "--manifest-path", FIX / "Cargo.toml", *selection, "--offline", "--locked"]
        case_env = dict(env, CARGO_TARGET_DIR=str(target), BUILD_VALUE="7")
        try:
            invocation = run(argv, f"n192-{mode}", target, case_env)
            result = {"case": f"n192-{mode}", "function_count": 192, "roots": None,
                      "feature_selected": False, "build_value": "7", "input_hashes": hashes(),
                      "target_size_bytes": sum(p.stat().st_size for p in target.rglob("*") if p.is_file()),
                      "invocation": invocation}
            if output.exists():
                result["llbc"] = llbc_projection(output)
            records.append(result)
            RAW.write_text(json.dumps({"records": records}, indent=2, sort_keys=True) + "\n")
            if mode == "shared-lib" and (invocation["exit"] != 0 or not output.exists() or result["llbc"]["has_errors"]):
                raise RuntimeError(f"failed {mode}: {invocation['stderr'][-1000:]}")
        finally:
            shutil.rmtree(target)
    metadata = subprocess.run([str(CARGO), "metadata", "--no-deps", "--format-version", "1", "--offline", "--manifest-path", str(FIX / "Cargo.toml")], cwd=FIX, env=env, capture_output=True, text=True, timeout=30)
    assert metadata.returncode == 0, metadata.stderr
    md = json.loads(metadata.stdout)
    packages = [{"name": p["name"], "version": p["version"], "manifest_path": normalize(p["manifest_path"], Path("/unused")),
                 "targets": [{"name": t["name"], "kind": t["kind"], "src_path": normalize(t["src_path"], Path("/unused"))} for t in p["targets"]],
                 "dependencies": [{"name": d["name"], "path": normalize(d["path"], Path("/unused")) if d.get("path") else None} for d in p["dependencies"]]} for p in md["packages"]]
    unit_graphs = {}
    for label, selection in (("app-default", ["--package", "app_closure", "--lib"]),
                             ("app-selected", ["--package", "app_closure", "--lib", "--features", "selected"]),
                             ("shared-lib", ["--package", "shared_closure", "--lib"]),
                             ("workspace-libs", ["--workspace", "--lib"])):
        graph_cmd = [str(CARGO), "-Z", "unstable-options", "build", "--unit-graph", "--offline", "--locked",
                     "--manifest-path", str(FIX / "Cargo.toml"), *selection]
        graph_out = subprocess.run(graph_cmd, cwd=FIX, env=env, capture_output=True, text=True, timeout=30)
        if graph_out.returncode:
            raise RuntimeError(f"unit graph {label}: {graph_out.stderr}")
        unit_graphs[label] = json.loads(graph_out.stdout.replace(str(FIX), "$FIX"))
    GRAPHS.write_text(json.dumps(unit_graphs, indent=2, sort_keys=True) + "\n")
    by_case = {r["case"]: r for r in records}
    assert {k: len(by_case[k]["llbc"]["local_functions"]) for k in
            ("n24-one", "n24-many", "n24-whole", "n192-one", "n192-many", "n192-whole")} == {
                "n24-one": 4, "n24-many": 25, "n24-whole": 75,
                "n192-one": 4, "n192-many": 97, "n192-whole": 579}
    def names(case):
        return {f["name"] for f in by_case[case]["llbc"]["local_functions"]}
    assert "app_closure::default_only" in names("n192-whole")
    assert "app_closure::selected" not in names("n192-whole")
    assert "app_closure::selected" in names("n192-feature")
    assert "app_closure::default_only" not in names("n192-feature")
    assert any(f["name"] == "shared_closure::dep" and f["body_kind"] == "Opaque" for f in by_case["n192-one"]["llbc"]["foreign_functions"])
    assert by_case["n192-whole"]["input_hashes"]["app/src/lib.rs"] == by_case["n192-build-env"]["input_hashes"]["app/src/lib.rs"]
    assert by_case["n192-whole"]["input_hashes"]["app/src/lib.rs"] == by_case["n192-payload"]["input_hashes"]["app/src/lib.rs"]
    def body_hash(case, short):
        return next(f["body_sha256"] for f in by_case[case]["llbc"]["local_functions"] if f["name"].endswith("::" + short))
    assert body_hash("n192-whole", "BUILD_VALUE") != body_hash("n192-build-env", "BUILD_VALUE")
    assert body_hash("n192-whole", "payload_len") != body_hash("n192-payload", "payload_len")
    assert by_case["n192-shared-lib"]["llbc"]["crate_name"] == "shared_closure"
    assert by_case["n192-workspace-libs"]["invocation"]["exit"] == 101
    assert by_case["n192-workspace-libs"]["llbc"]["crate_name"] == "shared_closure"
    assert "extern location for shared_closure does not exist" in by_case["n192-workspace-libs"]["invocation"]["stderr"]
    data = {"environment": {"platform": platform.platform(), "charon_sha256": sha(CHARON), "cargo_sha256": sha(CARGO), "rustc_sha256": sha(RUSTC),
                             "cargo_version": subprocess.check_output([str(CARGO), "--version"], env=env, text=True).strip(), "rustc_version": subprocess.check_output([str(RUSTC), "--version"], env=env, text=True).strip()},
            "workspace_packages": packages, "unit_graph_summary": {k: {"unit_count": len(v["units"]), "root_indices": v["roots"], "units": [{"package": u["pkg_id"].split("#")[-1], "target": u["target"]["name"], "kind": u["target"]["kind"], "mode": u["mode"], "features": u["features"]} for u in v["units"]]} for k, v in unit_graphs.items()},
            "final_fixture_hashes": hashes(), "records": records}
    RAW.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"cases": len(records), "exits": [x["invocation"]["exit"] for x in records],
                      "local_counts": [len(x.get("llbc", {}).get("local_functions", [])) for x in records],
                      "foreign_counts": [len(x.get("llbc", {}).get("foreign_functions", [])) for x in records]}, sort_keys=True))


if __name__ == "__main__":
    main()
