#!/usr/bin/env python3
"""R43: feed R42's five fixed LLBC permutations to pinned Aeneas and Lean/Lake."""
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORK = HERE / "work"
CHECKOUT = HERE.parents[2]
R42 = CHECKOUT / "reports/anneal-3730-charon-warm-noop-byte-diff-2026-09-29/support"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
AENEAS = TOOLS / "bin/aeneas"
LEAN_ROOT = TOOLS / "elan/toolchains/leanprover--lean4---v4.30.0-rc2"
LEAN = LEAN_ROOT / "bin/lean"
LAKE = LEAN_ROOT / "bin/lake"
BACKEND = TOOLS / "aeneas-release/backends/lean"
PACKAGES = ["Cli", "batteries", "Qq", "aesop", "proofwidgets", "importGraph",
            "LeanSearchClient", "plausible", "mathlib"]
GENERATED = ("Types.lean", "FunsExternal_Template.lean", "Funs.lean", "Probe.lean")
RESULT = {"schema": 1, "commands": [], "cases": {}, "incremental": [], "limits": []}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def put(path, text):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)

def inventory(root, names):
    return {name: {"sha256": sha(root / name), "bytes": (root / name).stat().st_size,
                   "mtime_ns": (root / name).stat().st_mtime_ns} for name in names}

def run(label, argv, cwd, env=None, timeout=120):
    started = time.monotonic()
    p = subprocess.run(list(map(str, argv)), cwd=cwd, env=env, capture_output=True,
                       text=True, timeout=timeout)
    safe = re.sub(r"[^A-Za-z0-9_.-]", "_", label)
    logdir = HERE / "logs"
    logdir.mkdir(exist_ok=True)
    out, err = logdir / f"{safe}.stdout", logdir / f"{safe}.stderr"
    put(out, p.stdout)
    put(err, p.stderr)
    row = {"label": label, "argv": list(map(str, argv)), "cwd": str(cwd), "exit": p.returncode,
           "elapsed_ms": round((time.monotonic() - started) * 1000, 2),
           "stdout": str(out.relative_to(HERE)), "stderr": str(err.relative_to(HERE)),
           "stdout_sha256": sha(out), "stderr_sha256": sha(err)}
    RESULT["commands"].append(row)
    return row, p.stdout + p.stderr

def lean_env(extra):
    libs = [BACKEND / ".lake/packages" / name / ".lake/build/lib/lean" for name in PACKAGES]
    libs += [BACKEND / ".lake/build/lib/lean", LEAN_ROOT / "lib/lean"]
    e = dict(os.environ)
    e["LEAN_PATH"] = os.pathsep.join(map(str, [extra, *(p for p in libs if p.is_dir())]))
    return e

def sources_from_generated(generated, consumer):
    (consumer / "Probe").mkdir(parents=True)
    for name in ("Types.lean", "Funs.lean"):
        shutil.copyfile(generated / name, consumer / "Probe" / name)
    shutil.copyfile(generated / "FunsExternal_Template.lean",
                    consumer / "Probe/FunsExternal.lean")
    shutil.copyfile(generated / "Probe.lean", consumer / "Probe.lean")
    put(consumer / "Proof.lean",
        "import Probe\n#check r37u0.combined\n"
        "theorem combined_self (x : Aeneas.Std.U32) : "
        "r37u0.combined x = r37u0.combined x := by rfl\n"
        "#print axioms combined_self\n")

def direct_consumer(case, generated):
    consumer = case / "direct-consumer"
    sources_from_generated(generated, consumer)
    env = lean_env(consumer)
    rows = []
    for module in ("Probe/Types", "Probe/FunsExternal", "Probe/Funs", "Probe"):
        row, output = run(case.name + ":lean:" + module.replace("/", "_"),
                          [LEAN, "-o", module + ".olean", module + ".lean"], consumer, env)
        assert row["exit"] == 0, (row, output[-2000:])
        rows.append(row)
    row, output = run(case.name + ":lean:Proof", [LEAN, "Proof.lean"], consumer, env)
    assert row["exit"] == 0 and "combined_self" in output and "sorryAx" not in output, (row, output)
    rows.append(row)
    return {"commands": [x["label"] for x in rows],
            "source": inventory(consumer, ["Probe/Types.lean", "Probe/FunsExternal.lean",
                                           "Probe/Funs.lean", "Probe.lean", "Proof.lean"]),
            "olean": inventory(consumer, ["Probe/Types.olean", "Probe/FunsExternal.olean",
                                          "Probe/Funs.olean", "Probe.olean"]),
            "proof_output": output}

def lake_setup(consumer):
    a = str(BACKEND)
    put(consumer / "lakefile.lean", f'import Lake\nopen Lake DSL\nrequire aeneas from "{a}"\n'
        'package r43_probe\n@[default_target]\nlean_lib Probe\n')
    parent_manifest = json.loads((BACKEND / "lake-manifest.json").read_text())
    parent_manifest["packages"].append({"type": "path", "scope": "", "name": "aeneas",
        "manifestFile": "lake-manifest.json", "inherited": False, "dir": a,
        "configFile": "lakefile.lean"})
    parent_manifest["name"] = "r43_probe"
    put(consumer / "lake-manifest.json", json.dumps(parent_manifest, indent=2) + "\n")
    packages = consumer / ".lake/packages"
    packages.parent.mkdir(exist_ok=True)
    packages.symlink_to(BACKEND / ".lake/packages", target_is_directory=True)

def lake_build(label, consumer):
    row, output = run(label, [LAKE, "build", "-v"], consumer, timeout=90)
    assert row["exit"] == 0, (row, output[-4000:])
    own = [line for line in output.splitlines() if re.search(r"\b(?:Built|Replayed) Probe(?:\.|\s|$)", line)]
    traces = {}
    base = consumer / ".lake/build"
    for module in ("Probe/Types", "Probe/FunsExternal", "Probe/Funs", "Probe"):
        paths = [base / "lib/lean" / (module + ".olean"),
                 base / "lib/lean" / (module + ".trace")]
        for p in paths:
            assert p.is_file(), p
            traces[str(p.relative_to(base))] = {"sha256": sha(p), "mtime_ns": p.stat().st_mtime_ns,
                                                 "bytes": p.stat().st_size}
    return {"command": row["label"], "own_job_lines": own, "artifacts": traces}

def declaration_summary(generated):
    out = {}
    for name in GENERATED:
        source = (generated / name).read_text()
        out[name] = {"decl_lines": [line for line in source.splitlines()
                                    if re.match(r"^(?:def|theorem|axiom|opaque|inductive|structure|class)\b", line)],
                     "imports": [line for line in source.splitlines() if line.startswith("import ")]}
    return out

def main():
    assert shutil.disk_usage(HERE).free > 5 * 1024**3
    for path in (AENEAS, LEAN, LAKE, BACKEND / ".lake/build/lib/lean/Aeneas.olean"):
        assert path.is_file(), path
    assert len(list((R42 / "artifacts").glob("run-*.llbc"))) == 5
    RESULT["tools"] = {str(p): sha(p) for p in (AENEAS, LEAN, LAKE,
                       BACKEND / ".lake/build/lib/lean/Aeneas.olean",
                       BACKEND / "lake-manifest.json")}
    RESULT["r42_report_sha256"] = sha(R42.parent / "REPORT.md")
    if WORK.exists():
        shutil.rmtree(WORK)
    if (HERE / "logs").exists():
        shutil.rmtree(HERE / "logs")
    WORK.mkdir()
    for number in range(1, 6):
        label = f"run-{number}"
        case = WORK / label
        generated = case / "generated"
        generated.mkdir(parents=True)
        source = R42 / "artifacts" / f"{label}.llbc"
        llbc = case / "probe.llbc"
        shutil.copyfile(source, llbc)
        assert sha(llbc) == sha(source)
        row, output = run(label + ":aeneas", [AENEAS, "-backend", "lean",
            "-no-progress-bar", "-sequential", "-split-files", "-gen-lib-entry",
            "-dest", generated, llbc], case, timeout=90)
        assert row["exit"] == 0 and all((generated / n).is_file() for n in GENERATED), (row, output)
        direct = direct_consumer(case, generated)
        lake = case / "lake-consumer"
        sources_from_generated(generated, lake)
        lake_setup(lake)
        built = lake_build(label + ":lake:fresh", lake)
        RESULT["cases"][label] = {"r42_llbc_sha256": sha(source), "copied_llbc_sha256": sha(llbc),
            "aeneas_command": row["label"], "generated": inventory(generated, GENERATED),
            "declarations": declaration_summary(generated), "direct": direct,
            "lake_fresh": built}
        # Avoid retaining a symlink into the cached dependency tree; the runner recreates it.
        (lake / ".lake/packages").unlink()
    # Same consumer/path control: no source rewrite, then replace generated source bytes from each
    # permutation at the same path and ask Lake which local jobs it replays or rebuilds.
    shared = WORK / "run-1/lake-consumer"
    (shared / ".lake/packages").symlink_to(BACKEND / ".lake/packages", target_is_directory=True)
    RESULT["incremental"].append({"input": "no-write", "lake": lake_build("incremental:no-write", shared)})
    for number in range(2, 6):
        label = f"run-{number}"
        generated = WORK / label / "generated"
        for name in ("Types.lean", "Funs.lean"):
            shutil.copyfile(generated / name, shared / "Probe" / name)
        shutil.copyfile(generated / "FunsExternal_Template.lean", shared / "Probe/FunsExternal.lean")
        shutil.copyfile(generated / "Probe.lean", shared / "Probe.lean")
        RESULT["incremental"].append({"input": label, "source_hashes":
            inventory(shared, ["Probe/Types.lean", "Probe/FunsExternal.lean",
                               "Probe/Funs.lean", "Probe.lean"]),
            "lake": lake_build("incremental:" + label, shared)})
    (shared / ".lake/packages").unlink()
    RESULT["comparison"] = {"raw_llbc_distinct": len({x["r42_llbc_sha256"]
        for x in RESULT["cases"].values()}), "generated_hash_groups":
        {name: sorted({x["generated"][name]["sha256"] for x in RESULT["cases"].values()})
         for name in GENERATED}, "decl_groups": {name: sorted({json.dumps(x["declarations"][name], sort_keys=True)
         for x in RESULT["cases"].values()}) for name in GENERATED}}
    RESULT["limits"] = ["Aeneas is a one-shot CLI, not the same-process OCaml API.",
        "The two path-dependency functions use generated axiom templates as external Lean contracts.",
        "This fixture isolates short_names order only; it does not license whole-LLBC normalization.",
        "Lake uses a private consumer with a path dependency and symlink to already cached Aeneas packages; no dependency was downloaded.",
        "Fresh batch acceptance checks elaboration/type preservation, not a semantic refinement proof of the Rust functions."]
    put(HERE / "results.json", json.dumps(RESULT, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"cases": list(RESULT["cases"]), "comparison": RESULT["comparison"],
        "commands": len(RESULT["commands"])}))

if __name__ == "__main__":
    main()
