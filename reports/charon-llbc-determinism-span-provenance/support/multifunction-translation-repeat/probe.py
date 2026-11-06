#!/usr/bin/env python3
"""Bounded Charon/Aeneas repeat probe for a five-function Rust corpus."""
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
FIX = ROOT / "fixture"
ART = ROOT / "artifacts"
LOG = ROOT / "logs"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
BIN = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
CHARON = TOOLS / "bin/charon"
AENEAS = TOOLS / "bin/aeneas"
LEAN_ROOT = TOOLS / "elan/toolchains/leanprover--lean4---v4.30.0-rc2"
LEAN = LEAN_ROOT / "bin/lean"
BACKEND = TOOLS / "aeneas-release/backends/lean"
PACKAGES = ("Cli", "batteries", "Qq", "aesop", "proofwidgets", "importGraph",
            "LeanSearchClient", "plausible", "mathlib")

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def invoke(label, argv, env, timeout=45, cwd=FIX):
    started = time.monotonic()
    p = subprocess.run([str(x) for x in argv], cwd=cwd, env=env,
                       capture_output=True, text=True, timeout=timeout)
    ended = time.monotonic()
    (LOG / (label + ".stdout")).write_text(p.stdout)
    (LOG / (label + ".stderr")).write_text(p.stderr)
    return {"label": label, "argv": [str(x) for x in argv], "cwd": str(cwd), "exit": p.returncode,
            "start_monotonic": started, "end_monotonic": ended,
            "elapsed_ms": round(1000 * (ended - started), 2),
            "stdout_sha256": digest(LOG / (label + ".stdout")),
            "stderr_sha256": digest(LOG / (label + ".stderr"))}

def charon(label, target, dest):
    env = dict(os.environ)
    env.update(RUSTUP_HOME=str(TOOLS / "rustup"), CARGO_HOME=str(TOOLS / "cargo"),
               CHARON_TOOLCHAIN_IS_IN_PATH="1", CARGO_BUILD_JOBS="1",
               CARGO_INCREMENTAL="0", RAYON_NUM_THREADS="1",
               CARGO_TARGET_DIR=str(target),
               PATH=os.pathsep.join([str(BIN), str(TOOLS / "bin"), env.get("PATH", "")]))
    row = invoke(label, [CHARON, "cargo", "--preset", "aeneas", "--dest-file", dest,
                         "--", "--manifest-path", FIX / "Cargo.toml", "--lib",
                         "--offline", "--locked", "-j", "1"], env)
    if row["exit"] != 0 or not dest.is_file():
        raise RuntimeError(f"{label}: Charon failed; see logs")
    return row

def aeneas(label, source, dest):
    dest.mkdir()
    row = invoke(label, [AENEAS, "-backend", "lean", "-no-progress-bar",
                         "-sequential", "-split-files", "-gen-lib-entry",
                         "-dest", dest, source], dict(os.environ))
    if row["exit"] != 0:
        raise RuntimeError(f"{label}: Aeneas failed; see logs")
    return row

def normalized(doc):
    doc = json.loads(json.dumps(doc))
    doc["translated"]["options"]["dest_file"] = "$DEST"
    names = doc["translated"]["short_names"]
    doc["translated"]["short_names"] = sorted(names, key=lambda x: json.dumps(x["key"], sort_keys=True))
    return doc

def lean_consumer(generated):
    consumer = ART / "consumer"
    (consumer / "Probe").mkdir(parents=True)
    shutil.copyfile(generated / "Types.lean", consumer / "Probe/Types.lean")
    shutil.copyfile(generated / "Funs.lean", consumer / "Probe/Funs.lean")
    shutil.copyfile(generated / "Probe.lean", consumer / "Probe.lean")
    (consumer / "Check.lean").write_text(
        "import Probe\n#check i148_corpus.add_one\n#check i148_corpus.choose\n"
        "#check i148_corpus.pair_sum\n#check i148_corpus.make_pair\n"
        "#check i148_corpus.combine\n#print axioms i148_corpus.combine\n")
    libs = [BACKEND / ".lake/packages" / name / ".lake/build/lib/lean" for name in PACKAGES]
    libs += [BACKEND / ".lake/build/lib/lean", LEAN_ROOT / "lib/lean"]
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(map(str, [consumer, *(p for p in libs if p.is_dir())]))
    rows = []
    for module in ("Probe/Types", "Probe/Funs", "Probe"):
        rows.append(invoke("lean-" + module.replace("/", "-"),
                           [LEAN, "-o", consumer / (module + ".olean"),
                            consumer / (module + ".lean")], env, timeout=60, cwd=consumer))
        assert rows[-1]["exit"] == 0, rows[-1]
    rows.append(invoke("lean-check", [LEAN, consumer / "Check.lean"], env, timeout=60, cwd=consumer))
    assert rows[-1]["exit"] == 0, rows[-1]
    return rows

def main():
    assert shutil.disk_usage(ROOT).free > 2 * (1 << 30)
    assert all(p.is_file() for p in (CHARON, AENEAS, LEAN, BIN / "cargo", BIN / "rustc"))
    assert not any(ART.iterdir()) and not any(LOG.iterdir()), "use a fresh package"
    source = {str(p.relative_to(FIX)): digest(p) for p in FIX.rglob("*") if p.is_file()}
    rows = []
    # Three source-unchanged warm requests with an identical LLBC destination path.
    same = ART / "same.llbc"
    for n in range(1, 4):
        rows.append(charon(f"charon-seq-{n}", ROOT / "target-seq", same))
        shutil.copyfile(same, ART / f"seq-{n}.llbc")
    # Two overlapping processes, one source path, private targets and destinations.
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        futs = [pool.submit(charon, f"charon-par-{n}", ROOT / f"target-par-{n}",
                            ART / f"par-{n}.llbc") for n in (1, 2)]
        rows.extend(f.result() for f in futs)
    llbc = [ART / f"seq-{n}.llbc" for n in (1, 2, 3)] + [ART / f"par-{n}.llbc" for n in (1, 2)]
    docs = [json.loads(p.read_bytes()) for p in llbc]
    assert all(doc["has_errors"] is False for doc in docs)
    assert all(normalized(doc) == normalized(docs[0]) for doc in docs)
    outputs = []
    for n, p in enumerate(llbc, 1):
        dest = ART / f"gen-{n}"
        copied = ART / f"input-{n}" / "probe.llbc"
        copied.parent.mkdir()
        shutil.copyfile(p, copied)
        assert digest(copied) == digest(p)
        rows.append(aeneas(f"aeneas-{n}", copied, dest))
        outputs.append(dest)
    inventories = [{str(p.relative_to(d)): digest(p) for p in d.rglob("*") if p.is_file()} for d in outputs]
    assert all(inv == inventories[0] for inv in inventories)
    assert all(source[str(p.relative_to(FIX))] == digest(p) for p in FIX.rglob("*") if p.is_file())
    lean = (outputs[0] / "Funs.lean").read_text()
    decls = [s.strip() for s in lean.splitlines() if re.match(r"^\s*(?:def|theorem|axiom|opaque|partial def)\s", s)]
    rows.extend(lean_consumer(outputs[0]))
    result = {"schema": 1, "tools": {p.name: digest(p) for p in (CHARON, AENEAS, LEAN, BIN / "cargo", BIN / "rustc")},
              "source": source, "runs": rows,
              "llbc": [{"file": p.name, "bytes": p.stat().st_size, "sha256": digest(p),
                        "short_names_count": len(d["translated"]["short_names"]),
                        "short_names_order": [x["key"] for x in d["translated"]["short_names"]]}
                       for p, d in zip(llbc, docs)],
              "all_core_llbc_equal_after_only_dest_and_short_name_order": True,
              "all_generated_file_inventories_equal": True,
              "generated_inventory": inventories[0], "lean_declarations": decls,
              "lean_obligation_markers": {s: lean.count(s) for s in ("sorry", "axiom", "theorem", "decreasing_by")}}
    (ROOT / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"runs": len(rows), "llbc_hashes": [x["sha256"][:12] for x in result["llbc"]],
                      "generated": inventories[0], "declarations": decls}, indent=2))

if __name__ == "__main__":
    main()
