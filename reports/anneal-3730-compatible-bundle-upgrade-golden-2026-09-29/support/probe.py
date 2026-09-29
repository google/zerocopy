#!/usr/bin/env python3
"""Replay one Rust golden across two cached compatible Charon/Aeneas bundles.

Only support/work and support/results.json in this report package are replaced.
No package manager, network fetch, or tool installation is used.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORK = HERE / "work"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
LEAN_ROOT = TOOLS / "elan/toolchains/leanprover--lean4---v4.30.0-rc2"
LEAN = LEAN_ROOT / "bin/lean"
OLD = TOOLS / "scratch/20260928-reference-open-checks/aeneas_revision/old"
NEW = TOOLS / "aeneas-release"
PACKAGES = ("Cli", "batteries", "Qq", "aesop", "proofwidgets", "importGraph",
            "LeanSearchClient", "plausible", "mathlib")
BUNDLES = {
    "june1": {"root": OLD, "rust": "nightly-2026-04-18-aarch64-apple-darwin",
              "aeneas_commit": "f95a80abaf554d4612cb60ef9ec8e849139bec44",
              "charon_pin": "42836b36b666a980cbc9d438a8aed340ad3b848b"},
    "june3": {"root": NEW, "rust": "nightly-2026-05-31-aarch64-apple-darwin",
              "aeneas_commit": "ac9f1bc5262a5e4ff1e24ca78617121382202727",
              "charon_pin": "a535e914f74db4fd9e6be7048f4233270d8945c0"},
}
RESULT = {"schema": 1, "bundles": {}, "cases": {}, "cross_pair": {}, "commands": [], "comparisons": {},
          "freshness_controls": {}, "parallel_option": {}, "limits": []}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(root: Path) -> dict:
    return {p.relative_to(root).as_posix(): {"bytes": p.stat().st_size, "sha256": sha(p)}
            for p in sorted(root.rglob("*")) if p.is_file()}


def run(label: str, argv: list, cwd: Path, env: dict | None = None, timeout: int = 180) -> dict:
    command = [str(a) for a in argv]
    p = subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True, timeout=timeout)
    record = {"label": label, "argv": command, "cwd": str(cwd), "exit": p.returncode,
              "stdout": p.stdout, "stderr": p.stderr}
    RESULT["commands"].append(record)
    return record


def rust_env(bundle: dict, target: Path) -> dict:
    rustbin = TOOLS / "rustup/toolchains" / bundle["rust"] / "bin"
    env = dict(os.environ)
    env.update({"RUSTUP_HOME": str(TOOLS / "rustup"), "CARGO_HOME": str(TOOLS / "cargo"),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "CARGO_BUILD_JOBS": "1",
                "CARGO_INCREMENTAL": "0", "CARGO_NET_OFFLINE": "true",
                "CARGO_TARGET_DIR": str(target),
                "PATH": os.pathsep.join((str(rustbin), str(bundle["root"]), env.get("PATH", "")))})
    env["DYLD_LIBRARY_PATH"] = os.pathsep.join((
        str(rustbin.parent / "lib"),
        str(rustbin.parent / "lib/rustlib/aarch64-apple-darwin/lib"),
        env.get("DYLD_LIBRARY_PATH", "")))
    return env


def lean_env(consumer: Path, bundle: dict) -> dict:
    backend = bundle["root"] / "backends/lean"
    cached = NEW / "backends/lean/.lake/packages"
    libs = [consumer, backend / ".lake/build/lib/lean"]
    libs += [cached / p / ".lake/build/lib/lean" for p in PACKAGES]
    libs += [LEAN_ROOT / "lib/lean"]
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in libs if p.is_dir())
    env["LEAN_NUM_THREADS"] = "1"
    return env


def proof_source(values: tuple[int, int, int]) -> str:
    lines = ["import Current"]
    for name, value in zip(("inc", "twice", "choose"), values):
        lines.append(f"theorem obl_{name} : bundle_golden.{name} 0#u32 = .ok {value}#u32 := by rfl")
        lines.append(f"#print axioms obl_{name}")
    return "\n".join(lines) + "\n"


def test_source(values: tuple[int, int, int]) -> str:
    return ("use bundle_golden::{inc, twice, choose};\n"
            "#[test] fn selected_values() {\n"
            f"    assert_eq!(inc(0), {values[0]});\n"
            f"    assert_eq!(twice(0), {values[1]});\n"
            f"    assert_eq!(choose(0), {values[2]});\n"
            "}\n")


def case(bundle_name: str, variant: str) -> None:
    bundle = BUNDLES[bundle_name]
    key = f"{bundle_name}-{variant}"
    base = WORK / key
    crate = base / "crate"
    shutil.copytree(HERE / "fixture", crate)
    values = (1, 2, 3) if variant == "base" else (2, 4, 5)
    if variant == "changed":
        source = crate / "src/lib.rs"
        source.write_text(source.read_text().replace("wrapping_add(1)", "wrapping_add(2)"))
        (crate / "tests/behavior.rs").write_text(test_source(values))
    target = base / "target"
    env = rust_env(bundle, target)
    rustbin = TOOLS / "rustup/toolchains" / bundle["rust"] / "bin"
    lock = run(key + ":lock", [rustbin / "cargo", "generate-lockfile", "--offline"], crate, env)
    assert lock["exit"] == 0, lock
    llbc = base / "current.llbc"
    charon = run(key + ":charon",
                 [bundle["root"] / "charon", "cargo", "--preset", "aeneas", "--dest-file", llbc,
                  "--", "--manifest-path", crate / "Cargo.toml", "--lib", "--offline", "--locked", "-j", "1"],
                 base, env, 300)
    assert charon["exit"] == 0 and llbc.is_file(), charon
    obj = json.loads(llbc.read_text())
    assert obj["has_errors"] is False
    generated = base / "generated"
    generated.mkdir()
    aeneas = run(key + ":aeneas",
                 [bundle["root"] / "aeneas", "-backend", "lean", "-no-progress-bar", "-sequential",
                  "-split-files", "-gen-lib-entry", "-dest", generated, llbc], base, timeout=180)
    assert aeneas["exit"] == 0, aeneas
    assert {p.name for p in generated.iterdir()} == {"Types.lean", "Funs.lean", "Current.lean"}
    behavior = run(key + ":rust-test", [rustbin / "cargo", "test", "--offline", "--locked", "--test", "behavior"], crate, env, 300)
    assert behavior["exit"] == 0 and "1 passed" in behavior["stdout"], behavior
    consumer = base / "consumer"
    (consumer / "Current").mkdir(parents=True)
    for name in ("Types", "Funs"):
        shutil.copyfile(generated / f"{name}.lean", consumer / "Current" / f"{name}.lean")
    shutil.copyfile(generated / "Current.lean", consumer / "Current.lean")
    le = lean_env(consumer, bundle)
    for module in ("Current/Types", "Current/Funs", "Current"):
        response = run(key + ":lean-compile:" + module,
                       [LEAN, "-o", module + ".olean", module + ".lean"], consumer, le)
        assert response["exit"] == 0, response
    (consumer / "Proof.lean").write_text(proof_source(values))
    proof = run(key + ":lean-proof", [LEAN, "--json", "Proof.lean"], consumer, le)
    assert proof["exit"] == 0 and "sorryAx" not in proof["stdout"], proof
    for name in ("obl_inc", "obl_twice", "obl_choose"):
        assert name in proof["stdout"], (key, name, proof)
    (consumer / "Wrong.lean").write_text(
        "import Current\ntheorem wrong_inc : bundle_golden.inc 0#u32 = .ok 99#u32 := by rfl\n")
    wrong = run(key + ":wrong-claim", [LEAN, "--json", "Wrong.lean"], consumer, le)
    assert wrong["exit"] != 0, wrong
    (consumer / "Missing.lean").write_text(
        "import Current\ntheorem obl_inc : bundle_golden.inc 0#u32 = .ok "
        f"{values[0]}#u32 := by rfl\n")
    missing = run(key + ":missing-obligations", [LEAN, "--json", "Missing.lean"], consumer, le)
    assert missing["exit"] == 0, missing
    (consumer / "Admitted.lean").write_text(
        "import Current\ntheorem admitted : bundle_golden.inc 0#u32 = .ok 99#u32 := by sorry\n#print axioms admitted\n")
    admitted = run(key + ":admitted", [LEAN, "--json", "Admitted.lean"], consumer, le)
    assert admitted["exit"] == 0 and "sorryAx" in admitted["stdout"], admitted
    RESULT["cases"][key] = {
        "bundle": bundle_name, "variant": variant, "rust_values": values,
        "source_sha256": sha(crate / "src/lib.rs"), "llbc_sha256": sha(llbc),
        "charon_version": obj["charon_version"], "llbc_function_names": [
            d["item_meta"]["name"][-1].get("Ident", [None])[0] for d in obj["translated"]["fun_decls"] if d],
        "generated": inventory(generated), "consumer": inventory(consumer),
        "proof_stdout": proof["stdout"], "proof_exit": proof["exit"],
        "wrong_claim_exit": wrong["exit"], "missing_obligations_exit": missing["exit"],
        "admitted_exit": admitted["exit"], "admitted_has_sorryAx": "sorryAx" in admitted["stdout"],
        "target_bytes_before_cleanup": sum(p.stat().st_size for p in target.rglob("*") if p.is_file()),
    }
    shutil.rmtree(target)


def main() -> None:
    assert shutil.disk_usage(HERE).free > 15 * 1024**3
    assert LEAN.is_file()
    for name, bundle in BUNDLES.items():
        root = bundle["root"]
        rustbin = TOOLS / "rustup/toolchains" / bundle["rust"] / "bin"
        for path in (root / "aeneas", root / "charon", root / "charon-driver", rustbin / "rustc", rustbin / "cargo",
                     root / "backends/lean/.lake/build/lib/lean/Aeneas.olean"):
            assert path.is_file(), path
        RESULT["bundles"][name] = {"aeneas_commit": bundle["aeneas_commit"],
            "charon_pin": bundle["charon_pin"], "rust_toolchain": bundle["rust"],
            "binary_sha256": {p: sha(root / p) for p in ("aeneas", "charon", "charon-driver")},
            "rustc_sha256": sha(rustbin / "rustc"), "cargo_sha256": sha(rustbin / "cargo"),
            "lean_sha256": sha(LEAN),
            "aeneas_olean_sha256": sha(root / "backends/lean/.lake/build/lib/lean/Aeneas.olean")}
    if WORK.exists():
        shutil.rmtree(WORK)
    WORK.mkdir()
    for name in BUNDLES:
        for variant in ("base", "changed"):
            case(name, variant)
    for name, bundle in BUNDLES.items():
        base = WORK / f"{name}-base"
        old_consumer = base / "consumer"
        stale = run(name + ":stale-base-proof-after-source-change",
                    [LEAN, "--json", "Proof.lean"], old_consumer, lean_env(old_consumer, bundle))
        assert stale["exit"] == 0 and RESULT["cases"][name + "-base"]["source_sha256"] != \
               RESULT["cases"][name + "-changed"]["source_sha256"]
        RESULT["freshness_controls"][name] = {"stale_batch_exit": stale["exit"],
            "old_import_source_sha256": RESULT["cases"][name + "-base"]["source_sha256"],
            "current_source_sha256": RESULT["cases"][name + "-changed"]["source_sha256"],
            "source_identity_gate_rejects": True}
        sequential = RESULT["cases"][name + "-base"]["generated"]
        outputs = []
        for index in (1, 2):
            dest = WORK / f"{name}-default-parallel-{index}"
            dest.mkdir()
            response = run(f"{name}:default-parallel:{index}",
                [bundle["root"] / "aeneas", "-backend", "lean", "-no-progress-bar",
                 "-split-files", "-gen-lib-entry", "-dest", dest, base / "current.llbc"], dest)
            assert response["exit"] == 0, response
            outputs.append(inventory(dest))
        RESULT["parallel_option"][name] = {"default_runs": outputs,
            "two_defaults_equal": outputs[0] == outputs[1],
            "default_equals_sequential": outputs[0] == sequential}
    for consumer, producer in (("june1", "june3"), ("june3", "june1")):
        label = f"{consumer}-on-{producer}-llbc"
        dest = WORK / label
        dest.mkdir()
        response = run(label, [BUNDLES[consumer]["root"] / "aeneas", "-backend", "lean", "-no-progress-bar",
                 "-sequential", "-split-files", "-gen-lib-entry", "-dest", dest,
                 WORK / f"{producer}-base/current.llbc"], dest)
        RESULT["cross_pair"][label] = {"exit": response["exit"], "stdout": response["stdout"],
                                       "stderr": response["stderr"], "inventory": inventory(dest)}
        assert response["exit"] != 0 and ("version" in (response["stdout"] + response["stderr"]).lower()), response
    for variant in ("base", "changed"):
        old = RESULT["cases"]["june1-" + variant]
        new = RESULT["cases"]["june3-" + variant]
        RESULT["comparisons"][variant] = {"same_rust_source_sha256": old["source_sha256"] == new["source_sha256"],
            "raw_llbc_equal": old["llbc_sha256"] == new["llbc_sha256"],
            "generated_file_names_equal": set(old["generated"]) == set(new["generated"]),
            "generated_file_sha256_equal": {k: v["sha256"] for k, v in old["generated"].items()} ==
                                           {k: v["sha256"] for k, v in new["generated"].items()},
            "old_generated": old["generated"], "new_generated": new["generated"]}
        assert RESULT["comparisons"][variant]["same_rust_source_sha256"]
    for bundle in BUNDLES:
        old = RESULT["cases"][bundle + "-base"]
        new = RESULT["cases"][bundle + "-changed"]
        assert old["source_sha256"] != new["source_sha256"]
        assert old["generated"]["Funs.lean"]["sha256"] != new["generated"]["Funs.lean"]["sha256"]
    RESULT["limits"] = [
        "Two cached paired releases only; no isolated Aeneas-only comparison because cross-pair LLBC is rejected.",
        "One tiny saved Rust crate and four sequential private targets; no Anneal generated workspace or service.",
        "Fresh Lean checks use each bundle's cached Aeneas Lean backend plus already cached shared dependency packages.",
        "Lean elaboration and selected Rust tests are not a proof of general translation soundness.",
        "No later-than-4.30 Lean/Lake pin is installed for F03's requested upgrade cell.",
    ]
    (HERE / "results.json").write_text(json.dumps(RESULT, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"case_count": len(RESULT["cases"]), "cross_pair_count": len(RESULT["cross_pair"]),
                      "comparisons": RESULT["comparisons"]}, indent=2))


if __name__ == "__main__":
    main()
