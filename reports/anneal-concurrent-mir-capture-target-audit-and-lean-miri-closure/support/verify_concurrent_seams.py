#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ANNEAL_ROOT = Path(os.environ["ANNEAL_ROOT"])
LEAN_PREFIX = Path(
    os.environ.get(
        "LEAN_PREFIX",
        str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1"),
    )
)
LEAN_BIN = LEAN_PREFIX / "bin" / "lean"
PROOF_SRC = Path(__file__).resolve().parent / "Anneal" / "ConcurrentSeamsProof.lean"

OLEAN_PARTS = ["olean", "olean.server", "olean.private"]
IR_PARTS = ["ir.sig", "ir"]
ALL_PARTS = OLEAN_PARTS + IR_PARTS
CLEAN_ENV = {"PATH": "/usr/bin:/bin"}


def sha256_path(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def to_wire(avail: dict[str, str]) -> list[list[str]]:
    o = [avail[k] for k in OLEAN_PARTS if k in avail]
    i = [avail[k] for k in IR_PARTS if k in avail]
    return [o, i]


THEOREMS = [
    "Anneal.ConcurrentSeamsProof.explPCM_idempotent_eq_unit",
    "Anneal.ConcurrentSeamsProof.explPCM_no_nonunit_self_duplication",
    "Anneal.ConcurrentSeamsProof.ResPCM.core_duplicable",
    "Anneal.ConcurrentSeamsProof.persistently_duplicable",
    "Anneal.ConcurrentSeamsProof.toResPCM_conj_iff",
    "Anneal.ConcurrentSeamsProof.toResPCM_wand_iff",
    "Anneal.ConcurrentSeamsProof.agreeNat_refutes_cancellativity",
    "Anneal.ConcurrentSeamsProof.heaplet_and_persistent_agreement_coexist",
]


def main() -> int:
    lock_data = json.loads((ANNEAL_ROOT / "trusted/lean/foundation-lock.json").read_text())
    inspector_orig = ANNEAL_ROOT / "trusted/audit/TrustedBoundary.lean"
    lean_sha = sha256_path(LEAN_BIN)
    lean_ver = subprocess.check_output([str(LEAN_BIN), "--version"], env=CLEAN_ENV, text=True).strip()
    assert lock_data["distributions"].get(lean_ver) == lean_sha

    # Verify all 255 sysroot foundation artifacts by SHA-256!
    artifacts: dict[str, list[list[str]]] = {}
    for fmod, rec in sorted(lock_data["modules"].items()):
        rel_mod = fmod.replace(".", "/")
        avail: dict[str, str] = {}
        for part in ALL_PARTS:
            expected = rec["parts"][part]
            installed = LEAN_PREFIX / "lib/lean" / f"{rel_mod}.{part}"
            if expected is not None:
                assert installed.exists() and sha256_path(installed) == expected, f"Mismatch {installed}"
                avail[part] = str(installed)
        artifacts[fmod] = to_wire(avail)

    foundation_mods = sorted(lock_data["modules"].keys())
    graph = dict(lock_data["graph"])
    axioms = lock_data["axioms"]

    # Minimal transitive closure of Trusted.* + Anneal.Core.SepPCM + Anneal.ConcurrentSeamsProof
    trusted_mods = [
        ("Trusted", ANNEAL_ROOT / "trusted/lean/Trusted.lean"),
        ("Trusted.MirAst.Types", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst/Types.lean"),
        ("Trusted.MirAst.Places", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst/Places.lean"),
        ("Trusted.MirAst.Rvalues", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst/Rvalues.lean"),
        ("Trusted.MirAst.Statements", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst/Statements.lean"),
        ("Trusted.MirAst.Terminators", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst/Terminators.lean"),
        ("Trusted.MirAst.Body", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst/Body.lean"),
        ("Trusted.MirAst", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst.lean"),
        ("Trusted.MirModel", ANNEAL_ROOT / "trusted/lean/Trusted/MirModel.lean"),
        ("Trusted.MirSemantics.Enum", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Enum.lean"),
        ("Trusted.MirSemantics.Bytes", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Bytes.lean"),
        ("Trusted.MirSemantics.Layout", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Layout.lean"),
        ("Trusted.MirSemantics.Memory", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Memory.lean"),
        ("Trusted.MirSemantics.State", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/State.lean"),
        ("Trusted.MirSemantics.Ops", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Ops.lean"),
        ("Trusted.MirSemantics.Step", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Step.lean"),
        ("Trusted.MirSemantics.Boundary", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Boundary.lean"),
        ("Trusted.MirSemantics.CanaryFixtures", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/CanaryFixtures.lean"),
        ("Trusted.MirSemantics", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics.lean"),
    ]
    theory_mods = [
        ("Anneal.NatBitwise", ANNEAL_ROOT / "theory/Anneal/NatBitwise.lean"),
        ("Anneal.MirWp.Core", ANNEAL_ROOT / "theory/Anneal/MirWp/Core.lean"),
        ("Anneal.MirWp.Scalars", ANNEAL_ROOT / "theory/Anneal/MirWp/Scalars.lean"),
        ("Anneal.MirWp.Reflection", ANNEAL_ROOT / "theory/Anneal/MirWp/Reflection.lean"),
        ("Anneal.MirWp.Execution", ANNEAL_ROOT / "theory/Anneal/MirWp/Execution.lean"),
        ("Anneal.MirWp.Canaries", ANNEAL_ROOT / "theory/Anneal/MirWp/Canaries.lean"),
        ("Anneal.MirWp", ANNEAL_ROOT / "theory/Anneal/MirWp.lean"),
        ("Anneal.Core.SepPCM", ANNEAL_ROOT / "theory/Anneal/Core/SepPCM.lean"),
        ("Anneal.ConcurrentSeamsProof", PROOF_SRC),
    ]
    all_mods = trusted_mods + theory_mods

    print(f"PROOF_SRC lines={len(PROOF_SRC.read_text().splitlines())} sha256={sha256_path(PROOF_SRC)}")

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        inspector = tmp / "TrustedBoundary.lean"
        shutil.copy2(inspector_orig, inspector)

        staged = []
        src_map = {}
        for m, p in all_mods:
            dst = tmp / "src" / (m.replace(".", "/") + ".lean")
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(p, dst)
            staged.append([m, str(dst)])
            src_map[m] = dst

        pf_req = tmp / "pf_req.json"
        pf_res = tmp / "pf_res.json"
        pf_req.write_text(json.dumps({
            "mode": "preflight",
            "sysroot": str(LEAN_PREFIX),
            "artifacts": [[k, v] for k, v in sorted(artifacts.items())],
            "foundation": foundation_mods,
            "graph": graph,
            "axioms": axioms,
            "sources": staged,
        }))
        subprocess.run([str(LEAN_BIN), "-j1", "-M2048", "--run", str(inspector), str(pf_req), str(pf_res)], cwd=tmp, env=CLEAN_ENV, check=True)
        pf_data = json.loads(pf_res.read_text())
        assert pf_data["ok"] is True
        imports_by_mod = {}
        module_tiers = []
        for hdr in pf_data["result"]["headers"]:
            m = hdr["module"]
            imports_by_mod[m] = hdr["imports"]
            if m.startswith("Trusted"):
                module_tiers.append([m, hdr["trustTier"]])
            else:
                assert hdr.get("trustTier") is None
        print("GATE 1 (PREFLIGHT) OK")

        staged_names = {m for m, _ in all_mods}
        topo_order: list[str] = []
        done: set[str] = set()

        def visit_mod(m: str) -> None:
            if m in done or m not in staged_names:
                return
            for imp in imports_by_mod[m]:
                visit_mod(imp["module"])
            done.add(m)
            topo_order.append(m)

        for m, _ in all_mods:
            visit_mod(m)

        out_lib = tmp / "lib"
        for m in topo_order:
            setup_p = tmp / f"{m}.setup.json"
            setup_p.write_text(json.dumps({
                "name": m,
                "isModule": False,
                "imports": imports_by_mod[m],
                "importArts": artifacts,
                "dynlibs": [],
                "plugins": [],
                "options": {},
            }))
            olean_out = out_lib / f"{m.replace('.', '/')}.olean"
            olean_out.parent.mkdir(parents=True, exist_ok=True)
            res = subprocess.run(
                [str(LEAN_BIN), "-j1", "-M2048", "-t0", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true", "--setup", str(setup_p), "-o", str(olean_out), str(src_map[m])],
                cwd=tmp, env=CLEAN_ENV, capture_output=True, text=True,
            )
            if res.returncode != 0 or res.stdout != "" or res.stderr != "":
                print(f"COMPILE FAILED {m}: rc={res.returncode} out={res.stdout!r} err={res.stderr!r}", file=sys.stderr)
                return 1
            avail_m = {}
            stem = str(olean_out)[:-len("olean")]
            for part in ALL_PARTS:
                cand = Path(f"{stem}{part}")
                if cand.exists():
                    avail_m[part] = str(cand)
            artifacts[m] = to_wire(avail_m)
            graph[m] = imports_by_mod[m]
        print("GATE 2 (COMPILE) OK")

        aud_req = tmp / "aud_req.json"
        aud_res = tmp / "aud_res.json"
        aud_req.write_text(json.dumps({
            "mode": "audit",
            "sysroot": str(LEAN_PREFIX),
            "artifacts": [[k, v] for k, v in sorted(artifacts.items())],
            "foundation": foundation_mods,
            "graph": graph,
            "axioms": axioms,
            "trusted": [m for m, _ in trusted_mods],
            "theory": [m for m, _ in theory_mods],
            "moduleTiers": module_tiers,
            "requireMirWp": True,
        }))
        subprocess.run([str(LEAN_BIN), "-j1", "-M2048", "--run", str(inspector), str(aud_req), str(aud_res)], cwd=tmp, env=CLEAN_ENV, check=True)
        aud_data = json.loads(aud_res.read_text())
        assert aud_data["ok"] is True and aud_data["result"]["replay"] is True
        print("GATE 3 (AUDIT) SUMMARY:", json.dumps({
            "ok": aud_data["ok"],
            "replay": aud_data["result"]["replay"],
            "replayedDeclarations": aud_data["result"]["replayedDeclarations"],
            "compilerOnlyNames": aud_data["result"]["compilerOnlyNames"],
            "axioms": aud_data["result"]["axioms"],
        }))

        ax_lines = ["prelude", "import Anneal.ConcurrentSeamsProof", ""] + [f"#print axioms {t}" for t in THEOREMS]
        ax_src = tmp / "Ax.lean"
        ax_src.write_text("\n".join(ax_lines) + "\n")
        ax_setup = tmp / "Ax.setup.json"
        ax_setup.write_text(json.dumps({
            "name": "Ax",
            "isModule": False,
            "imports": [{"module": "Anneal.ConcurrentSeamsProof", "importAll": False, "isExported": True, "isMeta": False}],
            "importArts": artifacts,
            "dynlibs": [],
            "plugins": [],
            "options": {},
        }))
        res_ax = subprocess.run([str(LEAN_BIN), "-j1", "-M2048", "-t0", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true", "--setup", str(ax_setup), str(ax_src)], cwd=tmp, env=CLEAN_ENV, capture_output=True, text=True, check=True)
        for line in res_ax.stdout.splitlines():
            assert "sorryAx" not in line and "ofReduceBool" not in line
        print("GATE 5 (AXIOMS):\n" + res_ax.stdout.strip())

    return 0


if __name__ == "__main__":
    sys.exit(main())
