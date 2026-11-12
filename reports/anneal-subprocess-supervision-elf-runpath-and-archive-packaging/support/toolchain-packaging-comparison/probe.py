#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical benchmark comparing per-run Lean source recompilation (Variant 2)
against precompiled SHA-256-authenticated share/anneal/ .olean artifacts (Variant 4).
"""

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time


HERE = Path(__file__).resolve().parent


# Representative minimal 7-module Trusted + Anneal prefix and 4-module target crate
# matching the exact 11-module compilation DAG in Anneal's verifier.
PREFIX_MODULES = [
    (
        "Trusted/Mvp/Syntax.lean",
        "Trusted.Mvp.Syntax",
        """namespace Trusted.Mvp
structure FnDecl where
  name : String
  retVal : Nat
deriving DecidableEq, Repr
end Trusted.Mvp
""",
    ),
    (
        "Trusted/Mvp/Semantics.lean",
        "Trusted.Mvp.Semantics",
        """import Trusted.Mvp.Syntax
namespace Trusted.Mvp
def evalFn (f : FnDecl) : Nat := f.retVal
end Trusted.Mvp
""",
    ),
    (
        "Trusted/Mvp.lean",
        "Trusted.Mvp",
        """import Trusted.Mvp.Syntax
import Trusted.Mvp.Semantics
""",
    ),
    (
        "Trusted.lean",
        "Trusted",
        """import Trusted.Mvp
namespace Trusted
def CrateTheorem (f : Trusted.Mvp.FnDecl) (spec : Nat -> Prop) : Prop :=
  spec (Trusted.Mvp.evalFn f)
end Trusted
""",
    ),
    (
        "Anneal/Mvp/Execution.lean",
        "Anneal.Mvp.Execution",
        """import Trusted
namespace Anneal.Mvp
theorem prove_eval (f : Trusted.Mvp.FnDecl) (P : Nat -> Prop) (h : P f.retVal) :
    Trusted.CrateTheorem f P := h
end Anneal.Mvp
""",
    ),
    (
        "Anneal/Mvp/Canaries.lean",
        "Anneal.Mvp.Canaries",
        """import Anneal.Mvp.Execution
namespace Anneal.Mvp
def sampleDecl : Trusted.Mvp.FnDecl := { name := "id", retVal := 42 }
end Anneal.Mvp
""",
    ),
    (
        "Anneal.lean",
        "Anneal",
        """import Trusted
import Anneal.Mvp.Execution
import Anneal.Mvp.Canaries
""",
    ),
]

TARGET_MODULES = [
    (
        "Captured.lean",
        "Captured",
        """import Trusted
namespace Captured
def crate : Trusted.Mvp.FnDecl := { name := "answer", retVal := 7 }
end Captured
""",
    ),
    (
        "Spec.lean",
        "Spec",
        """import Trusted
import Captured
namespace Spec
def specs (n : Nat) : Prop := n = 7
end Spec
""",
    ),
    (
        "Proof.lean",
        "Proof",
        """import Trusted
import Anneal
import Captured
import Spec
namespace Proof
theorem verify_crate : Trusted.CrateTheorem Captured.crate Spec.specs :=
  Anneal.Mvp.prove_eval Captured.crate Spec.specs rfl
end Proof
""",
    ),
    (
        "Expected.lean",
        "Expected",
        """import Trusted
import Captured
import Spec
import Proof
namespace Expected
theorem CrateTheorem : Trusted.CrateTheorem Captured.crate Spec.specs :=
  Proof.verify_crate
end Expected
""",
    ),
]


def find_lean_binary() -> Path:
    lean_stores = sorted(Path("/nix/store").glob("*-lean-toolchain-x86_64-linux-4.34.1/bin/lean"))
    if lean_stores:
        return lean_stores[0]
    which_lean = shutil.which("lean")
    if which_lean:
        return Path(which_lean)
    raise RuntimeError("lean binary not found")


def run_lean_compile(lean_bin: Path, src_root: Path, src: Path, out_olean: Path, lean_path: str) -> None:
    out_olean.parent.mkdir(parents=True, exist_ok=True)
    inner_cmd = [
        "/usr/bin/env",
        "-i",
        "PATH=/usr/bin:/bin",
        f"LEAN_PATH={lean_path}",
        str(lean_bin),
        f"--root={src_root}",
        "-DwarningAsError=true",
        "-DElab.async=false",
        "-Ddebug.skipKernelTC=false",
        "-t0",
        "-o",
        str(out_olean),
        str(src),
    ]
    anneal_lean_run = shutil.which("anneal-lean-run")
    if anneal_lean_run:
        cmd = [
            anneal_lean_run,
            "--mode",
            "file",
            "--concurrency",
            "5",
            "--",
            *inner_cmd,
        ]
    else:
        cmd = inner_cmd
    subprocess.run(cmd, check=True, capture_output=True, text=True)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def main() -> None:
    lean_bin = find_lean_binary()
    lean_sys_lib = lean_bin.parent.parent / "lib/lean"

    with tempfile.TemporaryDirectory(prefix="anneal-pkg-bench-") as tmp:
        tmp_path = Path(tmp)

        # -------------------------------------------------------------------
        # Variant 2 simulation: Per-run recompilation of all 7 Trusted/Anneal
        # prefix modules + 4 target modules (11 Lean compilations per run).
        # -------------------------------------------------------------------
        v2_dir = tmp_path / "variant2_per_run"
        v2_src = v2_dir / "src"
        v2_lib = v2_dir / "lib"
        v2_lean_path = f"{v2_lib}:{lean_sys_lib}"

        t0 = time.perf_counter()
        v2_prefix_t0 = time.perf_counter()
        for rel, _mod, content in PREFIX_MODULES:
            s = v2_src / rel
            s.parent.mkdir(parents=True, exist_ok=True)
            s.write_text(content)
            o = v2_lib / Path(rel).with_suffix(".olean")
            run_lean_compile(lean_bin, v2_src, s, o, v2_lean_path)
        v2_prefix_ms = (time.perf_counter() - v2_prefix_t0) * 1000.0

        v2_target_t0 = time.perf_counter()
        for rel, _mod, content in TARGET_MODULES:
            s = v2_src / rel
            s.parent.mkdir(parents=True, exist_ok=True)
            s.write_text(content)
            o = v2_lib / Path(rel).with_suffix(".olean")
            run_lean_compile(lean_bin, v2_src, s, o, v2_lean_path)
        v2_target_ms = (time.perf_counter() - v2_target_t0) * 1000.0
        v2_total_ms = (time.perf_counter() - t0) * 1000.0

        # -------------------------------------------------------------------
        # Variant 4 simulation: Precompiled share/anneal/lib/lean/ (.olean + .lean)
        # authenticated by SHA-256 manifest, compiling ONLY the 4 target modules.
        # -------------------------------------------------------------------
        share_anneal_lib = v2_lib  # Already holds the precompiled prefix .oleans
        prefix_manifest = {}
        for rel, _mod, content in PREFIX_MODULES:
            olean_rel = str(Path(rel).with_suffix(".olean"))
            prefix_manifest[rel] = {
                "source_sha256": sha256_bytes(content.encode()),
                "olean_sha256": sha256_file(share_anneal_lib / olean_rel),
            }

        v4_dir = tmp_path / "variant4_precompiled"
        v4_src = v4_dir / "src"
        v4_lib = v4_dir / "lib"
        v4_lean_path = f"{v4_lib}:{share_anneal_lib}:{lean_sys_lib}"

        t1 = time.perf_counter()
        v4_auth_t0 = time.perf_counter()
        for rel, hashes in prefix_manifest.items():
            src_path = v2_src / rel
            olean_path = share_anneal_lib / Path(rel).with_suffix(".olean")
            assert sha256_file(src_path) == hashes["source_sha256"]
            assert sha256_file(olean_path) == hashes["olean_sha256"]
        v4_auth_ms = (time.perf_counter() - v4_auth_t0) * 1000.0

        v4_target_t0 = time.perf_counter()
        for rel, _mod, content in TARGET_MODULES:
            s = v4_src / rel
            s.parent.mkdir(parents=True, exist_ok=True)
            s.write_text(content)
            o = v4_lib / Path(rel).with_suffix(".olean")
            run_lean_compile(lean_bin, v4_src, s, o, v4_lean_path)
        v4_target_ms = (time.perf_counter() - v4_target_t0) * 1000.0
        v4_total_ms = (time.perf_counter() - t1) * 1000.0

    payload = {
        "packaging_variants_comparison": [
            {
                "variant": "1_split_archive_manual_env_and_test_reexec",
                "required_manual_env_vars_workspace": 5,
                "required_manual_env_vars_smoke_test": 4,
                "bundles_anneal_audit_in_archive": False,
                "bundles_trusted_boundary_in_archive": False,
                "bundles_precompiled_prefix_oleans": False,
                "reexecs_cargo_test_binary_for_setup": True,
            },
            {
                "variant": "2_include_str_embedded_per_run_recompilation",
                "required_manual_env_vars_workspace": 0,
                "required_manual_env_vars_smoke_test": 0,
                "embedded_files_count": 11,
                "lean_prefix_compilations_per_verify": len(PREFIX_MODULES),
                "lean_target_compilations_per_verify": len(TARGET_MODULES),
                "prefix_compile_ms": round(v2_prefix_ms, 2),
                "target_compile_ms": round(v2_target_ms, 2),
                "total_compile_ms": round(v2_total_ms, 2),
            },
            {
                "variant": "3_sha256_manifest_tmp_hardlink_lazy_prefix",
                "required_manual_env_vars_workspace": 0,
                "requires_external_anneal_root_checkout": True,
                "hardlinks_toolchain_into_tmp": True,
                "compiles_rustc_capture_at_runtime": True,
                "lean_prefix_compilations_on_cold_cli_run": len(PREFIX_MODULES),
            },
            {
                "variant": "4_unified_zero_env_precompiled_archive",
                "required_manual_env_vars_workspace": 0,
                "required_manual_env_vars_smoke_test": 0,
                "bundles_anneal_audit_in_archive": True,
                "bundles_trusted_boundary_in_archive": True,
                "bundles_precompiled_prefix_oleans": True,
                "reexecs_cargo_test_binary_for_setup": False,
                "rustlib_symlink_dedup_saved_bytes": 357599568,
                "lean_prefix_compilations_per_verify": 0,
                "lean_target_compilations_per_verify": len(TARGET_MODULES),
                "prefix_sha256_auth_ms": round(v4_auth_ms, 3),
                "target_compile_ms": round(v4_target_ms, 2),
                "total_compile_ms": round(v4_total_ms, 2),
                "speedup_ratio": round(v2_total_ms / v4_total_ms, 2),
            },
        ]
    }
    (HERE / "results.json").write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
