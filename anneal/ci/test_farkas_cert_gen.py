# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and live-Lean kernel tests for `anneal/ci/farkas_cert_gen.py`."""

from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

_CI_DIR = Path(__file__).resolve().parent
_ANNEAL_ROOT = _CI_DIR.parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

from anneal_ci_lib import DEFAULT_TOOL_ENV_SPECS, env_tool  # noqa: E402
from farkas_cert_gen import (  # noqa: E402
    _MAG_CAP_128,
    ParseError,
    generate_certificate,
    main as cli_main,
    parse_inequalities,
)


def _scrubbed_env(extra: dict[str, str] | None = None) -> dict[str, str]:
    clean = {
        k: v for k, v in os.environ.items()
        if not k.startswith("ANNEAL_") and k != "CARGO_TARGET_DIR"
    }
    if extra:
        clean.update(extra)
    return clean


def _pinned_lean_version() -> str:
    raw = (_ANNEAL_ROOT / "trusted/lean/lean-toolchain").read_text("utf-8").strip()
    return raw.split(":v", 1)[1] if ":v" in raw else raw.rsplit(":", 1)[-1]


def _verify_lean_version(cand: Path, expected_ver: str) -> bool:
    try:
        ver = subprocess.run([str(cand), "--version"], capture_output=True, text=True, timeout=5)
        pat = rf"\bversion\s+{re.escape(expected_ver)}(?:[^0-9A-Za-z._-]|$)"
        return ver.returncode == 0 and bool(re.search(pat, ver.stdout))
    except (OSError, subprocess.SubprocessError):
        return False


def _find_pinned_lean() -> Path | None:
    expected_ver = _pinned_lean_version()
    lean_env_names, lean_bundle_suffix = DEFAULT_TOOL_ENV_SPECS["lean"]
    if explicit := env_tool(lean_env_names, lean_bundle_suffix):
        if not (p := explicit.expanduser()).is_file():
            raise FileNotFoundError(f"Configured Lean binary not found: {p}")
        if not _verify_lean_version(res := p.resolve(), expected_ver):
            raise RuntimeError(f"Configured Lean binary is not v{expected_ver}: {res}")
        return res
    home = Path.home()
    xdg = os.environ.get("XDG_CACHE_HOME", "").strip()
    cache = (Path(xdg).expanduser() if xdg else home / ".cache") / "anneal/toolchain"
    if cache.is_dir():
        entries = []
        for entry in cache.iterdir():
            cand = entry / "lean/bin/lean"
            with contextlib.suppress(OSError):
                if cand.is_file():
                    entries.append((entry.stat().st_mtime, cand.resolve()))
        for _, cand in sorted(entries, key=lambda item: item[0], reverse=True):
            if _verify_lean_version(cand, expected_ver):
                return cand
    elan = home / f".elan/toolchains/leanprover--lean4---v{expected_ver}/bin/lean"
    if elan.is_file() and _verify_lean_version(elan.resolve(), expected_ver):
        return elan.resolve()
    if found := shutil.which("lean"):
        if _verify_lean_version(cand := Path(found).resolve(), expected_ver):
            return cand
    ci_lean = Path("/opt/anneal-nix/lean-toolchain/bin/lean")
    if ci_lean.is_file() and _verify_lean_version(ci_lean.resolve(), expected_ver):
        return ci_lean.resolve()
    return None


def _comb_tree_height(steps: list[dict[str, int | str]]) -> int:
    heights: list[int] = []
    for st in steps:
        if st["op"] == "hyp":
            heights.append(0)
        elif st["op"] == "comb":
            heights.append(1 + max(heights[int(st["s1"])], heights[int(st["s2"])]))
        else:
            heights.append(1 + heights[int(st["s"])])
    return heights[-1]


class FarkasCertGenTests(unittest.TestCase):
    def test_grammar_domain_rules_and_bounds(self) -> None:
        # Equality expands to 2 bounds; `<` desugars; AST structure preserved.
        eqs = parse_inequalities("x = y + 1", "nat")
        self.assertEqual(len(eqs), 2)
        self.assertEqual([op for _, op, _ in eqs], ["<=", "<="])
        res = generate_certificate(
            "nat", ["1 + n <= i", "i + 1 <= b + a"], "n + 1 < b + a", "nat_ok"
        )
        self.assertTrue(res["solved"])
        self.assertIn("1 + n ≤ i", res["lean_snippet"])
        self.assertIn("n + 1 < b + a", res["lean_snippet"])

        # Nat rejects subtraction/negative constants; right-scalar rejected.
        for dom, hyps, goal in (
            ("nat", ["x - 1 <= y"], "x <= y"),
            ("nat", ["-x <= 1"], "0 <= 1"),
            ("nat", ["x <= -1"], "0 <= 1"),
            ("nat", ["x * 2 <= 4"], "x <= 2"),
            ("nat", ["x * y <= 4"], "0 <= 1"),
            ("int", ["x <= 1"], "x = 1"),
            ("int", ["def <= 1"], "def <= 2"),
            ("int", ["then <= 1"], "then <= 2"),
            ("int", ["syntax <= 1"], "syntax <= 2"),
            ("int", ["macro <= 1"], "macro <= 2"),
            ("int", ["unsafe <= 1"], "unsafe <= 2"),
            ("int", ["using <= 1"], "using <= 2"),
            ("int", ["h0 <= 1"], "h0 <= 2"),
            ("int", ["mythm <= 1"], "mythm <= 2"),
            ("int", ["x <= " + str(_MAG_CAP_128 + 1)], "0 <= 1"),
            ("int", ["x <= " + "9" * 45], "0 <= 1"),
        ):
            with self.assertRaises(ParseError, msg=(dom, hyps, goal)):
                generate_certificate(dom, hyps, goal, "mythm")
        for bad_name in ("then", "syntax", "macro", "unsafe"):
            with self.assertRaises(ParseError, msg=bad_name):
                generate_certificate("int", ["x <= 1"], "x <= 2", bad_name)

        # Deep expressions and large systems fail bounds upfront.
        deep_lhs = " + ".join(["x"] * 20)
        with self.assertRaisesRegex(ParseError, "kernel limits"):
            generate_certificate("nat", [f"{deep_lhs} <= y"], "x <= y", "deep")
        chain49 = [f"v{i} <= v{i + 1}" for i in range(49)]
        with self.assertRaisesRegex(ParseError, "maxRecDepth"):
            generate_certificate("nat", chain49, "v0 <= v49", "over_nat", max_nodes=20000)

        # Unsatisfiable search budget vs unprovable constraints.
        uns = generate_certificate("int", ["a <= 5"], "a <= 4", "nope")
        self.assertFalse(uns["solved"])
        self.assertIn("No Farkas", uns["error"])

    def test_balanced_comb_pruning_and_cli_surface(self) -> None:
        chain = [f"v{i} <= v{i + 1}" for i in range(40)]
        res = generate_certificate("int", chain, "v0 <= v40", "chain40")
        self.assertTrue(res["solved"])
        self.assertLessEqual(_comb_tree_height(res["steps"]), 8)

        noise = [f"u{i} <= 10" for i in range(50)]
        pruned = generate_certificate("nat", [*noise, "x + 1 <= y", "y <= z"], "x < z", "pruned")
        self.assertTrue(pruned["solved"])
        self.assertEqual(pruned["kept_hyp_indices"], [50, 51])
        self.assertEqual(pruned["variables"], ["x", "y", "z"])

        eq_p = generate_certificate("nat", ["u <= 1", "a = b", "b <= c"], "a <= c", "eq_p")
        self.assertEqual(eq_p["kept_hyp_indices"], [1, 2])

        # CLI negative args, JSON/text exit codes, ASCII output, bad UTF-8.
        out = io.StringIO()
        with mock.patch.dict(os.environ, _scrubbed_env(), clear=True):
            with contextlib.redirect_stdout(out):
                rc = cli_main([
                    "--domain", "int", "--hyp", "-x<=5",
                    "--hyp", "x<=-10", "--goal", "-9<=1", "--json",
                ])
        self.assertEqual(rc, 0)
        self.assertTrue(json.loads(out.getvalue())["solved"])

        for bad_hyp in ("x \udcff <= 1", "x <= " + "9" * 5000):
            o2, e2 = io.StringIO(), io.StringIO()
            with mock.patch.dict(os.environ, _scrubbed_env(), clear=True):
                with contextlib.redirect_stdout(o2), contextlib.redirect_stderr(e2):
                    argv2 = ["--domain", "int", "--hyp", bad_hyp, "--goal", "0 <= 1", "--json"]
                    rc2 = cli_main(argv2)
            self.assertEqual(rc2, 2)
            self.assertEqual(e2.getvalue(), "")
            self.assertFalse(json.loads(o2.getvalue())["solved"])

        o3, e3 = io.StringIO(), io.StringIO()
        with mock.patch.dict(os.environ, _scrubbed_env(), clear=True):
            with contextlib.redirect_stdout(o3), contextlib.redirect_stderr(e3):
                rc3 = cli_main(["--domain", "int", "--hyp", "a <= 5", "--goal", "a <= 4"])
        self.assertEqual(rc3, 1)
        self.assertEqual(o3.getvalue(), "")
        self.assertIn("No Farkas", e3.getvalue())

        ascii_run = subprocess.run(
            [sys.executable, "-B", str(_CI_DIR / "farkas_cert_gen.py"),
             "--domain", "int", "--hyp", "a <= b", "--goal", "a <= b"],
            env={**_scrubbed_env(), "PYTHONIOENCODING": "ascii"},
            capture_output=True, text=True, timeout=15,
        )
        self.assertEqual(ascii_run.returncode, 0, ascii_run.stderr)
        self.assertIn("<=", ascii_run.stdout)
        self.assertIn("{ lhs :=", ascii_run.stdout)

    def test_lean_discovery_error_handling(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            stub_dir = root / "cache/anneal/toolchain/wrong/lean/bin"
            stub_dir.mkdir(parents=True)
            stub = stub_dir / "lean"
            stub.write_text("#!/bin/sh\necho 'Lean (version 0.0.0)'\n", encoding="utf-8")
            stub.chmod(0o755)
            with mock.patch.dict(os.environ, _scrubbed_env({"ANNEAL_LEAN": str(stub)}), clear=True):
                with self.assertRaises(RuntimeError):
                    _find_pinned_lean()
            with mock.patch.dict(
                os.environ, _scrubbed_env({"ANNEAL_LEAN": str(root / "missing")}), clear=True
            ):
                with self.assertRaises(FileNotFoundError):
                    _find_pinned_lean()
            ci_bin = Path("/opt/anneal-nix/lean-toolchain/bin/lean")
            with mock.patch.dict(os.environ, {"HOME": str(root / "nohome")}, clear=True):
                with mock.patch("shutil.which", return_value=None):
                    with mock.patch.object(
                        Path, "is_file",
                        autospec=True,
                        side_effect=lambda self_p: self_p == ci_bin,
                    ):
                        with mock.patch.object(
                            Path, "resolve",
                            autospec=True,
                            side_effect=lambda self_p: stub if self_p == ci_bin else self_p,
                        ):
                            with mock.patch(
                                "test_farkas_cert_gen._verify_lean_version",
                                side_effect=lambda cand, _v: cand == stub,
                            ):
                                self.assertEqual(_find_pinned_lean(), stub)

    def test_pass1_int_syntax_and_ci_strict_mode(self) -> None:
        # `--domain int` negatives avoid unary `-` (`«term-_»`).
        int_sig = generate_certificate(
            "int", ["-2*x - y <= 5", "-3 <= -y"], "-4 <= x", "sig_chk"
        )
        self.assertTrue(int_sig["solved"])
        self.assertIn("Int.negOfNat 2 * x - y", int_sig["lean_snippet"])
        self.assertIn("Int.neg y", int_sig["lean_snippet"])
        self.assertIn("Int.negOfNat 4 ≤ x", int_sig["lean_snippet"])
        grp_sig = generate_certificate(
            "int", ["-(x + z) <= -(-1)", "x <= -2", "z <= 0"], "1 <= 0", "grp_chk"
        )
        self.assertTrue(grp_sig["solved"])
        self.assertIn("Int.neg (x + z) ≤ Int.neg (Int.negOfNat 1)", grp_sig["lean_snippet"])
        for snip in (int_sig["lean_snippet"], grp_sig["lean_snippet"]):
            for ln in snip.splitlines():
                self.assertNotRegex(ln, r"(?:^|[\s(\[≤<])-[0-9A-Za-z_(]")

        # Missing pinned Lean fails under ANNEAL_CI_STRICT=1 (no skip).
        with mock.patch("test_farkas_cert_gen._find_pinned_lean", return_value=None):
            with mock.patch.dict(os.environ, {"ANNEAL_CI_STRICT": "1"}, clear=False):
                with self.assertRaises(AssertionError):
                    self.test_live_lean_kernel_checks_emitted_snippets()
            with mock.patch.dict(
                os.environ, {k: v for k, v in os.environ.items() if k != "ANNEAL_CI_STRICT"},
                clear=True,
            ):
                with self.assertRaises(unittest.SkipTest):
                    self.test_live_lean_kernel_checks_emitted_snippets()

    def test_live_lean_kernel_checks_emitted_snippets(self) -> None:
        lean_bin = _find_pinned_lean()
        if lean_bin is None:
            msg = f"no pinned Lean {_pinned_lean_version()} toolchain installed"
            if os.environ.get("ANNEAL_CI_STRICT") == "1":
                self.fail(msg)
            self.skipTest(msg)
        noise = [f"u{i} <= 10" for i in range(50)]
        chain40 = [f"v{i} <= v{i + 1}" for i in range(40)]
        lad14 = ["3 * x1 <= 2", *[f"3 * x{i + 1} <= 2 * x{i} + 2" for i in range(1, 14)]]
        cases = [
            ("nat", ["2*i <= 2*n + 1", "2*n + 1 <= 2*i"], "1 <= 0", "parity_false", False),
            ("int", ["-2*x - y <= 5", "-3 <= -y"], "-4 <= x", "int_bound", False),
            ("int", ["-2*x - y <= 5", "-3 <= -y"], "-4 <= x", "int_bound_asc", True),
            ("int", ["2*i <= 2*n + 1", "2*n + 1 <= 2*i"], "1 <= 0", "int_parity", False),
            ("int", ["x - y <= 5", "y <= 2"], "x < 8", "int_sub_lt", False),
            ("int", ["1 <= 0"], "2 <= 0", "int_const", False),
            ("int", ["-9 <= 1", "1 <= 0"], "-2 <= 0", "int_neg_const", False),
            ("nat", ["a = b"], "a <= b", "eq_bound", False),
            ("nat", ["x + 2*y <= 10"], "x <= 10", "nonneg_x", False),
            ("nat", ["1 + n <= i", "i + 1 <= b + a"], "n + 1 < b + a", "nat_shape", False),
            ("nat", ["a + 1 <= b"], "b > a", "nat_gt", False),
            ("nat", lad14, "x14 <= 0", "lad_14_nat", False),
            ("int", lad14, "x14 <= 0", "lad_14_int", False),
            ("int", ["x <= -(3)"], "x <= -(2)", "int_neg_paren", False),
            ("int", ["-(2*x + y) <= -(-1)", "y <= 1"], "-x <= 1", "int_neg_grp", False),
            ("nat", [*noise, "x + 1 <= y", "y <= z"], "x < z", "pruned_50", False),
            ("int", chain40, "v0 <= v40", "chain_40", False),
            ("int", ["x <= 5"], "x <= 5", "ascii_check", True),
        ]
        snippets = [
            generate_certificate(d, h, g, nm, ascii_lean=asc)["lean_snippet"]
            for d, h, g, nm, asc in cases
        ]
        with tempfile.TemporaryDirectory() as tmp:
            t = Path(tmp)
            (t / "Anneal").mkdir()
            lean_env = {"PATH": f"{lean_bin.parent}:/usr/bin:/bin"}
            if ld := os.environ.get("LD_LIBRARY_PATH"):
                lean_env["LD_LIBRARY_PATH"] = ld
            subprocess.check_call(
                [
                    str(lean_bin), "-R", str(_ANNEAL_ROOT / "theory"),
                    "-o", str(t / "Anneal/LinearArith.olean"),
                    str(_ANNEAL_ROOT / "theory/Anneal/LinearArith.lean"),
                ],
                env=lean_env, timeout=120,
            )
            lean_env["LEAN_PATH"] = f"{t}:{lean_bin.parent.parent / 'lib/lean'}"
            probe = t / "Probe.lean"
            hdr = (
                "module\nprelude\nimport Anneal.LinearArith\n"
                "open Anneal.LinearArith\npublic section\n"
            )
            body = "\n".join(
                ln for snip in snippets for ln in snip.splitlines()
                if not ln.startswith(("import ", "open "))
            )
            probe.write_text(hdr + body + "\n", encoding="utf-8")
            res = subprocess.run(
                [str(lean_bin), str(probe)], env=lean_env,
                text=True, capture_output=True, timeout=120,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertEqual(res.stdout.strip() + res.stderr.strip(), "")

            neg_probe = t / "NegControl.lean"
            neg_probe.write_text(
                "import Anneal.LinearArith\nprivate theorem bad_ctrl : (1 : Nat) = 2 := rfl\n",
                encoding="utf-8",
            )
            neg_res = subprocess.run(
                [str(lean_bin), str(neg_probe)], env=lean_env,
                text=True, capture_output=True, timeout=60,
            )
            self.assertNotEqual(neg_res.returncode, 0)

            # Confirm emitted snippets also pass Pass-1 preflight.
            tb = _ANNEAL_ROOT / "trusted/audit/TrustedBoundary.lean"
            sysroot = str(lean_bin.parent.parent)
            pf_env = {**lean_env, "LEAN_PATH": f"{_ANNEAL_ROOT / 'theory'}:{sysroot}/lib/lean"}
            g_req, g_out = t / "greq.json", t / "gout.json"
            g_req.write_text(json.dumps(
                {"mode": "resolve-imports", "sysroot": sysroot, "modules": ["Init"]}
            ), encoding="utf-8")
            subprocess.check_call(
                [str(lean_bin), "--run", str(tb), str(g_req), str(g_out)], env=pf_env, timeout=60,
            )
            graph = json.loads(g_out.read_text(encoding="utf-8"))["result"]["graph"]
            p_req, p_out = t / "preq.json", t / "pout.json"
            p_req.write_text(json.dumps({
                "mode": "preflight", "sysroot": sysroot, "artifacts": [],
                "foundation": sorted(graph), "graph": graph, "axioms": [], "baseSources": [],
                "allowLocalSemireducible": False,
                "sources": [
                    ["Anneal.LinearArith", str(_ANNEAL_ROOT / "theory/Anneal/LinearArith.lean")],
                    ["Anneal.TestFarkasPreflight", str(probe)],
                ],
            }), encoding="utf-8")
            pf = subprocess.run(
                [str(lean_bin), "--run", str(tb), str(p_req), str(p_out)],
                env=pf_env, text=True, capture_output=True, timeout=60,
            )
            self.assertEqual(pf.returncode, 0, pf.stdout + pf.stderr)
            self.assertTrue(json.loads(p_out.read_text(encoding="utf-8"))["ok"])


if __name__ == "__main__":
    unittest.main()
