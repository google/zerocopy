#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for the `0`-TCB dual-polar `audit_spec.py` checker."""

from __future__ import annotations

import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
from typing import Any
import unittest
from unittest import mock

_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))
import audit_spec  # noqa: E402


def _write_exec(path: Path, body: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path


def _failure_receipt(**overrides: Any) -> dict[str, Any]:
    """A `cargo-anneal verify` Receipt v3 failure receipt (`FailureReceipt`).

    Mirrors a real `02_unit_pointer_metadata` mutant receipt: `reason` is
    omitted unless a resource limit was hit.
    """
    receipt: dict[str, Any] = {
        "schema_version": 3,
        "taint_reasons": [],
        "elaboration_sandbox": "linux_bwrap",
        "status": "proof_failed",
        "phase": "audit",
        "detail": "Proof.verify failed to check against Expected.claim",
        "hint": None,
        "artifacts": "/tmp/artifacts",
    }
    receipt.update(overrides)
    return receipt


def _verified_receipt(status: str = "selected_unit_verified") -> dict[str, Any]:
    return {
        "schema_version": 3,
        "status": status,
        "taint_reasons": [] if not status.startswith("tainted_") else ["x"],
        "elaboration_sandbox": "linux_bwrap",
        "deferred": [],
    }


class DirectSandbox:
    """Test double for `LeanSandbox` that records the policy and runs directly."""

    def __init__(self) -> None:
        self.calls: list[dict[str, Any]] = []

    def run(self, cmd, *, ro, rw, cwd, env, timeout):  # type: ignore[no-untyped-def]
        self.calls.append(
            {
                "cmd": list(cmd),
                "ro": [Path(p) for p in ro],
                "rw": [Path(p) for p in rw],
                "env": dict(env),
            }
        )
        return subprocess.run(
            list(cmd),
            cwd=cwd,
            env=dict(env),
            capture_output=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
            check=False,
        )


class ClassifyPoleATests(unittest.TestCase):
    def classify(self, rc: int, receipt: Any, stderr: str = ""):  # type: ignore[no-untyped-def]
        text = receipt if isinstance(receipt, str) else json.dumps(receipt)
        return audit_spec.classify_pole_a_result(rc, text, stderr)

    def test_clean_proof_failed(self) -> None:
        res = self.classify(1, _failure_receipt())
        self.assertTrue(res.clean_reject, res.detail)
        self.assertEqual(res.classification, "clean_proof_failed")
        self.assertEqual(res.phase, "audit")

    def test_any_resource_limit_reason_fails_closed(self) -> None:
        for reason in ("heartbeat_limit_exceeded", "a_future_limit_kind"):
            res = self.classify(1, _failure_receipt(reason=reason))
            self.assertFalse(res.clean_reject, reason)
            self.assertEqual(res.classification, "resource_limit", reason)

    def test_rejects_crash_markers_and_stderr(self) -> None:
        for detail in (
            "error: maximum recursion depth exceeded (runtime.maxRecDepth)",
            "deterministic timeout at (kernel)",
            "thread 'main' panicked at verifier",
        ):
            res = self.classify(1, _failure_receipt(detail=detail))
            self.assertFalse(res.clean_reject, detail)
            self.assertEqual(res.classification, "crash_masquerade", detail)
        res = self.classify(1, _failure_receipt(), "fatal runtime error")
        self.assertEqual(res.classification, "crash_masquerade")

    def test_every_passing_status_is_mutant_verified(self) -> None:
        for status in sorted(audit_spec.PASSING_STATUSES):
            res = self.classify(0, _verified_receipt(status))
            self.assertFalse(res.clean_reject, status)
            self.assertEqual(res.classification, "mutant_verified", status)
        # A fictional `verified` status is not a passing status.
        res = self.classify(0, _verified_receipt("verified"))
        self.assertEqual(res.classification, "unexpected_failure")

    def test_envelope_violations(self) -> None:
        for receipt, rc, want in (
            (_failure_receipt(schema_version=2), 1, "malformed_output"),
            ({k: v for k, v in _failure_receipt().items() if k != "schema_version"}, 1,
             "malformed_output"),
            (_failure_receipt(schema_version=True), 1, "malformed_output"),
            (_failure_receipt(phase="capture"), 1, "unexpected_failure"),
            (_failure_receipt(elaboration_sandbox=None), 1, "unexpected_failure"),
            (_failure_receipt(taint_reasons=["unsandboxed"]), 1, "unexpected_failure"),
            ({k: v for k, v in _failure_receipt().items() if k != "taint_reasons"}, 1,
             "unexpected_failure"),
            (_failure_receipt(status="unsupported"), 1, "unexpected_failure"),
            (_failure_receipt(status="tool_failed", phase="capture"), 2,
             "unexpected_failure"),
            (_failure_receipt(), 2, "unexpected_failure"),
            (_verified_receipt("crate_verified"), 1, "unexpected_failure"),
        ):
            res = self.classify(rc, receipt)
            self.assertFalse(res.clean_reject, receipt)
            self.assertEqual(res.classification, want, receipt)
        dup = '{"schema_version": 3, "status": "proof_failed", "status": "x"}'
        self.assertEqual(self.classify(1, dup).classification, "malformed_output")
        self.assertEqual(self.classify(1, "[]").classification, "malformed_output")


class ParseAndLintTests(unittest.TestCase):
    def test_parse_inspector_output_variants(self) -> None:
        nonce = "abc123"
        self.assertEqual(
            audit_spec.parse_inspector_output(f"AUDIT_SPEC_AXIOMS:{nonce}:[]\n", nonce),
            (),
        )
        self.assertEqual(
            audit_spec.parse_inspector_output(
                f'noise\nAUDIT_SPEC_AXIOMS:{nonce}:["propext","Quot.sound"]\n',
                nonce,
            ),
            ("propext", "Quot.sound"),
        )
        for bad in (
            "'__auditSpecCheck' does not depend on any axioms\n",
            "AUDIT_SPEC_AXIOMS:wrong:[]\n",
            f"AUDIT_SPEC_AXIOMS:{nonce}:[]\nAUDIT_SPEC_AXIOMS:{nonce}:[]\n",
            f"AUDIT_SPEC_AXIOMS:{nonce}:not-json\n",
            f'AUDIT_SPEC_AXIOMS:{nonce}:{{"a": 1}}\n',
            f"AUDIT_SPEC_AXIOMS:{nonce}:[1]\n",
        ):
            self.assertIsNone(audit_spec.parse_inspector_output(bad, nonce), bad)

    def test_parse_lean_header_follows_lean_grammar(self) -> None:
        hdr = audit_spec.parse_lean_header(
            "module\n\nprelude\npublic import\n  Expected\nimport Captured\n"
            "public section\ntheorem x : True := trivial\n"
        )
        self.assertTrue(hdr.is_module)
        self.assertTrue(hdr.has_prelude)
        self.assertEqual(
            hdr.imports, ((("public",), "Expected"), ((), "Captured"))
        )
        self.assertTrue(hdr.body_start > 0)
        self.assertEqual(
            audit_spec.parse_lean_header("import\nLean\n").imports,
            (((), "Lean"),),
        )
        with self.assertRaises(ValueError):
            audit_spec.parse_lean_header("prelude\nimport Trusted\u03b1\n")

    def test_lint_accepts_witness_modules(self) -> None:
        allowed = frozenset({"Specs.demo"})
        for ok in (
            "module\nprelude\npublic import Trusted.MirSemantics\n"
            "public import Anneal.Diag.ConcreteRefute\npublic import Captured\n"
            "public import Specs.demo\npublic import Expected\n"
            "-- a comment mentioning macro_rules, import Lean, and #print\n"
            "/- block with axiom -/\n"
            "public section\n"
            "@[simp] theorem helper : True := trivial\n"
            "theorem refute : ¬ Expected.claim := fun h => h.foo\nend\n",
            "prelude\nimport Expected\nimport Anneal.Diag.ConcreteRefute\n"
            "def quoteChar : Char := '\"'\n"
            "def x' : Nat := 0\n"
            "def y' : Nat := x'\n"
            "theorem refute : ¬ Expected.claim := fun h => List.find? id [] |>.elim\n",
        ):
            self.assertIsNone(audit_spec.lint_user_module(ok, allowed), ok)
        code, reason = audit_spec._strip_lean_comments(
            "def q : Char := '\"'\ndef esc : Char := '\\''\ndef s := \"ok\"\n",
            allow_strings=True,
        )
        self.assertEqual(reason, "")
        self.assertIsNotNone(code)

    def test_lint_rejects_metaprogramming_and_imports(self) -> None:
        allowed = frozenset({"Specs.demo"})
        for bad, needle in (
            ("prelude\naxiom «does not depend on any axioms» : False\n", "axiom"),
            ("prelude\nmacro_rules | `(x) => `(y)\n", "macro_rules"),
            ("prelude\nsyntax \"x\" : term\n", "string literals"),
            ("prelude\n#print axioms foo\n", "`#` commands"),
            ("prelude\n#eval 1\n", "`#` commands"),
            ("prelude\npublic meta import Lean.Parser.Command\n", "meta"),
            ("prelude\npublic import Init\n", "import of `Init`"),
            ("prelude\nimport Lean\n", "import of `Lean`"),
            ("prelude\nimport Proof\n", "import of `Proof`"),
            # Import directives split across lines or comments.
            ("prelude\nimport\nLean\n", "import of `Lean`"),
            ("prelude\nimport --c\nLean\n", "import of `Lean`"),
            ("prelude\nimport /- c -/ Init\n", "import of `Init`"),
            ("module\nprelude\npublic\nimport\n  Lean.Elab\n", "import of `Lean.Elab`"),
            ("prelude\nimport all Expected\n", "import all"),
            ("prelude\nimport Trusted\u03b1\n", "malformed import"),
            ("prelude\nimport Expected\ntheorem t : True := trivial\nimport Lean\n",
             "`import`"),
            ("prelude\ntheorem t : True := by_elab return default\n", "by_elab"),
            ("prelude\ndef x : Bool := !by_elab do return default\n", "by_elab"),
            ("prelude\ndef x : Bool := !sorry\n", "sorry"),
            ("prelude\ndef x : Bool := !native_decide\n", "native_decide"),
            ("prelude\ntheorem t : False := _root_.sorry\n", "sorry"),
            ("prelude\ntheorem t : False := sorryAx False true\n", "sorryAx"),
            ("prelude\ntheorem t : False := «sorryAx» False true\n", "sorryAx"),
            ("prelude\ntheorem t : True := by run_tac pure ()\n", "run_tac"),
            ("prelude\nexample : 1 = 1 := by native_decide\n", "native_decide"),
            ("prelude\nexample : 1 = 1 := by decide +native\n", "+native"),
            ("prelude\nexample : 1 = 1 := by decide + native\n", "+ native"),
            ("prelude\nexample : 1 = 1 := by decide +kernel\n", "+kernel"),
            ("prelude\nexample : 1 = 1 := by decide (config := { native := true })\n",
             "config :="),
            ("prelude\nexample : 1 = 1 := by decide!\n", "decide!"),
            ("prelude\nexample : 1 = 1 := by rfl'\n", "rfl'"),
            ("prelude\nexample : 1 = 1 := by grind\n", "grind"),
            ("prelude\nexample : False := sorry\n", "sorry"),
            ("prelude\nexample : False := «sorry»\n", "sorry"),
            ("prelude\nexample : False := Lean.ofReduceBool _ _ rfl\n", "ofReduceBool"),
            ("prelude\nexample : Lean.reduceBool true = true := rfl\n", "reduceBool"),
            ("prelude\nexample : Lean.«reduceBool» true = true := rfl\n", "reduceBool"),
            ("prelude\nexample : Lean.reduceNat 1 = 1 := rfl\n", "reduceNat"),
            ("prelude\nexample := Lean.trustCompiler\n", "trustCompiler"),
            ("prelude\nset_option debug.skipKernelTC true\n", "set_option"),
            ("prelude\n@[implemented_by foo] def x := 1\n", "implemented_by"),
            ("prelude\n@[simp [x], implemented_by foo] def x := 1\n", "implemented_by"),
            ("prelude\n@[simp [x], csimp] theorem x : True := trivial\n", "attributes"),
            ("prelude\n@[simp\ndef x := 1\n", "unterminated attribute"),
            ("prelude\nelab \"x\" : term => pure default\n", "string"),
            ("prelude\ninitialize pure ()\n", "initialize"),
            ("prelude\n«a--» macro_rules\n", "macro_rules"),
            ("prelude\nnamespace «a»\nend «a»axiom Classical.choice : False\n", "axiom"),
            ("prelude\nend «a»macro_rules | `(x) => `(y)\n", "macro_rules"),
            ("prelude\nend «a»elab : term => pure default\n", "elab"),
            ("prelude\nend «a»initialize pure ()\n", "initialize"),
            ("prelude\nend «a»run_cmd pure ()\n", "run_cmd"),
            ("prelude\ntheorem t : True := «b»by_elab pure default\n", "by_elab"),
            ("prelude\nend «a»ofReduceBool\n", "ofReduceBool"),
            ("prelude\nexample := Lean.«ofReduceBool»\n", "ofReduceBool"),
            ("prelude\n@[«extern»] def x := 1\n", "attributes"),
            ("prelude\ntheorem t :\u00a0True := trivial\n", "U+00A0"),
            ("theorem x : True := trivial\n", "prelude"),
            ("import Expected\nprelude\n", "prelude"),
            ("prelude\n/- unterminated\n", "unterminated"),
        ):
            err = audit_spec.lint_user_module(bad, allowed)
            self.assertIsNotNone(err, bad)
            self.assertIn(needle, err, bad)

    def test_identifier_and_case_name_validation(self) -> None:
        for good in ("PoleBRefute.refute", "a", "Specs.x_1.y'"):
            self.assertTrue(audit_spec.is_lean_ident(good), good)
        for bad in ("", 'PoleBRefute.refute\n#print "x"', "a..b", "a.", "1a", "a b", "«a»"):
            self.assertFalse(audit_spec.is_lean_ident(bad), bad)
        for good in ("case", "zerocopy_02.good-spec"):
            self.assertTrue(audit_spec.is_valid_case_name(good), good)
        for bad in ("", ".", "..", "/", "../..", "a/b", "-x", ".hidden"):
            self.assertFalse(audit_spec.is_valid_case_name(bad), bad)


def _request(
    spec_module: str = "Spec",
    *,
    scope_kind: str = "selected_unit",
    compilation: dict[str, Any] | None = None,
    proof_extra: dict[str, Any] | None = None,
    sources: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    scope: dict[str, Any] = {"kind": scope_kind}
    if scope_kind == "selected_unit":
        scope["roots"] = ["demo::f"]
    proof: dict[str, Any] = {
        "source_root": ".",
        "specification": f"{spec_module}.specs",
        "theorem": "Proof.verify",
        "sources": sources
        if sources is not None
        else [
            {"module": spec_module, "path": f"{spec_module}.lean", "role": "specification"},
            {"module": "Proof", "path": "Proof.lean", "role": "proof"},
        ],
    }
    proof.update(proof_extra or {})
    return {
        "schema_version": 1,
        "compilation": compilation
        or {
            "source_root": ".",
            "crate_root": "src/lib.rs",
            "crate_name": "demo",
            "source_files": ["src/lib.rs"],
        },
        "scope": scope,
        "proof": proof,
    }


class SpecLockTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def write_case(
        self,
        sub: str,
        req: dict[str, Any] | str,
        *,
        spec_text: str = "def specs := 1\n",
        proof_text: str = "theorem verify := ()\n",
    ) -> Path:
        d = self.root / sub
        d.mkdir()
        (d / "Spec.lean").write_text(spec_text, encoding="utf-8")
        (d / "Proof.lean").write_text(proof_text, encoding="utf-8")
        text = req if isinstance(req, str) else json.dumps(req)
        (d / "request.json").write_text(text, encoding="utf-8")
        return d / "request.json"

    def lock(self, mut: Path) -> tuple[bool, str]:
        return audit_spec.verify_spec_lock(self.root / "base/request.json", mut)

    def test_identical_requests_lock(self) -> None:
        self.write_case("base", _request())
        locked, msg = self.lock(self.write_case("same", _request()))
        self.assertTrue(locked, msg)
        no_base, msg2 = audit_spec.verify_spec_lock(None, self.root / "same/request.json")
        self.assertFalse(no_base)
        self.assertIn("baseline", msg2)

    def test_program_location_may_differ_but_semantics_may_not(self) -> None:
        self.write_case("base", _request())
        moved = _request(
            compilation={
                "source_root": "../elsewhere",
                "crate_root": "src/main_lib.rs",
                "crate_name": "demo",
                "source_files": ["src/main_lib.rs", "src/extra.rs"],
                "panic": "unwind",
                "edition": "2024",
            }
        )
        self.assertTrue(self.lock(self.write_case("moved", moved))[0])
        for i, (key, val) in enumerate(
            (
                ("panic", "abort"),
                ("overflow_checks", True),
                ("cfg", ["feature=\"x\""]),
                ("env", {"K": "V"}),
                ("edition", "2021"),
                ("crate_type", "bin"),
                ("crate_name", "other"),
                ("stdlib_crate", "core"),
            )
        ):
            req = _request()
            req["compilation"][key] = val
            locked, msg = self.lock(self.write_case(f"flag{i}", req))
            self.assertFalse(locked, key)
            self.assertIn("compilation", msg, key)

    def test_spec_proof_and_module_changes_unlock(self) -> None:
        self.write_case("base", _request())
        locked, msg = self.lock(self.write_case("spec", _request(), spec_text="def specs := 2\n"))
        self.assertFalse(locked)
        self.assertIn("specification source SHA-256", msg)
        locked, msg = self.lock(
            self.write_case("proof", _request(), proof_text="theorem verify := 1\n")
        )
        self.assertFalse(locked)
        self.assertIn("shipped proof source SHA-256", msg)
        locked, msg = self.lock(
            self.write_case("thm", _request(proof_extra={"theorem": "Proof.other"}))
        )
        self.assertFalse(locked)
        self.assertIn("proof.theorem", msg)
        locked, msg = self.lock(
            self.write_case(
                "smod",
                _request(
                    proof_extra={
                        "specification": "Spec.Inner.specs",
                        "specification_module": "Spec",
                    }
                ),
            )
        )
        self.assertFalse(locked)
        locked, msg = self.lock(self.write_case("scope", _request(scope_kind="crate")))
        self.assertFalse(locked)
        self.assertIn("scope", msg)

    def test_malformed_requests_fail_closed(self) -> None:
        self.write_case("base", _request())
        dup = json.dumps(_request())[:-1] + ', "scope": {"kind": "crate"}}'
        locked, msg = self.lock(self.write_case("dup", dup))
        self.assertFalse(locked)
        self.assertIn("duplicate JSON key", msg)
        two = _request(
            sources=[
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Spec", "path": "Proof.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"},
            ]
        )
        locked, msg = self.lock(self.write_case("twice", two))
        self.assertFalse(locked)
        self.assertIn("duplicate proof source module", msg)
        no_spec_mod = _request(proof_extra={"specification": "Other.specs"})
        locked, msg = self.lock(self.write_case("nospecmod", no_spec_mod))
        self.assertFalse(locked)
        self.assertIn("specification module Other", msg)
        extra_key = _request()
        extra_key["proof"]["sources"][0]["extra"] = 1
        self.assertFalse(self.lock(self.write_case("extrakey", extra_key))[0])

    def test_symlinked_source_inside_root_is_rejected(self) -> None:
        self.write_case("base", _request())
        mut = self.write_case("link", _request())
        (mut.parent / "Spec.lean").unlink()
        (mut.parent / "real").mkdir()
        (mut.parent / "real/Spec.lean").write_text("def specs := 1\n", encoding="utf-8")
        (mut.parent / "Spec.lean").symlink_to(mut.parent / "real/Spec.lean")
        locked, msg = self.lock(mut)
        self.assertFalse(locked)
        self.assertIn("symlink", msg)
        dir_link = _request(
            sources=[
                {"module": "Spec", "path": "alias/Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"},
            ]
        )
        mut2 = self.write_case("dirlink", dir_link)
        (mut2.parent / "alias").symlink_to(mut2.parent)
        locked, msg = self.lock(mut2)
        self.assertFalse(locked)
        self.assertIn("symlink", msg)

    def test_defaults_and_explicit_specification_module(self) -> None:
        req = _request()
        del req["proof"]["specification"]
        del req["proof"]["theorem"]
        self.write_case("base", req)
        self.assertTrue(self.lock(self.write_case("dflt", req))[0])
        locked = audit_spec.load_locked_request(self.root / "dflt/request.json")
        self.assertEqual(locked.specification, "Spec.specs")
        self.assertEqual(locked.specification_module, "Spec")
        self.assertEqual(locked.theorem_module, "Proof")
        explicit = _request(
            proof_extra={"specification": "Specs.Demo.specs", "specification_module": "Spec"}
        )
        d = self.root / "explicit"
        d.mkdir()
        (d / "Spec.lean").write_text("x", encoding="utf-8")
        (d / "Proof.lean").write_text("y", encoding="utf-8")
        (d / "request.json").write_text(json.dumps(explicit), encoding="utf-8")
        got = audit_spec.load_locked_request(d / "request.json")
        self.assertEqual(got.specification_module, "Spec")


class SandboxTests(unittest.TestCase):
    def test_argv_policy(self) -> None:
        sb = audit_spec.LeanSandbox(Path("/usr/bin/bwrap"))
        argv = sb.argv(
            ["/tc/bin/lean", "x.lean"],
            ro=[Path("/stage/lib"), Path("/tc")],
            rw=[Path("/stage/out/1")],
            cwd=Path("/stage/src"),
            env={"PATH": "/tc/bin"},
        )
        joined = " ".join(argv)
        for flag in ("--unshare-all", "--disable-userns", "--die-with-parent",
                     "--clearenv", "--cap-drop ALL", "--tmpfs /"):
            self.assertIn(flag, joined)
        self.assertIn("--ro-bind /stage/lib /stage/lib", joined)
        self.assertIn("--bind /stage/out/1 /stage/out/1", joined)
        self.assertNotIn("--bind /stage/lib", joined)
        self.assertEqual(argv[argv.index("--") + 1:], ["/tc/bin/lean", "x.lean"])
        with self.assertRaises(ValueError):
            sb.argv(["x"], ro=[Path("rel")], rw=[], cwd=Path("/"), env={})

    def test_probe_fails_closed_without_bwrap(self) -> None:
        with self.assertRaises(audit_spec.SandboxUnavailable):
            with tempfile.TemporaryDirectory() as tmp:
                audit_spec.LeanSandbox.probe((Path(tmp) / "bwrap",))

    def test_lean_env_is_allowlisted(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            lean = _write_exec(Path(tmp) / "tc/bin/lean", "#!/bin/sh\n")
            (Path(tmp) / "tc/lib/lean").mkdir(parents=True)
            with mock.patch.dict(
                os.environ,
                {"ACTIONS_RUNTIME_TOKEN": "s3cret", "LD_PRELOAD": "/x.so", "LEAN_PATH": "/evil"},
            ):
                env = audit_spec._lean_env(lean, Path("/stage/lib"))
            self.assertEqual(
                set(env), {"PATH", "HOME", "TMPDIR", "LANG", "LC_ALL", "LEAN_SYSROOT", "LEAN_PATH"}
            )
            self.assertEqual(env["LEAN_PATH"], "/stage/lib")
            self.assertTrue(env["PATH"].startswith(str(lean.parent)))

    def test_real_bwrap_blocks_lib_writes_env_and_host_files(self) -> None:
        """`[real measurement]` of the `bwrap` policy (skipped without bwrap)."""
        try:
            sandbox = audit_spec.LeanSandbox.probe()
        except audit_spec.SandboxUnavailable as exc:
            self.skipTest(str(exc))
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            secret = root / "host-secret.txt"
            secret.write_text("secret", encoding="utf-8")
            # Mimics `lean -DwarningAsError=true -R <root> -o <out> <src>`.
            lean = _write_exec(
                root / "tc/bin/lean",
                f"""#!/bin/sh
out="$5"
fail() {{ echo "$1" >&2; exit 1; }}
( echo pwned > "$LEAN_PATH/Expected.olean" ) 2>/dev/null && fail LIB_WRITABLE
[ -z "$ACTIONS_RUNTIME_TOKEN" ] || fail TOKEN_LEAKED
[ -e "{secret}" ] && fail HOST_VISIBLE
[ -n "$(ls -A "{Path.home()}" 2>/dev/null)" ] && fail HOME_VISIBLE
echo planted > "$(dirname "$out")/Expected.olean"
echo olean > "$out"
""",
            )
            stage = audit_spec._LeanStage(
                sandbox=sandbox,
                lean_bin=lean,
                stage_dir=root / "stage",
                lean_memory_mb=None,
                timeout=60,
            )
            stage.lib_dir.mkdir(parents=True)
            (stage.lib_dir / "Expected.olean").write_text("exp", encoding="utf-8")
            src_dir = root / "stage/src"
            src_dir.mkdir()
            (src_dir / "PoleBRefute.lean").write_text("prelude\n", encoding="utf-8")
            with mock.patch.dict(os.environ, {"ACTIONS_RUNTIME_TOKEN": "s3cret"}):
                err = stage.compile(
                    module="PoleBRefute",
                    src=src_dir / "PoleBRefute.lean",
                    root=src_dir,
                    overwrite=False,
                )
            self.assertIsNone(err)
            self.assertEqual(
                (stage.lib_dir / "Expected.olean").read_text(encoding="utf-8"), "exp"
            )
            self.assertEqual(
                (stage.lib_dir / "PoleBRefute.olean").read_text(encoding="utf-8"),
                "olean\n",
            )


class StagePlanTests(unittest.TestCase):
    def test_missing_mirwp_execution_is_compiled_from_theory(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            theory = root / "theory"
            (theory / "Anneal/Diag").mkdir(parents=True)
            (theory / "Anneal/MirWp").mkdir(parents=True)
            (theory / "Anneal/Diag/ConcreteRefute.lean").write_text(
                "module\nprelude\npublic import Init.NotationExtra\n"
                "public import Trusted.MirAst\npublic import Anneal.MirWp.Core\n"
                "public import Anneal.MirWp.Execution\n",
                encoding="utf-8",
            )
            (theory / "Anneal/MirWp/Core.lean").write_text(
                "module\nprelude\npublic import Trusted.MirAst\n", encoding="utf-8"
            )
            (theory / "Anneal/MirWp/Execution.lean").write_text(
                "module\n/- doc -/\nprelude\npublic import\n  Anneal.MirWp.Core\n"
                'def s := "x"\n',
                encoding="utf-8",
            )
            lib = root / "lib"
            (lib / "Trusted").mkdir(parents=True)
            (lib / "Trusted/MirAst.olean").write_text("t", encoding="utf-8")
            plan = audit_spec.concrete_refute_build_plan(lib, (theory,))
            self.assertEqual(
                [m for m, _, _ in plan],
                ["Anneal.MirWp.Core", "Anneal.MirWp.Execution", "Anneal.Diag.ConcreteRefute"],
            )
            (lib / "Anneal/MirWp").mkdir(parents=True)
            (lib / "Anneal/MirWp/Core.olean").write_text("c", encoding="utf-8")
            plan = audit_spec.concrete_refute_build_plan(lib, (theory,))
            self.assertEqual(
                [m for m, _, _ in plan],
                ["Anneal.MirWp.Execution", "Anneal.Diag.ConcreteRefute"],
            )
            (lib / "Trusted/MirAst.olean").unlink()
            with self.assertRaises(audit_spec.StageError):
                audit_spec.concrete_refute_build_plan(lib, (theory,))


class EndToEndHarnessTests(unittest.TestCase):
    """Drives `audit_case` with fake `cargo-anneal`/`lean` binaries."""

    def _build_fixture(self, root: Path, *, scope_kind: str = "selected_unit") -> dict[str, Any]:
        theory = root / "theory"
        (theory / "Anneal/Diag").mkdir(parents=True)
        (theory / "Anneal/MirWp").mkdir(parents=True)
        # As in the real file, `ConcreteRefute` imports `Anneal.MirWp.*`,
        # which the fake export below omits; `Anneal.ExtraHelper` is only
        # imported when a witness explicitly requests it.
        (theory / "Anneal/Diag/ConcreteRefute.lean").write_text(
            "module\nprelude\npublic import Anneal.MirWp.Execution\n", encoding="utf-8"
        )
        (theory / "Anneal/MirWp/Execution.lean").write_text(
            "module\nprelude\n", encoding="utf-8"
        )
        (theory / "Anneal/ExtraHelper.lean").write_text(
            "module\nprelude\n", encoding="utf-8"
        )

        for name, body_flag in (("base", "good"), ("mut", "bad")):
            d = root / name
            d.mkdir()
            (d / "Spec.lean").write_text("module\nprelude\ndef specs := True\n", encoding="utf-8")
            (d / "Proof.lean").write_text("module\nprelude\n", encoding="utf-8")
            (d / "marker.txt").write_text(body_flag, encoding="utf-8")
            (d / "request.json").write_text(
                json.dumps(_request(scope_kind=scope_kind)), encoding="utf-8"
            )

        witness_hdr = "module\nprelude\npublic import Expected\n"
        files = {
            "nonvac": witness_hdr + "-- NonVacuity\n",
            "poleb_good": witness_hdr + "-- GOOD_POLE_B\n",
            "poleb_weak": witness_hdr + "-- WEAK_SPEC\n",
            "poleb_sorry": witness_hdr + "-- SORRY_POLE_B\n",
            "poleb_spoof": "prelude\naxiom «does not depend on any axioms» : False\n",
            "poleb_forge": "prelude\nimport\nLean\ntheorem refute : True := by_elab pure default\n",
            "poleb_nonmodule": "prelude\nimport Expected\n-- GOOD_POLE_B\n",
        }
        paths = {}
        for key, text in files.items():
            paths[key] = root / f"{key}.lean"
            paths[key].write_text(text, encoding="utf-8")

        verified = audit_spec.CLEAN_VERIFIED_STATUS[scope_kind]
        cli = _write_exec(
            root / "fake-cargo-anneal",
            f"""#!{sys.executable}
import json, os, pathlib, sys
args = sys.argv[1:]
assert "ACTIONS_RUNTIME_TOKEN" not in os.environ
req = pathlib.Path(args[args.index("--request") + 1])
art = pathlib.Path(args[args.index("--artifacts") + 1])
marker = (req.parent / "marker.txt").read_text().strip()
override = (req.parent / "receipt.json")
(art / "generated").mkdir(parents=True, exist_ok=True)
(art / "generated/Expected.lean").write_text("module\\nprelude\\n", encoding="utf-8")
(art / "lean-lib").mkdir(parents=True, exist_ok=True)
(art / "lean-lib/Trusted").mkdir(parents=True, exist_ok=True)
for mod in ("Expected", "Captured", "Spec",
            "Trusted/MirAst", "Trusted/MirModel", "Trusted/MirSemantics"):
    (art / "lean-lib" / (mod + ".olean")).write_text(mod, encoding="utf-8")
leaked_suffix = (req.parent / "leak_suffix.txt")
if leaked_suffix.exists():
    sfx = leaked_suffix.read_text().strip()
    (art / "lean-lib" / ("Proof" + sfx)).write_text("leaked", encoding="utf-8")
if override.exists():
    print(override.read_text())
    raise SystemExit(0)
if marker == "good":
    (art / "lean-lib/Proof.olean").write_text("proof", encoding="utf-8")
    print(json.dumps({{"schema_version": 3, "status": {verified!r}, "taint_reasons": [],
                      "elaboration_sandbox": "linux_bwrap", "deferred": []}}))
    raise SystemExit(0)
print({json.dumps(json.dumps(_failure_receipt(detail="Proof.verify mismatch")))})
raise SystemExit(1)
""",
        )
        lean = _write_exec(
            root / "tc/bin/lean",
            f"""#!{sys.executable}
import json, os, pathlib, sys
assert "ACTIONS_RUNTIME_TOKEN" not in os.environ
if "--run" in sys.argv:
    assert "LEAN_PATH" not in os.environ
    run_idx = sys.argv.index("--run")
    script_text = pathlib.Path(sys.argv[run_idx + 1]).read_text(encoding="utf-8")
    for req_tok in ("import Lean", "toKernelEnv.replay", "auditCheckOrigin",
                    "nv_claim", "AUDIT_SPEC_AXIOMS:"):
        assert req_tok in script_text, req_tok
    args = sys.argv[run_idx + 2:]
    lib, module, decl, nonce, mode = args[:5]
    assert decl == "__auditSpecCheck", decl
    lib_dir = pathlib.Path(lib)
    if module == "PoleBVerify":
        assert mode == "not_claim", mode
        ref_olean = (lib_dir / "PoleBRefute.olean").read_text(encoding="utf-8")
        if "INSPECTOR_MALFORMED" in ref_olean:
            print("garbage without nonce")
            raise SystemExit(0)
        axioms = ["propext", "sorryAx"] if "SORRY_POLE_B" in ref_olean else ["propext"]
    else:
        assert module == "NonVacuityVerify", module
        assert mode == "nv_claim", mode
        assert args[5:] == ["AuditSpecNvClaim.claim@AuditSpecNvClaim",
                            "Spec.specs@Spec", "Captured.program@Captured"], args
        assert (lib_dir / "AuditSpecNvClaim.olean").is_file()
        nv_olean = (lib_dir / "NonVacuity.olean").read_text(encoding="utf-8")
        if "INSPECTOR_MALFORMED" in nv_olean:
            print("garbage without nonce")
            raise SystemExit(0)
        axioms = []
    print(f"AUDIT_SPEC_AXIOMS:{{nonce}}:{{json.dumps(axioms)}}")
    raise SystemExit(0)
lib = pathlib.Path(os.environ["LEAN_PATH"])
out = pathlib.Path(sys.argv[sys.argv.index("-o") + 1])
src = pathlib.Path(sys.argv[-1])
text = src.read_text(encoding="utf-8")
if src.name == "AuditSpecNvClaim.lean":
    assert "Trusted.MirSemantics.ValidEntryArgs" in text, text
    assert "Anneal.Diag.ConcreteRefute" not in text, text
for line in text.splitlines():
    if line.startswith(("import ", "public import ")):
        dep = line.split()[-1]
        assert (lib / (dep.replace(".", "/") + ".olean")).is_file(), dep
if "SIGKILL_ME" in text:
    os.kill(os.getpid(), 9)
if "MAX_HEARTBEATS_ME" in text:
    print("error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)", file=sys.stderr)
    raise SystemExit(1)
if "UNKNOWN_IDENT_ME" in text:
    print("error(lean.unknownIdentifier): Unknown identifier `renamedLemma`", file=sys.stderr)
    raise SystemExit(1)
if "LINTER_WARN_ME" in text:
    print("error: Variable name `unused` is not explicitly referenced.\\nNote: This linter can be disabled with `set_option linter.unusedVariables false`", file=sys.stderr)
    raise SystemExit(1)
if "WEAK_SPEC" in text:
    print("error: type mismatch proving False", file=sys.stderr)
    raise SystemExit(1)
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text("olean:" + src.name + "\\n" + text, encoding="utf-8")
""",
        )
        capture = _write_exec(root / "fake-capture", "#!/bin/sh\nexit 0\n")
        sysroot = root / "sysroot"
        sysroot.mkdir()
        sandbox = DirectSandbox()
        common = dict(
            baseline_request=root / "base/request.json",
            mutant_request=root / "mut/request.json",
            nonvacuity_path=paths["nonvac"],
            cli=cli,
            capture=capture,
            sysroot=sysroot,
            lean=lean,
            theory_root=theory,
            artifacts_root=root / "artifacts",
            sandbox=sandbox,
        )
        return {"paths": paths, "common": common, "sandbox": sandbox, "root": root}

    def test_adequate_vs_vacuous_and_cheats(self) -> None:
        with tempfile.TemporaryDirectory() as tmp, mock.patch.dict(
            os.environ, {"ACTIONS_RUNTIME_TOKEN": "s3cret"}
        ):
            fx = self._build_fixture(Path(tmp))
            p, common = fx["paths"], fx["common"]
            good = audit_spec.audit_case(name="good", pole_b_path=p["poleb_good"], **common)
            self.assertEqual(good.classification, "adequate", good.detail)
            self.assertTrue(good.dual_polar_adequate)
            self.assertTrue(good.baseline_verified)
            self.assertTrue(good.pre_non_vacuous)
            self.assertTrue(good.pole_b["kernel_replayed"])

            # Every Lean process ran with an allowlisted env and no writable
            # view of the staged library.
            calls = fx["sandbox"].calls
            self.assertTrue(calls)
            for call in calls:
                self.assertNotIn("ACTIONS_RUNTIME_TOKEN", call["env"])
                for rw in call["rw"]:
                    self.assertIn("out", rw.parts)
                    for ro in call["ro"]:
                        self.assertFalse(ro.is_relative_to(rw), (ro, rw))
            compiled = [c["cmd"][-1] for c in calls if "-o" in c["cmd"]]
            self.assertTrue(any(s.endswith("Anneal/MirWp/Execution.lean") for s in compiled))

            weak = audit_spec.audit_case(name="weak", pole_b_path=p["poleb_weak"], **common)
            self.assertFalse(weak.dual_polar_adequate)
            self.assertTrue(weak.pole_a_clean_reject)
            self.assertEqual(weak.classification, "vacuous_spec_false_kill")

            cheated = audit_spec.audit_case(name="sorry", pole_b_path=p["poleb_sorry"], **common)
            self.assertFalse(cheated.pole_b_refuted)
            self.assertIn("sorryAx", cheated.detail)

            for key in ("poleb_spoof", "poleb_forge"):
                res = audit_spec.audit_case(name=key, pole_b_path=p[key], **common)
                self.assertFalse(res.pole_b_refuted, key)
                self.assertIn("rejected by lint", res.detail, key)

            mismatch = audit_spec.audit_case(
                name="nonmodule", pole_b_path=p["poleb_nonmodule"], **common
            )
            self.assertFalse(mismatch.pole_b_refuted)
            self.assertIn("must start with `module`", mismatch.detail)

            for bad_name in ("/", "..", "../..", "a/b"):
                with self.assertRaises(ValueError, msg=bad_name):
                    audit_spec.audit_case(name=bad_name, pole_b_path=p["poleb_good"], **common)
            with self.assertRaises(ValueError):
                audit_spec.audit_case(
                    name="inject",
                    pole_b_path=p["poleb_good"],
                    pole_b_decl='PoleBRefute.refute\n#print "x"',
                    **common,
                )
            unlocked = audit_spec.audit_case(
                name="no_baseline",
                pole_b_path=p["poleb_good"],
                **dict(common, baseline_request=None),
            )
            self.assertEqual(unlocked.classification, "spec_unlocked")

    def test_crate_scope_baseline_uses_crate_verified(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fx = self._build_fixture(Path(tmp), scope_kind="crate")
            res = audit_spec.audit_case(
                name="crate", pole_b_path=fx["paths"]["poleb_good"], **fx["common"]
            )
            self.assertTrue(res.baseline_verified, res.detail)
            self.assertEqual(res.classification, "adequate", res.detail)

    def test_unclean_baseline_receipts_fail(self) -> None:
        for receipt in (
            _verified_receipt("tainted_selected_unit_verified"),
            _verified_receipt("crate_verified"),
            dict(_verified_receipt(), elaboration_sandbox=None),
            {k: v for k, v in _verified_receipt().items() if k != "taint_reasons"},
        ):
            with tempfile.TemporaryDirectory() as tmp:
                fx = self._build_fixture(Path(tmp))
                (fx["root"] / "base/receipt.json").write_text(json.dumps(receipt))
                res = audit_spec.audit_case(
                    name="b", pole_b_path=fx["paths"]["poleb_good"], **fx["common"]
                )
                self.assertEqual(res.classification, "baseline_failed", receipt)
                self.assertFalse(res.baseline_verified)

    def test_nonvacuity_witness_is_required(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fx = self._build_fixture(Path(tmp))
            res = audit_spec.audit_case(
                name="nonv",
                pole_b_path=fx["paths"]["poleb_good"],
                **dict(fx["common"], nonvacuity_path=None),
            )
            self.assertFalse(res.dual_polar_adequate)
            self.assertEqual(res.classification, "nonvacuity_missing")
            self.assertFalse(audit_spec.matches_expectation(res, False))

    def test_negative_expectations_need_semantic_verdicts(self) -> None:
        def res(classification: str) -> audit_spec.CaseResult:
            return audit_spec.CaseResult(
                name="x", baseline_verified=None, spec_locked=True,
                pre_non_vacuous=None, pole_a_clean_reject=False,
                pole_b_refuted=False, dual_polar_adequate=False,
                classification=classification, detail="", pole_a={}, pole_b={},
            )
        for cls in ("vacuous_spec_false_kill", "pre_vacuous", "mutant_verified"):
            self.assertTrue(audit_spec.matches_expectation(res(cls), False), cls)
            self.assertFalse(audit_spec.matches_expectation(res(cls), True), cls)
        for cls in ("baseline_failed", "spec_unlocked", "crash_masquerade",
                    "resource_limit", "malformed_output", "unexpected_failure",
                    "pole_b_error", "nonvacuity_error", "nonvacuity_missing"):
            self.assertFalse(audit_spec.matches_expectation(res(cls), False), cls)

    def test_artifacts_dir_never_replaces_inputs_or_foreign_dirs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fx = self._build_fixture(Path(tmp))
            root = fx["root"]
            # A case directory that is (or contains) an input is refused.
            for art_root, name in ((root, "base"), (root.parent, root.name)):
                with self.assertRaises(ValueError, msg=name):
                    audit_spec.audit_case(
                        name=name,
                        pole_b_path=fx["paths"]["poleb_good"],
                        **dict(fx["common"], artifacts_root=art_root),
                    )
            self.assertTrue((root / "base/request.json").is_file())
            foreign = root / "artifacts/keep"
            foreign.mkdir(parents=True)
            (foreign / "precious.txt").write_text("x", encoding="utf-8")
            with self.assertRaises(ValueError):
                audit_spec.audit_case(
                    name="keep", pole_b_path=fx["paths"]["poleb_good"], **fx["common"]
                )
            self.assertTrue((foreign / "precious.txt").is_file())
            # Re-running a case replaces only its own marked directory.
            for _ in range(2):
                res = audit_spec.audit_case(
                    name="rerun", pole_b_path=fx["paths"]["poleb_good"], **fx["common"]
                )
                self.assertEqual(res.classification, "adequate", res.detail)

    def test_memory_cap_reaches_every_lean_process(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fx = self._build_fixture(Path(tmp))
            res = audit_spec.audit_case(
                name="mem",
                pole_b_path=fx["paths"]["poleb_good"],
                lean_memory_mb=2048,
                **fx["common"],
            )
            self.assertEqual(res.classification, "adequate", res.detail)
            calls = fx["sandbox"].calls
            self.assertTrue(calls)
            for call in calls:
                self.assertEqual(call["cmd"][1:3], ["-M", "2048"], call["cmd"])

    def test_missing_theory_dependency_is_a_structured_error(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fx = self._build_fixture(Path(tmp))
            (fx["common"]["theory_root"] / "Anneal/MirWp/Execution.lean").unlink()
            res = audit_spec.audit_case(
                name="nodep", pole_b_path=fx["paths"]["poleb_good"], **fx["common"]
            )
            self.assertEqual(res.classification, "nonvacuity_error", res.detail)
            self.assertIn("Anneal.MirWp.Execution", res.detail)
            self.assertTrue(res.nonvacuity["infrastructure_error"])

    def test_infrastructure_failures_never_satisfy_negative_expectations(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fx = self._build_fixture(Path(tmp))
            root, p, common = fx["root"], fx["paths"], fx["common"]
            hdr = "module\nprelude\npublic import Expected\n"
            for name, body in (
                ("sigkill", hdr + "-- SIGKILL_ME\n"),
                ("hb", hdr + "-- MAX_HEARTBEATS_ME\n"),
                ("bad_insp", hdr + "-- INSPECTOR_MALFORMED\n"),
                ("unknown_id", hdr + "-- UNKNOWN_IDENT_ME\n"),
                ("linter_warn", hdr + "-- LINTER_WARN_ME\n"),
                ("missing_anneal", hdr + "public import Anneal.NoSuchMod\n"),
                ("extra_anneal", hdr + "public import Anneal.ExtraHelper\n-- GOOD_POLE_B\n"),
            ):
                p[name] = root / f"{name}.lean"
                p[name].write_text(body, encoding="utf-8")

            # A witness importing a pruned `Anneal.*` module stages it cleanly.
            extra_ok = audit_spec.audit_case(
                name="c_extra_anneal", pole_b_path=p["extra_anneal"], **common
            )
            self.assertEqual(extra_ok.classification, "adequate", extra_ok.detail)

            for key in ("sigkill", "hb", "bad_insp", "unknown_id", "linter_warn",
                        "missing_anneal", "poleb_sorry",
                        "poleb_spoof", "poleb_forge", "poleb_nonmodule"):
                res = audit_spec.audit_case(name=f"c_{key}", pole_b_path=p[key], **common)
                self.assertEqual(res.classification, "pole_b_error", (key, res))
                self.assertTrue(res.pole_b["infrastructure_error"], key)
                self.assertFalse(audit_spec.matches_expectation(res, False), key)

            for nv_key in ("bad_insp", "unknown_id", "linter_warn", "missing_anneal"):
                nv_bad = audit_spec.audit_case(
                    name=f"nv_{nv_key}",
                    pole_b_path=p["poleb_good"],
                    **dict(common, nonvacuity_path=p[nv_key]),
                )
                self.assertEqual(nv_bad.classification, "nonvacuity_error", (nv_key, nv_bad))
                self.assertFalse(audit_spec.matches_expectation(nv_bad, False), nv_key)

            # Timeouts during witness compile and during axiom inspection are
            # classified as `*_error`, never as semantic inadequacy verdicts.
            class TimeoutOnTargetSandbox(DirectSandbox):
                def __init__(self, trigger: str) -> None:
                    super().__init__()
                    self.trigger = trigger

                def run(self, cmd, *, ro, rw, cwd, env, timeout):  # type: ignore[no-untyped-def]
                    joined = " ".join(cmd)
                    if self.trigger in joined:
                        raise subprocess.TimeoutExpired(cmd=cmd, timeout=timeout)
                    return super().run(cmd, ro=ro, rw=rw, cwd=cwd, env=env, timeout=timeout)

            for trig, want_cls in (
                ("AuditSpecInspect.lean", "nonvacuity_error"),
                ("PoleBRefute.lean", "pole_b_error"),
                ("PoleBVerify.lean", "pole_b_error"),
            ):
                res_t = audit_spec.audit_case(
                    name=f"to_{want_cls}_{trig[:5]}",
                    pole_b_path=p["poleb_good"],
                    **dict(common, sandbox=TimeoutOnTargetSandbox(trig)),
                )
                self.assertEqual(res_t.classification, want_cls, res_t.detail)
                self.assertFalse(audit_spec.matches_expectation(res_t, False), trig)

    def test_leaked_compiled_proof_artifacts_rejected_in_pole_b(self) -> None:
        for suffix in (".olean", ".olean.private", ".olean.server", ".ilean"):
            with tempfile.TemporaryDirectory() as tmp:
                fx = self._build_fixture(Path(tmp))
                (fx["root"] / "mut/leak_suffix.txt").write_text(suffix, encoding="utf-8")
                res = audit_spec.audit_case(
                    name="leak", pole_b_path=fx["paths"]["poleb_good"], **fx["common"]
                )
                self.assertEqual(res.classification, "pole_b_error", (suffix, res.detail))
                self.assertIn("Proof" + suffix, res.detail)
                self.assertTrue(res.pole_b["infrastructure_error"])
                self.assertFalse(audit_spec.matches_expectation(res, False))

    def test_timeouts_and_invalid_utf8_do_not_crash_suite_json_out(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fx = self._build_fixture(Path(tmp))
            root, p, common = fx["root"], fx["paths"], fx["common"]
            # Bad UTF-8 on Pole A stdout/stderr -> `malformed_output`.
            bad_cli = _write_exec(
                root / "bad-utf8-cli",
                f"""#!{sys.executable}
import json, pathlib, sys
args = sys.argv[1:]
req = pathlib.Path(args[args.index("--request") + 1])
art = pathlib.Path(args[args.index("--artifacts") + 1])
marker = (req.parent / "marker.txt").read_text().strip()
(art / "generated").mkdir(parents=True, exist_ok=True)
(art / "generated/Expected.lean").write_text("module\\nprelude\\n", encoding="utf-8")
(art / "lean-lib/Trusted").mkdir(parents=True, exist_ok=True)
for mod in ("Expected", "Captured", "Spec",
            "Trusted/MirAst", "Trusted/MirModel", "Trusted/MirSemantics"):
    (art / "lean-lib" / (mod + ".olean")).write_text(mod, encoding="utf-8")
if marker == "good":
    print(json.dumps({{"schema_version": 3, "status": "selected_unit_verified",
                      "taint_reasons": [], "elaboration_sandbox": "linux_bwrap",
                      "deferred": []}}))
    raise SystemExit(0)
sys.stdout.buffer.write(b"\\xff\\xfe\\xfd")
raise SystemExit(1)
""",
            )
            res_utf8 = audit_spec.audit_case(
                name="bad_utf8",
                pole_b_path=p["poleb_good"],
                **dict(common, cli=bad_cli),
            )
            self.assertEqual(res_utf8.classification, "malformed_output", res_utf8.detail)
            self.assertFalse(audit_spec.matches_expectation(res_utf8, False))

            with mock.patch.object(
                audit_spec.anneal_ci_lib,
                "run_cargo_anneal_verify",
                side_effect=subprocess.TimeoutExpired(cmd=["cli"], timeout=1.0),
            ):
                res_bto = audit_spec.audit_case(
                    name="base_to", pole_b_path=p["poleb_good"], **common
                )
            self.assertEqual(res_bto.classification, "baseline_failed")
            self.assertFalse(audit_spec.matches_expectation(res_bto, False))

            orig_run = subprocess.run

            def pole_a_timeout(cmd, *a, **kw):  # type: ignore[no-untyped-def]
                if isinstance(cmd, list) and cmd and str(cmd[0]) == str(common["cli"]):
                    if str(root / "mut") in " ".join(str(x) for x in cmd):
                        raise subprocess.TimeoutExpired(cmd=cmd, timeout=1.0)
                return orig_run(cmd, *a, **kw)

            suite_file = root / "suite.json"
            json_out = root / "report.json"
            suite_file.write_text(
                json.dumps(
                    {
                        "cases": [
                            {
                                "name": "pole_a_to",
                                "baseline_request": str(common["baseline_request"]),
                                "mutant_request": str(common["mutant_request"]),
                                "pole_b": str(p["poleb_good"]),
                                "nonvacuity": str(common["nonvacuity_path"]),
                                "expect_adequate": False,
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )
            with (
                mock.patch.object(
                    audit_spec.LeanSandbox, "probe", return_value=fx["sandbox"]
                ),
                mock.patch("subprocess.run", side_effect=pole_a_timeout),
            ):
                rc = audit_spec.main(
                    [
                        "--suite",
                        str(suite_file),
                        "--cli",
                        str(common["cli"]),
                        "--capture",
                        str(common["capture"]),
                        "--sysroot",
                        str(common["sysroot"]),
                        "--lean",
                        str(common["lean"]),
                        "--theory-root",
                        str(common["theory_root"]),
                        "--json-out",
                        str(json_out),
                    ]
                )
            self.assertEqual(rc, 1)
            report = json.loads(json_out.read_text(encoding="utf-8"))
            self.assertEqual(report["cases"][0]["classification"], "resource_limit")
            self.assertFalse(report["cases"][0]["matched_expectation"])

    def test_real_lean_axiom_inspector_and_nonvacuity_claim(self) -> None:
        """`[real measurement]` Executes `AXIOM_INSPECTOR_SRC` with real Lean."""
        try:
            sandbox = audit_spec.LeanSandbox.probe()
        except audit_spec.SandboxUnavailable as exc:
            self.skipTest(str(exc))
        anneal_root = Path(__file__).resolve().parent.parent
        tools = audit_spec.anneal_ci_lib.resolve_cli_tools(
            anneal_root, mock.Mock(lean=None), names=("lean",)
        )
        lean_bin = tools.get("lean")
        if lean_bin is None or not Path(lean_bin).is_file():
            cand = Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
            lean_bin = cand if cand.is_file() else None
        if lean_bin is None:
            self.skipTest("no real Lean binary found")
        lean_bin = Path(lean_bin).resolve()

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            stage = audit_spec._LeanStage(
                sandbox=sandbox,
                lean_bin=lean_bin,
                stage_dir=root / "stage",
                lean_memory_mb=2048,
                timeout=120.0,
            )
            stage.lib_dir.mkdir(parents=True)
            src = root / "src"
            src.mkdir()

            def write_and_compile(mod: str, text: str) -> None:
                f = src / (mod.replace(".", "/") + ".lean")
                f.parent.mkdir(parents=True, exist_ok=True)
                f.write_text(text, encoding="utf-8")
                err = stage.compile(module=mod, src=f, root=src, overwrite=True)
                self.assertIsNone(err, (mod, err))

            write_and_compile(
                "Expected",
                "module\nprelude\npublic import Init.Core\n"
                "public section\n@[expose] def Expected.claim : Prop := False\nend\n",
            )
            write_and_compile(
                "PoleBVerify",
                "module\nprelude\npublic import Expected\n"
                "public section\n"
                "theorem __auditSpecCheck : ¬ _root_.Expected.claim := id\nend\n",
            )
            axioms, err = audit_spec._run_axiom_inspector(
                stage=stage,
                module_name="PoleBVerify",
                decl="__auditSpecCheck",
                inspector_spec=("not_claim", "Expected.claim@Expected"),
            )
            self.assertEqual(err, "")
            self.assertEqual(axioms, ())

            # Wrong origin module is rejected by `auditCheckOrigin`.
            bad_ax, bad_err = audit_spec._run_axiom_inspector(
                stage=stage,
                module_name="PoleBVerify",
                decl="__auditSpecCheck",
                inspector_spec=("not_claim", "Expected.claim@OtherMod"),
            )
            self.assertIsNone(bad_ax)
            self.assertIn("comes from module Expected", bad_err)

            # `sorryAx` from `Init.Prelude` is reported by the real inspector;
            # any non-foundation axiom (including a spoofed `Classical.choice`
            # or user `axiom`) is rejected directly by origin checking.
            write_and_compile(
                "SorryVerify",
                "module\nprelude\npublic import Init.Core\npublic import Expected\n"
                "public section\n"
                "set_option warn.sorry false in\n"
                "theorem __auditSpecCheck : ¬ _root_.Expected.claim :=\n"
                "  sorryAx (¬ _root_.Expected.claim) false\nend\n",
            )
            s_ax, s_err = audit_spec._run_axiom_inspector(
                stage=stage,
                module_name="SorryVerify",
                decl="__auditSpecCheck",
                inspector_spec=("not_claim", "Expected.claim@Expected"),
            )
            self.assertEqual(s_err, "")
            self.assertEqual(s_ax, ("sorryAx",))

            write_and_compile(
                "ForeignAxiomVerify",
                "module\nprelude\npublic import Init.Core\npublic import Expected\n"
                "public section\n"
                "axiom mySorry : ¬ _root_.Expected.claim\n"
                "theorem __auditSpecCheck : ¬ _root_.Expected.claim := mySorry\nend\n",
            )
            fa_ax, fa_err = audit_spec._run_axiom_inspector(
                stage=stage,
                module_name="ForeignAxiomVerify",
                decl="__auditSpecCheck",
                inspector_spec=("not_claim", "Expected.claim@Expected"),
            )
            self.assertIsNone(fa_ax)
            self.assertIn("non-foundation axiom", fa_err)

            # Top-level `propext` spoof when `Init.Core` is omitted.
            write_and_compile(
                "TrueExpected",
                "module\nprelude\npublic import Init.Prelude\n"
                "public section\n@[expose] def TrueExpected.claim : Prop := True\nend\n",
            )
            write_and_compile(
                "RootPropextSpoof",
                "module\nprelude\npublic import Init.Prelude\n"
                "public import TrueExpected\npublic section\n"
                "axiom propext : Not _root_.TrueExpected.claim\n"
                "theorem __auditSpecCheck : Not _root_.TrueExpected.claim := propext\n"
                "end\n",
            )
            rp_ax, rp_err = audit_spec._run_axiom_inspector(
                stage=stage,
                module_name="RootPropextSpoof",
                decl="__auditSpecCheck",
                inspector_spec=("not_claim", "TrueExpected.claim@TrueExpected"),
            )
            self.assertIsNone(rp_ax)
            self.assertIn("non-foundation axiom", rp_err)

            # Kernel-accelerated primitive spoof (`Nat.gcd`) against a vacuous
            # `TrueExpected.claim := True` compiles with zero axioms in Lean
            # when `Init.Data.Nat.Gcd` is unimported, and MUST be rejected by
            # `AXIOM_INSPECTOR_SRC`.
            write_and_compile(
                "GcdSpoofWitness",
                "module\nprelude\npublic import Init.Core\n"
                "public import TrueExpected\npublic section\n"
                "@[expose] def Nat.gcd (_ _ : Nat) : Nat := 0\n"
                "theorem gcd_two : Nat.gcd 2 2 = 2 := rfl\n"
                "theorem gcd_zero (x y : Nat) : Nat.gcd x y = 0 := rfl\n"
                "theorem __auditSpecCheck : ¬ _root_.TrueExpected.claim := by\n"
                "  intro _\n"
                "  have h : (2 : Nat) = 0 := Eq.trans (Eq.symm gcd_two) (gcd_zero 2 2)\n"
                "  cases h\n"
                "end\n",
            )
            gcd_ax, gcd_err = audit_spec._run_axiom_inspector(
                stage=stage,
                module_name="GcdSpoofWitness",
                decl="__auditSpecCheck",
                inspector_spec=("not_claim", "TrueExpected.claim@TrueExpected"),
            )
            self.assertIsNone(gcd_ax)
            self.assertIn("reserved kernel namespace", gcd_err)

            # Real Lean `compile_classified` distinguishes non-semantic errors
            # (unknown identifiers, unused-variable linter under
            # `-DwarningAsError=true`) from semantic type mismatches.
            for mod, bad_src, expect_infra in (
                (
                    "RealUnknownIdent",
                    "module\nprelude\npublic import Init.Core\npublic section\n"
                    "theorem t : True := noSuchHelper\nend\n",
                    True,
                ),
                (
                    "RealUnusedVar",
                    "module\nprelude\npublic import Init.Core\npublic section\n"
                    "theorem t : Nat → True := fun unusedX => True.intro\nend\n",
                    True,
                ),
                (
                    "RealTypeMismatch",
                    "module\nprelude\npublic import Init.Core\npublic section\n"
                    "theorem t : False := True.intro\nend\n",
                    False,
                ),
            ):
                f_bad = src / f"{mod}.lean"
                f_bad.write_text(bad_src, encoding="utf-8")
                c_err, is_infra = stage.compile_classified(
                    module=mod, src=f_bad, root=src, overwrite=True
                )
                self.assertIsNotNone(c_err, mod)
                self.assertEqual(is_infra, expect_infra, (mod, c_err))

            # `nv_claim` accepts a `Trusted.*`-only claim and rejects a claim
            # definition referencing an untrusted module.
            write_and_compile(
                "Captured",
                "module\nprelude\npublic import Init.Core\n"
                "public section\n@[expose] def Captured.program : Nat := 0\nend\n",
            )
            write_and_compile(
                "Spec",
                "module\nprelude\npublic import Init.Core\n"
                "public section\n@[expose] def Spec.specs : Nat := 0\nend\n",
            )
            write_and_compile(
                "Trusted.Dummy",
                "module\nprelude\npublic import Init.Core\n"
                "public section\n@[expose] def Trusted.Dummy.ok (a b : Nat) : Prop :=\n"
                "  a = b\nend\n",
            )
            write_and_compile(
                "AuditSpecNvOk",
                "module\nprelude\npublic import Captured\npublic import Spec\n"
                "public import Trusted.Dummy\npublic section\n"
                "@[expose] def AuditSpecNvOk.claim : Prop :=\n"
                "  Trusted.Dummy.ok Captured.program Spec.specs\nend\n",
            )
            write_and_compile(
                "NvOkVerify",
                "module\nprelude\npublic import AuditSpecNvOk\npublic section\n"
                "theorem __auditSpecCheck : _root_.AuditSpecNvOk.claim := rfl\nend\n",
            )
            ok_ax, ok_err = audit_spec._run_axiom_inspector(
                stage=stage,
                module_name="NvOkVerify",
                decl="__auditSpecCheck",
                inspector_spec=(
                    "nv_claim",
                    "AuditSpecNvOk.claim@AuditSpecNvOk",
                    "Spec.specs@Spec",
                    "Captured.program@Captured",
                ),
            )
            self.assertEqual(ok_err, "")
            self.assertEqual(ok_ax, ())

            write_and_compile(
                "UntrustedHelper",
                "module\nprelude\npublic import Init.Core\n"
                "public section\n@[expose] def UntrustedHelper.vacuous : Prop := True\nend\n",
            )
            write_and_compile(
                "AuditSpecNvClaim",
                "module\nprelude\npublic import Captured\npublic import Spec\n"
                "public import UntrustedHelper\npublic section\n"
                "@[expose] def AuditSpecNvClaim.claim : Prop :=\n"
                "  Captured.program = Spec.specs ∧ UntrustedHelper.vacuous\nend\n",
            )
            write_and_compile(
                "NvSpoofVerify",
                "module\nprelude\npublic import AuditSpecNvClaim\npublic section\n"
                "theorem __auditSpecCheck : _root_.AuditSpecNvClaim.claim :=\n"
                "  ⟨rfl, True.intro⟩\nend\n",
            )
            nv_ax, nv_err = audit_spec._run_axiom_inspector(
                stage=stage,
                module_name="NvSpoofVerify",
                decl="__auditSpecCheck",
                inspector_spec=(
                    "nv_claim",
                    "AuditSpecNvClaim.claim@AuditSpecNvClaim",
                    "Spec.specs@Spec",
                    "Captured.program@Captured",
                ),
            )
            self.assertIsNone(nv_ax)
            self.assertIn("untrusted", nv_err)


if __name__ == "__main__":
    unittest.main()
