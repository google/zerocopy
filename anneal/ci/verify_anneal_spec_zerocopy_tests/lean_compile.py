# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`verify_anneal_spec_zerocopy.py` tests for trusted module ordering and the
Lean compile check."""

from .support import (
    json,
    make_fixture,
    make_trusted_tree,
    mock,
    Path,
    SimpleNamespace,
    subprocess,
    tempfile,
    verify_anneal_spec_zerocopy,
)


class LeanCompileCases:
    """`VerifyAnnealSpecZerocopyTests` methods for trusted module ordering and
    the Lean compile check."""

    def test_trusted_module_order_puts_imports_first_and_rejects_cycles(self):
        with tempfile.TemporaryDirectory() as tmp:
            trusted = make_trusted_tree(Path(tmp))
            order = verify_anneal_spec_zerocopy.trusted_module_order(trusted)
            self.assertEqual(
                [m for m, _ in order],
                ["Trusted.MirAst", "Trusted.MirSemantics.Ops", "Trusted.MirSemantics"],
            )
            (trusted / "Trusted/MirAst.lean").write_text(
                "prelude\nimport Trusted.MirSemantics\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(RuntimeError, "import cycle"):
                verify_anneal_spec_zerocopy.trusted_module_order(trusted)
            (trusted / "Trusted/MirAst.lean").write_text(
                "prelude\nimport Trusted.Missing\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(RuntimeError, "missing Trusted module"):
                verify_anneal_spec_zerocopy.trusted_module_order(trusted)

    def test_lean_compile_check_builds_in_order_and_rejects_any_message(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec_root, _, _, _ = make_fixture(root)
            trusted = make_trusted_tree(root)
            args = SimpleNamespace(
                src_root=spec_root,
                trusted_lean=trusted,
                lean=root / "lean",
                lower=root / "lower",
                timeout=30,
            )
            calls = []

            listing = json.dumps([
                {"target": t, "claim": c, "file": "tests/lean_compile/spec.rs",
                 "kind": "external"}
                for t, c in (("a", "c1"), ("b", "c1"), ("m::d", "m__d"))
            ])

            def clean(cmd, **kwargs):
                calls.append((cmd, kwargs.get("env")))
                out = listing if "--list-targets" in cmd else ""
                return subprocess.CompletedProcess(cmd, 0, out, "")

            work = root / "work"
            work.mkdir()
            with mock.patch("verify_anneal_spec_zerocopy.subprocess.run", side_effect=clean):
                result = verify_anneal_spec_zerocopy.run_lean_compile_check(args, work)
            self.assertEqual(
                result, {"status": "compiled", "trusted_modules": 3, "v2_modules": 2}
            )
            lib = work / "lean-compile/lib"
            v2 = work / "lean-compile/v2"
            self.assertEqual(calls[0][0][-1], "tests/lean_compile/spec.rs")
            lean_calls = [cmd for cmd, _ in calls if cmd[0] == str(args.lean)]
            self.assertEqual(
                [cmd[-1] for cmd in lean_calls],
                [
                    str(trusted / "Trusted/MirAst.lean"),
                    str(trusted / "Trusted/MirSemantics/Ops.lean"),
                    str(trusted / "Trusted/MirSemantics.lean"),
                    str(work / "lean-compile/Spec.lean"),
                    str(spec_root / "tests/lean_compile/Check.lean"),
                    str(v2 / "Specs/lean_compile/c1.lean"),
                    str(v2 / "Specs/lean_compile/m__d.lean"),
                ],
            )
            lower_calls = [cmd for cmd, _ in calls if cmd[0] == str(args.lower)]
            self.assertEqual(
                [cmd[cmd.index("--claim") + 1] for cmd in lower_calls if "--claim" in cmd],
                ["c1", "m__d"],
            )
            self.assertEqual(
                lean_calls[-1][1:6],
                [
                    "-DautoImplicit=false",
                    "-DrelaxedAutoImplicit=false",
                    f"--root={v2}",
                    "-o",
                    str(lib / "Specs/lean_compile/m__d.olean"),
                ],
            )
            self.assertEqual(calls[3][0][1:4], [f"--root={trusted}", "-o", str(lib / "Trusted/MirSemantics.olean")])
            self.assertEqual(
                calls[4][0][1:6],
                [
                    "-DautoImplicit=false",
                    "-DrelaxedAutoImplicit=false",
                    f"--root={work / 'lean-compile'}",
                    "-o",
                    str(lib / "Spec.olean"),
                ],
            )
            self.assertTrue(
                all(env["LEAN_PATH"] == str(lib) for cmd, env in calls if cmd[0] == str(args.lean))
            )

            def warns_on_spec(cmd, **_kwargs):
                if cmd[-1].endswith("Spec.lean"):
                    return subprocess.CompletedProcess(cmd, 0, "Spec.lean:1:0: warning: x\n", "")
                return clean(cmd)

            work_bad = root / "work-bad"
            work_bad.mkdir()
            with mock.patch(
                "verify_anneal_spec_zerocopy.subprocess.run", side_effect=warns_on_spec
            ):
                with self.assertRaisesRegex(RuntimeError, "generated Spec.lean failed"):
                    verify_anneal_spec_zerocopy.run_lean_compile_check(args, work_bad)

            # A module that does not compile fails the check too.
            def rejects_module(cmd, **_kwargs):
                if cmd[-1].endswith("m__d.lean"):
                    return subprocess.CompletedProcess(cmd, 1, "", "error: private\n")
                return clean(cmd)

            # An empty fixture listing would silently skip the modules.
            def lists_nothing(cmd, **_kwargs):
                if "--list-targets" in cmd:
                    return subprocess.CompletedProcess(cmd, 0, "[]", "")
                return clean(cmd)

            work_empty = root / "work-empty"
            work_empty.mkdir()
            with mock.patch(
                "verify_anneal_spec_zerocopy.subprocess.run", side_effect=lists_nothing
            ):
                with self.assertRaisesRegex(RuntimeError, "found no items"):
                    verify_anneal_spec_zerocopy.run_lean_compile_check(args, work_empty)

            work_mod = root / "work-mod"
            work_mod.mkdir()
            with mock.patch(
                "verify_anneal_spec_zerocopy.subprocess.run", side_effect=rejects_module
            ):
                with self.assertRaisesRegex(
                    RuntimeError, "generated module Specs/lean_compile/m__d.lean failed"
                ):
                    verify_anneal_spec_zerocopy.run_lean_compile_check(args, work_mod)
