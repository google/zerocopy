# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`check_minirust_pin.py` tests for the Lean hygiene checks (`--check-
lean`)."""

from __future__ import annotations

from .support import (
    Path,
    populate_valid_repo,
    tempfile,
)


class LeanHygieneCases:
    """`CheckMiniRustPinTests` methods for the Lean hygiene checks (`--check-
    lean`)."""

    # ------------------------------------------------------------------
    # Lean hygiene tests (`--check-lean`)
    # ------------------------------------------------------------------

    def test_lean_hygiene_passes_with_docstring_and_string_mentions(
        self,
    ) -> None:
        clean_lean = r'''
import Init.Data.Nat.Basic
import Trusted.MirAst
import Trusted.MirSemantics

/-!
# Clean module mentioning forbidden words only in comments & strings

This docstring explicitly discusses zero `sorry`, zero `admit`, zero
`native_decide`, zero `unsafe`, zero `partial`, zero `axiom`, and zero
`import Miri`, `import Trusted.Correspondence`, or `import Anneal.MirWp`.
/- Nested block comment mentioning `sorry` and `axiom` -/
Still inside outer block comment: `admit`, `unsafe`, `partial`.
-/

-- Line comment: import Miri; axiom bad : False; sorry

namespace Anneal.MiniRust

/-- Docstring mentioning `sorry` and `axiom` and `native_decide`. -/
def note1 : String := "no sorry, no axiom, no unsafe, no import Miri"
def note2 : String := r#"raw string with sorry, admit, partial, axiom"#
def note3 : String := s!"interpolated string mentioning sorry and {1 + 2}"
def note4 : String := s! "spaced interpolated string with sorry and {3 + 4}"
def primeIdent (x' : Nat) (s'' : Nat) : Nat := x' + s''
def charLit : Char := 'a'
def escChar : Char := '\''
def no_sorry_in_name : Bool := true

end Anneal.MiniRust
'''
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root, lean_files={"Clean.lean": clean_lean})
            res = self.run_cli("--repo-root", str(root), "--check-lean")
            self.assertEqual(res.returncode, 0, res.stderr)
            self.assertIn("lean-hygiene: OK (2 modules)", res.stdout)

    def test_lean_hygiene_rejects_forbidden_imports(self) -> None:
        bad_imports = [
            "import Miri",
            "import Miri.Memory.Access",
            "import Trusted.Correspondence",
            "import Trusted.Correspondence.Claim",
            "public meta import all Miri.Interpreter.Step",
            "import «Miri».ABI.Size",
            "import Anneal.MirCorrespondenceProof",
            "import Anneal.MirCorrespondence.Codec",
            "import Anneal.MirWp",
            "import Anneal.MirWp.Tactics",
        ]
        for imp in bad_imports:
            with self.subTest(imp=imp), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp) / "anneal"
                populate_valid_repo(
                    root,
                    lean_files={
                        "BadImport.lean": f"{imp}\ndef x : Nat := 0\n"
                    },
                )
                res = self.run_cli("--repo-root", str(root), "--check-lean")
                self.assertNotEqual(res.returncode, 0, imp)
                self.assertIn("forbidden import", res.stderr)

    def test_lean_hygiene_rejects_missing_required_exported_theorems(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(
                root,
                lean_files={"Syntax.lean": "def x := 1\n"},
                proof_lean=(
                    "namespace Anneal.MiniRustProof\n"
                    "theorem minirust_forward_sim_holds : True := trivial\n"
                    "end Anneal.MiniRustProof\n"
                ),
            )
            res = self.run_cli("--repo-root", str(root), "--check-lean")
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("missing required exported theorem", res.stderr)

            # Re-exporting via `export ... (...)` must not satisfy the required
            # real `theorem` declaration check in `MiniRustProof.lean`.
            (root / "correspondence/Anneal/MiniRustProof.lean").write_text(
                "namespace Anneal.MiniRustProof\n"
                "export Anneal.MiniRust.OracleCert (\n"
                "  minirust_forward_sim_holds\n"
                "  minirust_bi_fault_equiv_holds\n"
                ")\n"
                "end Anneal.MiniRustProof\n",
                encoding="utf-8",
            )
            res_export = self.run_cli("--repo-root", str(root), "--check-lean")
            self.assertNotEqual(res_export.returncode, 0)
            self.assertIn(
                "missing required exported theorem", res_export.stderr
            )

    def test_lean_hygiene_rejects_over_3500_loc(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(
                root,
                lean_files={"Limit.lean": "-- line\n" * 3500},
            )
            ok = self.run_cli("--repo-root", str(root), "--check-lean")
            self.assertEqual(ok.returncode, 0, ok.stderr)

            (root / "correspondence/Anneal/MiniRust/Limit.lean").write_text(
                "-- line\n" * 3501, encoding="utf-8"
            )
            bad = self.run_cli("--repo-root", str(root), "--check-lean")
            self.assertNotEqual(bad.returncode, 0)
            self.assertIn("exceeds line limit (3501 > 3500)", bad.stderr)

    def test_lean_hygiene_rejects_real_forbidden_tokens(self) -> None:
        cases = [
            ("sorry", "theorem t : False := by sorry\n"),
            ("sorryAx", "theorem t : False := sorryAx False false\n"),
            ("admit", "theorem t : False := by admit\n"),
            ("native_decide", "theorem t : 1 = 1 := by native_decide\n"),
            ("unsafe", "unsafe def f : Nat := 0\n"),
            ("partial", "partial def f (n : Nat) : Nat := f n\n"),
            ("axiom", "axiom bad : False\n"),
            ("escaped-sorry", "def x := «sorry»\n"),
            ("interpolated-sorry", 'def x : String := s!"val={sorry}"\n'),
            (
                "spaced-s-interp-sorry",
                'def x : String := s! "{sorry}"\n',
            ),
            (
                "spaced-m-interp-sorry",
                'def x : String := m!  "v={(sorry : Nat)}"\n',
            ),
            (
                "tab-f-interp-sorry",
                'def x : String := f!\t"{sorry}"\n',
            ),
            (
                "raw-interp-sorry",
                'def x : String := s! r#"raw {sorry}"#\n',
            ),
            (
                "newline-s-interp-sorry",
                'def x : String := s!\n  "{(sorry : Nat)}"\n',
            ),
            (
                "crlf-m-interp-sorry",
                'def x : String := m!\r\n  "{(sorry : Nat)}"\n',
            ),
            (
                "block-comment-interp-sorry",
                'def x : String := s! /- c -/ "{(sorry : Nat)}"\n',
            ),
            (
                "nested-and-line-comment-raw-interp-sorry",
                'def x : String := f! /- a /- b -/ -/ -- c\n'
                '  r#"{(sorry : Nat)}"#\n',
            ),
        ]
        for label, src in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp) / "anneal"
                populate_valid_repo(root, lean_files={"Bad.lean": src})
                res = self.run_cli("--repo-root", str(root), "--check-lean")
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("forbidden Lean token", res.stderr)

    def test_lean_hygiene_rejects_symlinks_and_compiled_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root, lean_files={"Syntax.lean": "def x := 1\n"})
            (root / "correspondence/Anneal/MiniRust/Link.lean").symlink_to(
                "Syntax.lean"
            )
            res = self.run_cli("--repo-root", str(root), "--check-lean")
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("symlink forbidden", res.stderr)

        for artifact in (
            "correspondence/Anneal/MiniRust/Syntax.olean",
            "correspondence/Anneal/MiniRust/Syntax.ilean",
            "correspondence/Anneal/MiniRustProof.olean",
            "correspondence/Anneal/MiniRustProof.ilean",
        ):
            with (
                self.subTest(artifact=artifact),
                tempfile.TemporaryDirectory() as tmp,
            ):
                root = Path(tmp) / "anneal"
                populate_valid_repo(
                    root, lean_files={"Syntax.lean": "def x := 1\n"}
                )
                (root / artifact).write_bytes(b"fake-artifact")
                res = self.run_cli("--repo-root", str(root), "--check-lean")
                self.assertNotEqual(res.returncode, 0)
                self.assertIn("compiled artifact forbidden", res.stderr)
