# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `check_minirust_pin.py`."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import tomllib
import unittest

import check_minirust_pin


SCRIPT = Path(__file__).resolve().parent / "check_minirust_pin.py"
ANNEAL_ROOT = Path(__file__).resolve().parent.parent


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _minimal_required_proof_lean() -> str:
    lines = [
        "import Trusted.MirSemantics",
        "namespace Anneal.MiniRustProof",
    ]
    for qual in check_minirust_pin.REQUIRED_EXPORTED_THEOREMS:
        short = qual.removeprefix("Anneal.MiniRustProof.")
        lines.append(f"theorem {short} : True := trivial")
    lines.append("end Anneal.MiniRustProof")
    return "\n".join(lines) + "\n"


def _make_tree_writable(root: Path) -> None:
    """Ensure copied fixture files and directories are owner-writable."""
    for dirpath, _, filenames in os.walk(root, topdown=True, followlinks=False):
        dp = Path(dirpath)
        dp.chmod(
            stat.S_IMODE(dp.stat().st_mode)
            | stat.S_IRUSR
            | stat.S_IWUSR
            | stat.S_IXUSR
        )
        for name in filenames:
            fp = dp / name
            if not fp.is_symlink():
                fp.chmod(
                    stat.S_IMODE(fp.stat().st_mode)
                    | stat.S_IRUSR
                    | stat.S_IWUSR
                )


def populate_valid_repo(
    root: Path,
    *,
    source_root: Path | None = None,
    spec_files: dict[str, str] | None = None,
    lean_files: dict[str, str] | None = None,
    proof_lean: str | None = None,
) -> dict[str, str]:
    """Create a valid Anneal fixture with pinned MiniRust files.

    When `spec_files` is `None`, copies the real locked 30-file
    `vendor/minirust/` tree so CLI invocations exercise the locked commit,
    file count, and manifest SHA-256 without any bypass flags.
    """
    vendor_dir = root / "vendor/minirust"
    if spec_files is None:
        src_root = ANNEAL_ROOT if source_root is None else source_root
        shutil.copytree(src_root / "vendor/minirust", vendor_dir)
        _make_tree_writable(vendor_dir)
        pin_data = json.loads(
            (vendor_dir / "UPSTREAM_PIN.json").read_text(encoding="utf-8")
        )
        files_map: dict[str, str] = dict(pin_data["files"])
    else:
        vendor_dir.mkdir(parents=True, exist_ok=True)
        files_map = {}
        for rel, content in sorted(spec_files.items()):
            target = vendor_dir / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            raw = content.encode("utf-8")
            target.write_bytes(raw)
            files_map[rel] = _sha256_bytes(raw)

        manifest_sha = check_minirust_pin._compute_manifest_sha256(files_map)
        pin = {
            "schema_version": 1,
            "upstream_repo": check_minirust_pin.EXPECTED_UPSTREAM_REPO,
            "commit": check_minirust_pin.LOCKED_MINIRUST_COMMIT,
            "tarball_sha256": check_minirust_pin.LOCKED_MINIRUST_TARBALL_SHA256,
            "file_count": len(files_map),
            "manifest_sha256": manifest_sha,
            "files": files_map,
        }
        (vendor_dir / "UPSTREAM_PIN.json").write_text(
            json.dumps(pin, indent=2) + "\n", encoding="utf-8"
        )

    if lean_files is not None or proof_lean is not None:
        minirust_corr = root / "correspondence/Anneal/MiniRust"
        minirust_corr.mkdir(parents=True, exist_ok=True)
        if lean_files is None:
            lean_files = {
                "Syntax.lean": (
                    "import Trusted.MirAst\n"
                    "namespace Anneal.MiniRust\n"
                    "def okDecl : Nat := 1\n"
                    "end Anneal.MiniRust\n"
                ),
            }
        for rel, content in lean_files.items():
            target = minirust_corr / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content, encoding="utf-8")

        if proof_lean is None:
            proof_lean = _minimal_required_proof_lean()
        (root / "correspondence/Anneal/MiniRustProof.lean").write_text(
            proof_lean, encoding="utf-8"
        )

    return files_map


def write_fake_lean(path: Path, body: str) -> Path:
    """Create an executable Python stub acting as `--lean`."""
    path.write_text(f"#!{sys.executable}\n{body}", encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path


class CheckMiniRustPinTests(unittest.TestCase):
    def run_cli(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), *args],
            capture_output=True,
            text=True,
        )

    # ------------------------------------------------------------------
    # Vendor pin tests
    # ------------------------------------------------------------------

    def test_real_vendored_minirust_pin_passes(self) -> None:
        res = self.run_cli(
            "--repo-root",
            str(ANNEAL_ROOT),
            "--check-lean",
            "--check-anchors",
        )
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertIn("vendor-pin: OK (30 files at d821c6e3a3d3)", res.stdout)
        self.assertIn("lean-hygiene: OK (10 modules)", res.stdout)
        self.assertIn("spec-anchors: OK (58 anchors)", res.stdout)

    def test_valid_copied_pin_passes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            res = self.run_cli("--repo-root", str(root))
            self.assertEqual(res.returncode, 0, res.stderr)
            self.assertIn(
                "vendor-pin: OK (30 files at d821c6e3a3d3)", res.stdout
            )

    def test_populate_valid_repo_from_readonly_source_tree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            ro_src = tmp_path / "readonly_anneal"
            shutil.copytree(
                ANNEAL_ROOT / "vendor/minirust", ro_src / "vendor/minirust"
            )
            try:
                for dirpath, _, filenames in os.walk(
                    ro_src, topdown=False, followlinks=False
                ):
                    dp = Path(dirpath)
                    for name in filenames:
                        fp = dp / name
                        if not fp.is_symlink():
                            fp.chmod(0o444)
                    dp.chmod(0o555)

                dst_repo = tmp_path / "dst_anneal"
                populate_valid_repo(dst_repo, source_root=ro_src)
                vendor_dir = dst_repo / "vendor/minirust"
                (vendor_dir / "UPSTREAM_PIN.json").write_text(
                    "{}\n", encoding="utf-8"
                )
                (vendor_dir / "spec/lang/well-formed.md").write_text(
                    "mutated\n", encoding="utf-8"
                )
                (vendor_dir / "spec/lang/extra.md").write_text(
                    "added\n", encoding="utf-8"
                )
            finally:
                if ro_src.exists():
                    _make_tree_writable(ro_src)

    def test_rejects_altered_locked_commit_and_manifest_sha256(self) -> None:
        # 1. Valid 40-hex commit different from LOCKED_MINIRUST_COMMIT fails.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            pin_path = root / "vendor/minirust/UPSTREAM_PIN.json"
            pin = json.loads(pin_path.read_text(encoding="utf-8"))
            pin["commit"] = "a" * 40
            pin_path.write_text(
                json.dumps(pin, indent=2) + "\n", encoding="utf-8"
            )
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("LOCKED_MINIRUST_COMMIT", res.stderr)

        # 2. Lockstep re-pin (file modified + files map + manifest_sha256
        # recomputed consistently) still fails against LOCKED_MINIRUST_MANIFEST.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            readme = root / "vendor/minirust/README.md"
            new_bytes = b"# Replaced upstream spec\n"
            readme.write_bytes(new_bytes)
            pin_path = root / "vendor/minirust/UPSTREAM_PIN.json"
            pin = json.loads(pin_path.read_text(encoding="utf-8"))
            pin["files"]["README.md"] = _sha256_bytes(new_bytes)
            pin["manifest_sha256"] = (
                check_minirust_pin._compute_manifest_sha256(pin["files"])
            )
            pin_path.write_text(
                json.dumps(pin, indent=2) + "\n", encoding="utf-8"
            )
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("LOCKED_MINIRUST_MANIFEST_SHA256", res.stderr)

        # 3. Valid 64-hex tarball_sha256 different from
        # LOCKED_MINIRUST_TARBALL_SHA256 fails, as do malformed digests, bad
        # schema_version, and duplicate JSON keys.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            pin_path = root / "vendor/minirust/UPSTREAM_PIN.json"
            orig_pin = json.loads(pin_path.read_text(encoding="utf-8"))

            for mutate, expected in (
                (
                    lambda p: p.update(tarball_sha256="b" * 64),
                    "LOCKED_MINIRUST_TARBALL_SHA256",
                ),
                (
                    lambda p: p.update(tarball_sha256="not-hex"),
                    "tarball_sha256 must be a 64-char lowercase hex SHA",
                ),
                (lambda p: p.update(schema_version=2), "schema_version"),
                (lambda p: p.update(schema_version=True), "schema_version"),
            ):
                bad = json.loads(json.dumps(orig_pin))
                mutate(bad)
                pin_path.write_text(
                    json.dumps(bad, indent=2) + "\n", encoding="utf-8"
                )
                res = self.run_cli("--repo-root", str(root))
                self.assertNotEqual(res.returncode, 0)
                self.assertIn(expected, res.stderr)

            pin_path.write_text(
                '{"schema_version": 1, "schema_version": 1}\n',
                encoding="utf-8",
            )
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("duplicate JSON key", res.stderr)

    def test_rejects_tampered_sha(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            target = root / "vendor/minirust/spec/lang/machine.md"
            target.write_text(
                target.read_text(encoding="utf-8") + "\ntampered\n",
                encoding="utf-8",
            )
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("SHA-256 mismatch", res.stderr)

    def test_rejects_extra_unpinned_file_and_stray_dir(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            (root / "vendor/minirust/EXTRA.txt").write_text(
                "stray\n", encoding="utf-8"
            )
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("extra unpinned file", res.stderr)

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            (root / "vendor/minirust/tooling").mkdir()
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("unpinned directory", res.stderr)

    def test_rejects_missing_pinned_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            (root / "vendor/minirust/spec/mem/basic.md").unlink()
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("missing pinned file", res.stderr)

    def test_rejects_forbidden_vendor_names_pinned_or_on_disk(self) -> None:
        forbidden_paths = (
            "Cargo.toml",
            "spec/Cargo.lock",
            "rust-toolchain.toml",
            "rust-toolchain",
            ".cargo/config.toml",
            "lean-toolchain",
            "lakefile",
            "lakefile.lean",
            "lakefile.toml",
            ".gitattributes",
            "build.rs",
            ".envrc",
        )
        for forbidden in forbidden_paths:
            with (
                self.subTest(pinned=forbidden),
                tempfile.TemporaryDirectory() as tmp,
            ):
                root = Path(tmp) / "anneal"
                populate_valid_repo(
                    root,
                    spec_files={
                        "README.md": "ok\n",
                        forbidden: "forbidden\n",
                    },
                )
                res = self.run_cli("--repo-root", str(root))
                self.assertNotEqual(res.returncode, 0)
                self.assertIn("forbidden ambient/build/toolchain", res.stderr)

            with (
                self.subTest(on_disk=forbidden),
                tempfile.TemporaryDirectory() as tmp,
            ):
                root = Path(tmp) / "anneal"
                populate_valid_repo(root)
                target = root / "vendor/minirust" / forbidden
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text("forbidden\n", encoding="utf-8")
                res = self.run_cli("--repo-root", str(root))
                self.assertNotEqual(res.returncode, 0)
                self.assertIn("forbidden ambient/build/toolchain", res.stderr)

    def test_rejects_symlinks_in_vendor_tree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            (root / "vendor/minirust/link.md").symlink_to("README.md")
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("symlink forbidden", res.stderr)

        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            real_root = tmp_path / "real"
            populate_valid_repo(real_root)
            fake_root = tmp_path / "fake"
            (fake_root / "vendor").mkdir(parents=True)
            (fake_root / "vendor/minirust").symlink_to(
                real_root / "vendor/minirust"
            )
            res = self.run_cli("--repo-root", str(fake_root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("expected regular directory", res.stderr)

    def test_rejects_unreadable_dir_and_bad_manifest_digest(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(root)
            pin_path = root / "vendor/minirust/UPSTREAM_PIN.json"
            pin = json.loads(pin_path.read_text(encoding="utf-8"))
            pin["manifest_sha256"] = "0" * 64
            pin_path.write_text(
                json.dumps(pin, indent=2) + "\n", encoding="utf-8"
            )
            res = self.run_cli("--repo-root", str(root))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("manifest_sha256 mismatch", res.stderr)

        if os.geteuid() != 0:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp) / "anneal"
                populate_valid_repo(root)
                hidden = root / "vendor/minirust/spec/hidden"
                hidden.mkdir()
                (hidden / "escape.md").symlink_to("/etc/passwd")
                hidden.chmod(0o000)
                try:
                    res = self.run_cli("--repo-root", str(root))
                    self.assertNotEqual(res.returncode, 0)
                    self.assertIn("cannot traverse", res.stderr)
                finally:
                    hidden.chmod(0o755)

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

    # ------------------------------------------------------------------
    # SpecAnchor verification tests (`--check-anchors`)
    # ------------------------------------------------------------------

    def test_valid_spec_anchors_resolve_lean_symbols_and_excerpts(self) -> None:
        syntax_src = (
            "namespace Anneal.MiniRust\n"
            "structure Machine where\n"
            "  prog : Nat\n"
            "def MrMemory.allocate : Nat := 0\n"
            "end Anneal.MiniRust\n"
        )
        anchors_src = r'''
namespace Anneal.MiniRust

/-!
Example in docstring that must be ignored:
⟨"fake-doc", "Anneal.MiniRust.Missing", "spec/nonexistent.md", "missing"⟩
-/

structure SpecAnchor where
  id : String
  leanSymbol : String
  specFile : String
  excerpt : String

def specAnchors : List SpecAnchor := [
  {
    id := "machine-struct",
    leanSymbol := "Anneal.MiniRust.Machine",
    specFile := "spec/lang/machine.md",
    excerpt := r#"pub struct Machine<M: Memory> {"#
  },
  {
    id := "mem-alloc-size",
    leanSymbol := "Anneal.MiniRust.MrMemory.allocate",
    specFile := "spec/mem/basic.md",
    excerpt := "throw_ub!(\"" ++ "asking for a too large allocation\");"
  }
]

end Anneal.MiniRust
'''
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            populate_valid_repo(
                root,
                lean_files={
                    "Syntax.lean": syntax_src,
                    "Anchors.lean": anchors_src,
                },
            )
            pin = check_minirust_pin.verify_vendor_pin(root)
            anchors = check_minirust_pin.verify_spec_anchors(
                root, pin, expected_count=2
            )
            self.assertEqual(len(anchors), 2)

            # CLI enforces the locked 58-anchor count on `specAnchors`.
            res_count = self.run_cli(
                "--repo-root", str(root), "--check-anchors"
            )
            self.assertNotEqual(res_count.returncode, 0)
            self.assertIn("expected locked count 58", res_count.stderr)

    def test_rejects_angle_where_mk_unresolved_and_tampered_anchors(
        self,
    ) -> None:
        syntax_src = (
            "namespace Anneal.MiniRust\n"
            "structure Machine where\n"
            "  prog : Nat\n"
            "end Anneal.MiniRust\n"
        )
        cases = [
            (
                "angle-bracket-form",
                (
                    "structure SpecAnchor where\n"
                    "  id : String\n"
                    "  leanSymbol : String\n"
                    "  specFile : String\n"
                    "  excerpt : String\n"
                    "def specAnchors : List SpecAnchor := [\n"
                    '  ⟨"a", "Anneal.MiniRust.Machine", '
                    '"spec/lang/machine.md", "NOT IN SPEC"⟩\n'
                    "]\n"
                ),
                "anonymous constructor",
            ),
            (
                "where-clause-form",
                (
                    "structure SpecAnchor where\n"
                    "  id : String\n"
                    "  leanSymbol : String\n"
                    "  specFile : String\n"
                    "  excerpt : String\n"
                    "def hidden : SpecAnchor where\n"
                    '  id := "a"\n'
                    '  leanSymbol := "Anneal.MiniRust.Machine"\n'
                    '  specFile := "spec/lang/machine.md"\n'
                    '  excerpt := "NOT IN SPEC"\n'
                    "def specAnchors : List SpecAnchor := [hidden]\n"
                ),
                "`where` constructor form is forbidden",
            ),
            (
                "mk-constructor-form",
                (
                    "structure SpecAnchor where\n"
                    "  id : String\n"
                    "  leanSymbol : String\n"
                    "  specFile : String\n"
                    "  excerpt : String\n"
                    "def specAnchors : List SpecAnchor := [\n"
                    '  SpecAnchor.mk "a" "Anneal.MiniRust.Machine" '
                    '"spec/lang/machine.md" "pub struct Machine"\n'
                    "]\n"
                ),
                "`SpecAnchor.mk` constructor form is forbidden",
            ),
            (
                "missing-leanSymbol-field",
                (
                    "def specAnchors := [\n"
                    '  { id := "a", specFile := "spec/lang/machine.md", '
                    'excerpt := "pub struct Machine" }\n'
                    "]\n"
                ),
                "missing required field(s): leanSymbol",
            ),
            (
                "unresolved-leanSymbol",
                (
                    "def specAnchors := [\n"
                    '  { id := "a", leanSymbol := "Anneal.MiniRust.NoSuchDef", '
                    'specFile := "spec/lang/machine.md", '
                    'excerpt := "pub struct Machine" }\n'
                    "]\n"
                ),
                "does not resolve to a declared symbol",
            ),
            (
                "tampered-excerpt",
                (
                    "def specAnchors := [\n"
                    '  { id := "a", leanSymbol := "Anneal.MiniRust.Machine", '
                    'specFile := "spec/lang/machine.md", '
                    'excerpt := "NOT IN SPEC FILE" }\n'
                    "]\n"
                ),
                "not found verbatim",
            ),
            (
                "unpinned-spec-file",
                (
                    "def specAnchors := [\n"
                    '  { id := "a", leanSymbol := "Anneal.MiniRust.Machine", '
                    'specFile := "spec/lang/missing.md", '
                    'excerpt := "pub struct Machine" }\n'
                    "]\n"
                ),
                "is not in vendor/minirust/UPSTREAM_PIN.json",
            ),
            (
                "duplicate-id",
                (
                    "def specAnchors := [\n"
                    '  { id := "dup", leanSymbol := "Anneal.MiniRust.Machine", '
                    'specFile := "spec/lang/machine.md", '
                    'excerpt := "pub struct Machine" },\n'
                    '  { id := "dup", leanSymbol := "Anneal.MiniRust.Machine", '
                    'specFile := "spec/mem/basic.md", '
                    'excerpt := "struct Allocation" }\n'
                    "]\n"
                ),
                "duplicate SpecAnchor id",
            ),
            (
                "non-literal-excerpt",
                (
                    'def hidden : String := "pub struct Machine"\n'
                    "def specAnchors := [\n"
                    '  { id := "a", leanSymbol := "Anneal.MiniRust.Machine", '
                    'specFile := "spec/lang/machine.md", excerpt := hidden }\n'
                    "]\n"
                ),
                "must be a string literal",
            ),
            (
                "empty-anchors",
                "def specAnchors : List SpecAnchor := []\n",
                "no SpecAnchor records found",
            ),
        ]
        for label, anchors_src, expected_err in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp) / "anneal"
                populate_valid_repo(
                    root,
                    lean_files={
                        "Syntax.lean": syntax_src,
                        "Anchors.lean": anchors_src,
                    },
                )
                pin = check_minirust_pin.verify_vendor_pin(root)
                with self.assertRaises(check_minirust_pin.VerificationError) as ctx:
                    check_minirust_pin.verify_spec_anchors(
                        root, pin, expected_count=None
                    )
                self.assertIn(expected_err, str(ctx.exception), label)

    # ------------------------------------------------------------------
    # Constructive axiom check tests (`--check-axioms`)
    # ------------------------------------------------------------------

    def test_extract_exported_theorems_scopes_and_visibility(self) -> None:
        src = (
            "namespace Anneal.MiniRustProof\n"
            "structure S where\n"
            "  private field : Nat\n"
            "theorem thm_top : True := trivial\n"
            "private theorem thm_priv : True := trivial\n"
            "private @[simp] theorem thm_priv_attr : True := trivial\n"
            "@[simp] theorem thm_attr : True := trivial\n"
            "mutual\n"
            "theorem thm_mut : True := trivial\n"
            "end\n"
            "section Inner\n"
            "theorem thm_sec : True := trivial\n"
            "end Inner\n"
            "namespace Sub\n"
            "theorem thm_sub : True := trivial\n"
            "end Sub\n"
            "export Anneal.MiniRust.OracleCert (reexported_thm)\n"
            "end Anneal.MiniRustProof\n"
        )
        got = check_minirust_pin.extract_exported_theorems(src)
        self.assertEqual(
            got,
            [
                "Anneal.MiniRustProof.thm_top",
                "Anneal.MiniRustProof.thm_attr",
                "Anneal.MiniRustProof.thm_mut",
                "Anneal.MiniRustProof.thm_sec",
                "Anneal.MiniRustProof.Sub.thm_sub",
            ],
        )
        self.assertIn(
            "Anneal.MiniRustProof.reexported_thm",
            check_minirust_pin.extract_declared_symbols(src),
        )

    def test_resolve_lean_command_uses_direct_binary_without_wrappers(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fake = write_fake_lean(Path(tmp) / "lean", "import sys; sys.exit(0)\n")
            self.assertEqual(
                check_minirust_pin._resolve_lean_command(fake), [str(fake)]
            )
            self.assertEqual(
                check_minirust_pin._resolve_lean_command(
                    "lean", path_env=str(tmp)
                ),
                [str(fake)],
            )
            with self.assertRaises(check_minirust_pin.VerificationError):
                check_minirust_pin._resolve_lean_command("lean", path_env="")

    def test_check_axioms_accepts_constructive_and_rejects_classical_or_sorry(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            root = tmp_path / "anneal"
            stage = tmp_path / "stage"
            stage.mkdir()
            populate_valid_repo(
                root,
                lean_files={"Syntax.lean": "def x := 1\n"},
                proof_lean=(
                    "namespace Anneal.MiniRustProof\n"
                    "theorem minirust_forward_sim_holds : True := trivial\n"
                    "theorem minirust_bi_fault_equiv_holds : 1 = 1 := rfl\n"
                    "end Anneal.MiniRustProof\n"
                ),
            )

            ok_lean = write_fake_lean(
                tmp_path / "lean_ok.py",
                """
import os, pathlib, sys
assert str(pathlib.Path(sys.argv[-1])).endswith("CheckMiniRustAxioms.lean")
assert os.environ.get("LEAN_PATH", ""), "LEAN_PATH must include stage-dir"
for secret_var in (
    "ACTIONS_CACHE_URL",
    "ACTIONS_RESULTS_URL",
    "ACTIONS_RUNTIME_TOKEN",
    "GITHUB_TOKEN",
    "GH_TOKEN",
):
    assert secret_var not in os.environ, f"leaked {secret_var}"
probe = pathlib.Path(sys.argv[-1]).read_text(encoding="utf-8")
assert "import Anneal.MiniRustProof" in probe
print("'Anneal.MiniRustProof.minirust_forward_sim_holds' depends on axioms: [propext,")
print(" Quot.sound]")
print("'Anneal.MiniRustProof.minirust_bi_fault_equiv_holds' does not depend on any axioms")
""",
            )
            env_with_secrets = os.environ.copy()
            env_with_secrets.update(
                {
                    "ACTIONS_CACHE_URL": "https://cache.example.invalid",
                    "ACTIONS_RESULTS_URL": "https://results.example.invalid",
                    "ACTIONS_RUNTIME_TOKEN": "mock-runtime-token",
                    "GITHUB_TOKEN": "mock-github-token",
                    "GH_TOKEN": "mock-gh-token",
                }
            )
            res_ok = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--repo-root",
                    str(root),
                    "--check-axioms",
                    "--lean",
                    str(ok_lean),
                    "--stage-dir",
                    str(stage),
                ],
                capture_output=True,
                text=True,
                env=env_with_secrets,
            )
            self.assertEqual(res_ok.returncode, 0, res_ok.stderr)
            self.assertIn("axioms: OK (2 exported theorems", res_ok.stdout)

            for bad_axiom in (
                "Classical.choice",
                "sorryAx",
                "Lean.ofReduceBool",
            ):
                with self.subTest(bad_axiom=bad_axiom):
                    bad_lean = write_fake_lean(
                        tmp_path / f"lean_bad_{bad_axiom}.py",
                        f"""
print("'Anneal.MiniRustProof.minirust_forward_sim_holds' depends on axioms: [propext, {bad_axiom}]")
print("'Anneal.MiniRustProof.minirust_bi_fault_equiv_holds' does not depend on any axioms")
""",
                    )
                    res_bad = self.run_cli(
                        "--repo-root",
                        str(root),
                        "--check-axioms",
                        "--lean",
                        str(bad_lean),
                        "--stage-dir",
                        str(stage),
                    )
                    self.assertNotEqual(res_bad.returncode, 0)
                    self.assertIn(bad_axiom, res_bad.stderr)

            missing_lean = write_fake_lean(
                tmp_path / "lean_missing.py",
                """
print("'Anneal.MiniRustProof.minirust_forward_sim_holds' does not depend on any axioms")
""",
            )
            res_missing = self.run_cli(
                "--repo-root",
                str(root),
                "--check-axioms",
                "--lean",
                str(missing_lean),
            )
            self.assertNotEqual(res_missing.returncode, 0)
            self.assertIn(
                "missing from `#print axioms` output", res_missing.stderr
            )

            # Bare `--lean` / `ANNEAL_LEAN` command names resolve via `PATH`
            # (not CWD) and fail closed when absent from `PATH`.
            bin_dir = tmp_path / "custom_bin"
            bin_dir.mkdir()
            write_fake_lean(
                bin_dir / "custom-lean-stub",
                """
p = "Anneal.MiniRustProof"
print(f"'{p}.minirust_forward_sim_holds' depends on axioms: [propext]")
print(f"'{p}.minirust_bi_fault_equiv_holds' does not depend on any axioms")
""",
            )
            path_env = {
                **os.environ,
                "PATH": f"{bin_dir}{os.pathsep}{os.environ.get('PATH', '')}",
            }
            res_bare_flag = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--repo-root",
                    str(root),
                    "--check-axioms",
                    "--lean",
                    "custom-lean-stub",
                ],
                capture_output=True,
                text=True,
                env=path_env,
            )
            self.assertEqual(
                res_bare_flag.returncode, 0, res_bare_flag.stderr
            )
            res_bare_env = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--repo-root",
                    str(root),
                    "--check-axioms",
                ],
                capture_output=True,
                text=True,
                env={**path_env, "ANNEAL_LEAN": "custom-lean-stub"},
            )
            self.assertEqual(res_bare_env.returncode, 0, res_bare_env.stderr)
            res_bare_missing = self.run_cli(
                "--repo-root",
                str(root),
                "--check-axioms",
                "--lean",
                "nonexistent-lean-binary-xyz",
            )
            self.assertNotEqual(res_bare_missing.returncode, 0)

    def test_ci_core_checks_toml_and_codeowners_cover_minirust_pin(self) -> None:
        ws_root = ANNEAL_ROOT.parent
        checks_path = ws_root / "ci" / "checks.toml"
        codeowners_path = ws_root / ".github" / "CODEOWNERS"
        with checks_path.open("rb") as fh:
            checks_cfg = tomllib.load(fh)
        checks_by_id = {
            chk["id"]: chk
            for chk in checks_cfg.get("checks", [])
            if "id" in chk
        }
        self.assertIn("anneal-ci-tests", checks_by_id)
        ci_tests_includes = {
            pat
            for inp in checks_by_id["anneal-ci-tests"].get("inputs", [])
            if inp.get("kind") == "glob" and not inp.get("exclude")
            for pat in inp.get("include", [])
        }
        self.assertIn("anneal/vendor/minirust/**", ci_tests_includes)

        for check_id in (
            "anneal-flake-eval",
            "anneal-clippy",
            "anneal-sandbox-aarch64",
            "anneal-installed-smoke",
        ):
            with self.subTest(check_id=check_id):
                self.assertIn(check_id, checks_by_id)
                pin_includes = {
                    pat
                    for inp in checks_by_id[check_id].get("inputs", [])
                    if inp.get("kind") == "glob" and not inp.get("exclude")
                    for pat in inp.get("include", [])
                }
                self.assertIn(
                    "anneal/vendor/minirust/UPSTREAM_PIN.json", pin_includes
                )

        codeowners_lines = [
            ln.strip()
            for ln in codeowners_path.read_text(encoding="utf-8").splitlines()
            if ln.strip() and not ln.lstrip().startswith("#")
        ]
        for expected_rule in (
            "/anneal/correspondence/Anneal/MiniRust/ @joshlf @jswrenn @mdittmer",
            "/anneal/correspondence/Anneal/MiniRustProof.lean @joshlf @jswrenn @mdittmer",
            "/anneal/vendor/minirust/UPSTREAM_PIN.json @joshlf @jswrenn @mdittmer",
        ):
            self.assertIn(expected_rule, codeowners_lines)

    def test_tier0_ci_script_invokes_check_minirust_pin_on_checkout(
        self,
    ) -> None:
        script_text = (ANNEAL_ROOT / "ci" / "run_anneal_check.sh").read_text(
            encoding="utf-8"
        )
        ci_tests_match = re.search(
            r"^\s*ci-tests\)\n(.*?)^\s*;;\n",
            script_text,
            re.M | re.S,
        )
        self.assertIsNotNone(ci_tests_match)
        ci_tests_body = " ".join(
            ln.rstrip("\\").strip()
            for ln in ci_tests_match.group(1).splitlines()
        )
        self.assertIn(
            "./ci/check_minirust_pin.py "
            "--repo-root . --check-lean --check-anchors",
            ci_tests_body,
        )


if __name__ == "__main__":
    unittest.main()
