# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`check_minirust_pin.py` tests for the SpecAnchor checks (`--check-
anchors`)."""

from __future__ import annotations

from .support import (
    check_minirust_pin,
    Path,
    populate_valid_repo,
    tempfile,
)


class SpecAnchorCases:
    """`CheckMiniRustPinTests` methods for the SpecAnchor checks (`--check-
    anchors`)."""

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
