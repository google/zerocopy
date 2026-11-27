# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`Trusted.MirAst` schema tests for loading the live `Trusted.MirAst` sources
and auditing them."""

from __future__ import annotations

from .support import (
    audit_mir_ast_sources,
    MIR_AST_DIR,
    MIR_AST_UMBRELLA,
    strip_lean_comments,
    VARIABLE_DECL_RE,
)


class LiveSourcesCases:
    """`MirAstSchemaTests` methods for loading the live `Trusted.MirAst` sources
    and auditing them."""

    def _load_live_sources(self) -> dict[str, str]:
        self.assertTrue(
            MIR_AST_UMBRELLA.is_file(),
            f"missing umbrella module {MIR_AST_UMBRELLA}",
        )
        files = sorted(MIR_AST_DIR.rglob("*.lean"))
        self.assertTrue(files, f"no Lean files found in {MIR_AST_DIR}")
        sources = {
            "MirAst.lean": MIR_AST_UMBRELLA.read_text(encoding="utf-8")
        }
        for p in files:
            sources[p.relative_to(MIR_AST_DIR).as_posix()] = p.read_text(
                encoding="utf-8"
            )
        return sources

    def test_live_mir_ast_has_zero_unexpected_or_generic_defaults(self) -> None:
        stripped = strip_lean_comments(
            'def quoteChar : Char := \'"\'\n/- secret -/\n'
        )
        self.assertNotIn("secret", stripped)
        self.assertIsNone(VARIABLE_DECL_RE.search("in " * 200 + "xxxxx"))
        errors = audit_mir_ast_sources(self._load_live_sources())
        self.assertEqual(errors, [])
