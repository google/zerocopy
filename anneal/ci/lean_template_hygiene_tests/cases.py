# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""The `LeanTemplateHygieneTests` cases, as a mixin."""

import tomllib

from .lean_scanner import scan_lean_directories, scan_lean_source
from .python_scanner import scan_python_scaffold_source
from .rust_scanner import scan_rust_template_source
from .support import (
    CHECKS_TOML,
    LEAN_SCAN_DIRS,
    PYTHON_SCAFFOLD_TEMPLATE,
    REPO_ROOT,
    RUST_INIT_ASSETS_DIR,
    RUST_INIT_TEMPLATE,
)

class LeanTemplateHygieneCases:
    def test_repo_lean_directories_have_no_sorry_or_admit(self):
        for root in LEAN_SCAN_DIRS:
            self.assertTrue(root.is_dir(), f"Expected Lean directory to exist: {root}")
        file_count, findings = scan_lean_directories(LEAN_SCAN_DIRS)
        self.assertGreater(file_count, 0, "Expected at least one .lean file to scan")
        self.assertEqual(
            findings,
            [],
            "Forbidden sorry/admit tokens found in Lean sources:\n"
            + "\n".join(f"  {f.path}:{f.line}: {f.token}: {f.snippet}" for f in findings),
        )

    def test_repo_scaffold_templates_have_no_sorry_or_admit(self):
        self.assertTrue(
            RUST_INIT_TEMPLATE.is_file(),
            f"Expected Rust init template source: {RUST_INIT_TEMPLATE}",
        )
        lean_templates, findings = scan_rust_template_source(
            RUST_INIT_TEMPLATE.read_text(encoding="utf-8"),
            str(RUST_INIT_TEMPLATE.relative_to(REPO_ROOT)),
        )
        asset_lean_count = 0
        if RUST_INIT_ASSETS_DIR.is_dir():
            asset_lean_count, asset_findings = scan_lean_directories(
                (RUST_INIT_ASSETS_DIR,)
            )
            findings.extend(asset_findings)

        self.assertGreaterEqual(
            lean_templates + asset_lean_count,
            4,
            "Expected at least 4 Lean templates across init.rs and "
            "cargo-anneal/assets/**/*.lean",
        )
        self.assertEqual(
            findings,
            [],
            "Forbidden sorry/admit/sorryAx tokens found in scaffold templates:\n"
            + "\n".join(f"  {f.path}:{f.line}: {f.token}: {f.snippet}" for f in findings),
        )

        if PYTHON_SCAFFOLD_TEMPLATE.is_file():
            py_findings = scan_python_scaffold_source(
                PYTHON_SCAFFOLD_TEMPLATE.read_text(encoding="utf-8"),
                str(PYTHON_SCAFFOLD_TEMPLATE.relative_to(REPO_ROOT)),
            )
            self.assertEqual(
                py_findings,
                [],
                "Forbidden sorry/admit tokens found in anneal_scaffold.py:\n"
                + "\n".join(
                    f"  {f.path}:{f.line}: {f.token}: {f.snippet}" for f in py_findings
                ),
            )

    def test_synthetic_sorry_and_admit_detected_in_lean(self):
        src = (
            "module\n"
            "theorem t1 : False := by\n"
            "  sorry\n"
            "theorem t2 : False := by\n"
            "  admit\n"
        )
        findings = scan_lean_source(src, "synthetic.lean")
        self.assertEqual([(f.line, f.token) for f in findings], [(3, "sorry"), (5, "admit")])

    def test_lean_comments_nested_blocks_strings_and_identifiers_ignored(self):
        src = (
            "-- line comment mentioning sorry and admit\n"
            "/- block comment with sorry\n"
            "   /- nested block with admit -/\n"
            "   still inside outer block: sorry\n"
            "-/\n"
            "/-- doc comment: zero `sorry`, admits inputs -/\n"
            'def msg : String := "sorry admit"\n'
            "def BodyStaticAdmitted : Bool := true\n"
            "def sorry_free : Bool := true\n"
            "/- closed block -/ theorem caught : False := by sorry\n"
        )
        findings = scan_lean_source(src, "comments.lean")
        self.assertEqual([(f.line, f.token) for f in findings], [(10, "sorry")])

    def test_rust_template_detects_sorry_and_admit_and_ignores_comments(self):
        rust_src = (
            "// Rust comment: never emit sorry or admit\n"
            "/* block comment /* nested sorry */ admit */\n"
            'const CLEAN: &str = "\\\n'
            "-- Lean comment mentioning sorry and admit\n"
            'public theorem verify : True := True.intro\n";\n'
            'const BAD_NORMAL: &str = "\\\n'
            'public theorem bad1 : False := by\\n  sorry\\n";\n'
            'const BAD_RAW: &str = r#"\n'
            "public theorem bad2 : False := by\n"
            "  admit\n"
            '"#;\n'
            "#[cfg(test)]\n"
            "mod tests {\n"
            '    const TEST_ONLY: &str = "theorem ignored : False := sorry";\n'
            "}\n"
        )
        _, findings = scan_rust_template_source(rust_src, "synthetic_init.rs")
        self.assertEqual([f.token for f in findings], ["sorry", "admit"])

    def test_lean_char_raw_string_interpolation_and_sorry_ax(self):
        src = (
            'def q : Char := \'"\'\n'
            "theorem after_char : False := by sorry\n"
            'def esc : Char := \'\\\'\'\n'
            'def raw_backslash : String := r"\\"\n'
            "theorem after_raw : False := by admit\n"
            'def raw_hash : String := r#"still " raw "#\n'
            'def interp_s : String := s!"val={sorry}"\n'
            'def interp_m : String := m!"ok {if true then admit else 0} lit sorry"\n'
            "def direct_ax : False := sorryAx False false\n"
        )
        findings = scan_lean_source(src, "lexer_edges.lean")
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [
                (2, "sorry"),
                (5, "admit"),
                (7, "sorry"),
                (8, "admit"),
                (9, "sorryAx"),
            ],
        )

    def test_lean_prefix_negation_before_string_with_brace_not_interp(self):
        src = (
            'def x : Bool := !"{".isEmpty\n'
            "theorem bad : False := by sorry\n"
            'def y : Bool := (!"{".isEmpty)\n'
            "theorem bad2 : False := by admit\n"
        )
        findings = scan_lean_source(src, "neg_string.lean")
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [(2, "sorry"), (4, "admit")],
        )

    def test_lean_french_quoted_identifiers_do_not_swallow_following_sorry(self):
        src = (
            "def «/-» : Nat := 0\n"
            "theorem after_french_comment_open : False := by sorry\n"
            'def «"» : Nat := 0\n'
            "theorem after_french_quote : False := by admit\n"
            "def unclosed «\"/- \n"
            "theorem after_unclosed_french : False := sorryAx False false\n"
        )
        findings = scan_lean_source(src, "french_ident.lean")
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [(2, "sorry"), (4, "admit"), (6, "sorryAx")],
        )

    def test_rust_template_after_earlier_cfg_test_block_is_still_scanned(self):
        rust_src = (
            "#[cfg(test)]\n"
            "mod early_tests {\n"
            '    const TEST_ONLY: &str = "theorem ignored : False := by sorry";\n'
            "}\n"
            'const PROD_AFTER_TEST: &str = "\\\n'
            'public theorem verify : False := by\\n  sorry\\n";\n'
        )
        lean_count, findings = scan_rust_template_source(
            rust_src, "early_cfg_test.rs"
        )
        self.assertEqual(lean_count, 1)
        self.assertEqual([(f.line, f.token) for f in findings], [(6, "sorry")])

    def test_rust_cfg_test_fields_variants_match_arms_and_generics(self):
        rust_src = (
            "struct Cfg {\n"
            "    #[cfg(test)]\n"
            "    debug: bool,\n"
            "    #[cfg(test)]\n"
            "    pub extra: bool,\n"
            "}\n"
            'const PROD_AFTER_STRUCT: &str = "theorem t1 : False := by sorry";\n'
            "enum Mode {\n"
            "    A,\n"
            "    #[cfg(test)]\n"
            "    B,\n"
            "}\n"
            'const PROD_AFTER_ENUM: &str = "theorem t2 : False := by admit";\n'
            "fn pick(x: u8) -> &'static str {\n"
            "    match x {\n"
            '        #[cfg(test)] 0 => "theorem ignored_arm : False := by sorry",\n'
            '        _ => "theorem t3 : False := by sorry",\n'
            "    }\n"
            "}\n"
            "fn pick_last(x: u8) -> &'static str {\n"
            "    match x {\n"
            '        0 => "ok",\n'
            '        #[cfg(test)] _ => "theorem ignored_last : False := by sorry"\n'
            "    }\n"
            "}\n"
            'const PROD_AFTER_MATCH: &str = "theorem t4 : False := by admit";\n'
            "#[cfg(test)]\n"
            "pub fn generic_test<T, U>() where T: Copy, U: Copy {\n"
            '    const X: &str = "public theorem ignored_fn : False := by sorry";\n'
            "}\n"
            'const PROD_AFTER_GENERIC_FN: &str = "theorem t5 : False := by sorry";\n'
        )
        lean_count, findings = scan_rust_template_source(
            rust_src, "cfg_test_variants.rs"
        )
        self.assertEqual(lean_count, 5)
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [
                (7, "sorry"),
                (13, "admit"),
                (17, "sorry"),
                (26, "admit"),
                (31, "sorry"),
            ],
        )

    def test_rust_concat_macro_evaluated_and_non_literal_fails_closed(self):
        rust_src = (
            'const OK: &str = concat!("-- no sorry\\n", "public theorem ok : True := True.intro\\n");\n'
            'const SPLIT_SORRY: &str = concat!("theorem bad1 : False := by sor", "ry\\n");\n'
            'const SPLIT_ADMIT: &str = concat!(r#"theorem bad2 : False := by ad"#, "mit\\n");\n'
            'const DYNAMIC: &str = concat!("theorem bad3 : False := ", DYNAMIC_TOKEN);\n'
        )
        lean_count, findings = scan_rust_template_source(rust_src, "concat_init.rs")
        self.assertGreaterEqual(lean_count, 3)
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [(4, "concat!"), (2, "sorry"), (3, "admit")],
        )

    def test_rust_char_literal_quote_does_not_hide_following_sorry(self):
        rust_src = (
            "fn q() -> char { '\"' }\n"
            "const B: u8 = b'\"';\n"
            'const T: &str = "theorem t : False := by sorry";\n'
        )
        lean_count, findings = scan_rust_template_source(rust_src, "char_quote.rs")
        self.assertEqual(lean_count, 1)
        self.assertEqual([(f.line, f.token) for f in findings], [(3, "sorry")])

    def test_rust_c_raw_and_c_string_literals_handled(self):
        rust_src = (
            'const X: &core::ffi::CStr = cr#"foo\\"#;\n'
            'const Y: &str = "theorem t : False := by sorry";\n'
            'const Z: &core::ffi::CStr = c"theorem t2 : False := by admit";\n'
        )
        lean_count, findings = scan_rust_template_source(rust_src, "c_strings.rs")
        self.assertEqual(lean_count, 2)
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [(2, "sorry"), (3, "admit")],
        )

    def test_checks_toml_anneal_ci_tests_inputs_cover_scanned_trees(self):
        data = tomllib.loads(CHECKS_TOML.read_text(encoding="utf-8"))
        checks = {c["id"]: c for c in data.get("checks", [])}
        self.assertIn("anneal-ci-tests", checks)
        includes = {
            pat
            for inp in checks["anneal-ci-tests"].get("inputs", [])
            if inp.get("kind") == "glob"
            for pat in inp.get("include", [])
        }
        for required in ("anneal/**", "zerocopy/proofs/**", "ci/checks.toml"):
            self.assertIn(required, includes)

    def test_rust_hex_and_unicode_escapes_decoded_and_malformed_rejected(self):
        rust_src = (
            'const HEX: &str = "theorem bad1 : False := by \\x73orry";\n'
            'const UNI1: &str = "theorem bad2 : False := by \\u{73}orry";\n'
            'const UNI2: &str = "theorem bad3 : False := by \\u{00_61}dmit";\n'
            'const BAD_ESC: &str = "theorem bad4 : False := by \\xZZ";\n'
        )
        _, findings = scan_rust_template_source(rust_src, "escapes_init.rs")
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [(4, "escape"), (1, "sorry"), (2, "sorry"), (3, "admit")],
        )

    def test_python_scaffold_detects_sorry_admit_fstrings_and_implicit_concat(self):
        py_src = (
            "# Python comment: never emit sorry or admit\n"
            'CLEAN = "-- Lean comment with sorry\\ntheorem ok : True := True.intro\\n"\n'
            'BAD_SORRY = "theorem bad1 : False := by sorry"\n'
            'BAD_ADMIT = """theorem bad2 : False := by\n  admit\n"""\n'
            'IMPLICIT_CONCAT = ("theorem bad3 : False := by sor" "ry")\n'
            'FSTR_MULTILINE = f"""theorem verify : Expected.claim := by\n  sorry\n"""\n'
            'FSTR_INTERP = f"theorem {name} : False := by admit"\n'
            'FSTR_CONST_SPLIT = f"theorem bad4 : False := by sor{\'\'}ry"\n'
        )
        findings = scan_python_scaffold_source(py_src, "anneal_scaffold.py")
        self.assertEqual(
            [f.token for f in findings],
            ["sorry", "admit", "sorry", "sorry", "admit", "sorry"],
        )

        # Malformed Python syntax in scaffold must fail closed rather than pass.
        bad_py = scan_python_scaffold_source("def broken(:\n", "broken.py")
        self.assertEqual([f.token for f in bad_py], ["SyntaxError"])
