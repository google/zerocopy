# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `prebuild_bundled_oleans.py`."""

import json
import os
from pathlib import Path
import stat
import tempfile
import unittest

import prebuild_bundled_oleans


class PrebuildBundledOleansTests(unittest.TestCase):
    def test_module_keyword_detector_skips_comments(self):
        self.assertFalse(prebuild_bundled_oleans.source_starts_with_module_keyword(b"prelude\n"))
        self.assertTrue(
            prebuild_bundled_oleans.source_starts_with_module_keyword(
                b"-- comment\n/- nested /- block -/ -/\nmodule\nprelude\n"
            )
        )
        self.assertFalse(
            prebuild_bundled_oleans.source_starts_with_module_keyword(b"module_foo\n")
        )

    def test_prebuild_synthetic_pipeline_generates_valid_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            lean_prefix = Path(tmp) / "sysroot"
            out_dir = Path(tmp) / "prebuilt"
            (lean_prefix / "lib/lean/Init").mkdir(parents=True)
            (lean_prefix / "lib/lean/Std").mkdir(parents=True)
            (lean_prefix / "src/lean/Init").mkdir(parents=True)
            (lean_prefix / "src/lean/Std").mkdir(parents=True)
            (lean_prefix / "bin").mkdir(parents=True)
            init_core = lean_prefix / "lib/lean/Init/Core.olean"
            init_core.write_bytes(b"olean\x02synthetic-core")
            (lean_prefix / "lib/lean/Std/Basic.olean").write_bytes(b"olean\x02synthetic-std")
            (lean_prefix / "src/lean/Init/Core.lean").write_text("-- core\n", encoding="utf-8")
            (lean_prefix / "src/lean/Std/Basic.lean").write_text("-- std\n", encoding="utf-8")

            (root / "trusted/audit").mkdir(parents=True)
            (root / "trusted/lean/Trusted").mkdir(parents=True)
            (root / "trusted/cargo-anneal/src").mkdir(parents=True)
            (root / "theory/Anneal").mkdir(parents=True)

            inspector = root / "trusted/audit/TrustedBoundary.lean"
            inspector.write_text("-- inspector\n", encoding="utf-8")
            (root / "trusted/lean/foundation-lock.json").write_text(
                json.dumps(
                    {
                        "modules": {"Init.Core": {}},
                        "graph": {"Init.Core": []},
                    }
                ),
                encoding="utf-8",
            )
            (root / "trusted/audit/library-lock.json").write_text(
                prebuild_bundled_oleans.render_library_lock_for_prefix(lean_prefix),
                encoding="utf-8",
            )

            mir_ast = root / "trusted/lean/Trusted/MirAst.lean"
            mir_ast.write_text("module\nprelude\npublic import Init.Core\n", encoding="utf-8")
            (root / "trusted/cargo-anneal/src/bundle.rs").write_text(
                'pub const TRUSTED_BUNDLE_SOURCES: &[&str] = &[\n'
                '    "trusted/lean/Trusted/MirAst.lean",\n'
                '];\n',
                encoding="utf-8",
            )

            wp = root / "theory/Anneal/MirWp.lean"
            wp.write_text("module\nprelude\npublic import Trusted.MirAst\n", encoding="utf-8")
            wp_sha = prebuild_bundled_oleans.sha256_file(wp)
            (root / "theory/bundle-manifest.json").write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "modules": [{"path": "theory/Anneal/MirWp.lean", "sha256": wp_sha}],
                    }
                ),
                encoding="utf-8",
            )

            fake_lean = lean_prefix / "bin/lean"
            fake_lean.write_text(
                """#!/usr/bin/env python3
import json, pathlib, sys
args = sys.argv[1:]
if "--run" in args:
    req = json.loads(pathlib.Path(args[-2]).read_text())
    if req.get("mode") == "resolve-imports":
        res = {
            "ok": True,
            "result": {
                "graph": {
                    "Init.Core": [],
                    "Std.Basic": [
                        {"module": "Init.Core", "isExported": True, "importAll": False, "isMeta": False}
                    ],
                }
            },
        }
        pathlib.Path(args[-1]).write_text(json.dumps(res))
        sys.exit(0)
    res = {
        "ok": True,
        "result": {
            "headers": [
                {
                    "module": "Trusted.MirAst",
                    "isModule": True,
                    "imports": [{"module": "Init.Core", "isExported": True, "importAll": False, "isMeta": False}],
                },
                {
                    "module": "Anneal.MirWp",
                    "isModule": True,
                    "imports": [
                        {"module": "Trusted.MirAst", "isExported": True, "importAll": False, "isMeta": False},
                        {"module": "Std.Basic", "isExported": True, "importAll": False, "isMeta": False},
                    ],
                },
            ]
        },
    }
    pathlib.Path(args[-1]).write_text(json.dumps(res))
    sys.exit(0)
if "-o" in args:
    out = pathlib.Path(args[args.index("-o") + 1])
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(b"olean\\x024.34.1\\x00" + out.name.encode())
    if "--setup" in args:
        setup = json.loads(pathlib.Path(args[args.index("--setup") + 1]).read_text())
        if not setup.get("isModule"):
            sys.stderr.write("expected isModule=true in setup.json\\n")
            sys.exit(2)
        out.with_suffix(".olean.server").write_bytes(b"olean\\x024.34.1\\x00srv-" + out.name.encode())
        out.with_suffix(".olean.private").write_bytes(b"olean\\x024.34.1\\x00prv-" + out.name.encode())
        out.with_suffix(".ir").write_bytes(b"ir-discard")
    sys.exit(0)
sys.exit(1)
""",
                encoding="utf-8",
            )
            fake_lean.chmod(stat.S_IRWXU)

            manifest = prebuild_bundled_oleans.prebuild(
                anneal_root=root,
                lean_bin=fake_lean,
                lean_exec=fake_lean,
                lean_prefix=lean_prefix,
                output_dir=out_dir,
                jobs=2,
            )
            self.assertEqual(manifest["schema_version"], 1)
            by_mod = {(e["kind"], e["module"]): e for e in manifest["entries"]}
            self.assertEqual(
                set(by_mod.keys()),
                {
                    ("inspector", "TrustedBoundary"),
                    ("module", "Trusted.MirAst"),
                    ("module", "Anneal.MirWp"),
                },
            )
            mir_ast_entry = by_mod[("module", "Trusted.MirAst")]
            mir_wp_entry = by_mod[("module", "Anneal.MirWp")]
            self.assertTrue(mir_ast_entry["is_module"])
            self.assertTrue(mir_wp_entry["is_module"])
            self.assertEqual(
                [p["suffix"] for p in mir_ast_entry["parts"]],
                ["olean", "olean.server", "olean.private"],
            )
            self.assertEqual(
                mir_wp_entry["imports"][0]["part_sha256s"],
                [p["sha256"] for p in mir_ast_entry["parts"]],
            )
            self.assertEqual(
                mir_wp_entry["imports"][1]["part_sha256s"],
                [prebuild_bundled_oleans.sha256_file(lean_prefix / "lib/lean/Std/Basic.olean")],
            )
            self.assertTrue((out_dir / "TrustedBoundary.olean").is_file())
            self.assertTrue((out_dir / "lib/Trusted/MirAst.olean").is_file())
            self.assertTrue((out_dir / "lib/Trusted/MirAst.olean.server").is_file())
            self.assertTrue((out_dir / "lib/Trusted/MirAst.olean.private").is_file())
            self.assertFalse((out_dir / "lib/Trusted/MirAst.ir").exists())
            self.assertTrue((out_dir / "lib/Anneal/MirWp.olean").is_file())
            self.assertTrue((out_dir / "manifest.json").is_file())

    def test_prebuild_keeps_setup_is_module_consistent_with_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            lean_prefix = Path(tmp) / "sysroot"
            out_dir = Path(tmp) / "prebuilt"
            recorded_setups = Path(tmp) / "recorded_setups.jsonl"
            for rel in ("lib/lean/Init", "lib/lean/Std", "src/lean/Init", "src/lean/Std", "bin"):
                (lean_prefix / rel).mkdir(parents=True)
            (lean_prefix / "lib/lean/Init/Core.olean").write_bytes(
                b"olean\x02synthetic-core"
            )

            (root / "trusted/audit").mkdir(parents=True)
            (root / "trusted/lean/Trusted").mkdir(parents=True)
            (root / "trusted/cargo-anneal/src").mkdir(parents=True)
            (root / "theory/Anneal").mkdir(parents=True)

            (root / "trusted/audit/TrustedBoundary.lean").write_text(
                "-- inspector\n", encoding="utf-8"
            )
            (root / "trusted/lean/foundation-lock.json").write_text(
                json.dumps(
                    {
                        "modules": {"Init.Core": {}},
                        "graph": {"Init.Core": []},
                    }
                ),
                encoding="utf-8",
            )
            (root / "trusted/audit/library-lock.json").write_text(
                prebuild_bundled_oleans.render_library_lock_for_prefix(lean_prefix),
                encoding="utf-8",
            )

            (root / "trusted/lean/Trusted/MirAst.lean").write_text(
                "prelude\nimport Init.Core\n", encoding="utf-8"
            )
            (root / "trusted/cargo-anneal/src/bundle.rs").write_text(
                'pub const TRUSTED_BUNDLE_SOURCES: &[&str] = &[\n'
                '    "trusted/lean/Trusted/MirAst.lean",\n'
                '];\n',
                encoding="utf-8",
            )

            wp = root / "theory/Anneal/MirWp.lean"
            wp.write_text(
                "-- leading comment\nmodule\nprelude\nimport Trusted.MirAst\n",
                encoding="utf-8",
            )
            wp_sha = prebuild_bundled_oleans.sha256_file(wp)
            (root / "theory/bundle-manifest.json").write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "modules": [
                            {
                                "path": "theory/Anneal/MirWp.lean",
                                "sha256": wp_sha,
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            fake_lean = lean_prefix / "bin/lean"
            fake_lean.write_text(
                f"""#!/usr/bin/env python3
import json, pathlib, sys
args = sys.argv[1:]
if "--run" in args:
    res = {{
        "ok": True,
        "result": {{
            "headers": [
                {{
                    "module": "Trusted.MirAst",
                    "imports": [{{"module": "Init.Core", "isExported": True, "importAll": False, "isMeta": False}}],
                }},
                {{
                    "module": "Anneal.MirWp",
                    "imports": [{{"module": "Trusted.MirAst", "isExported": True, "importAll": False, "isMeta": False}}],
                }},
            ]
        }},
    }}
    pathlib.Path(args[-1]).write_text(json.dumps(res))
    sys.exit(0)
if "--setup" in args:
    setup = json.loads(pathlib.Path(args[args.index("--setup") + 1]).read_text())
    with pathlib.Path({str(recorded_setups)!r}).open("a", encoding="utf-8") as f:
        f.write(json.dumps({{"name": setup["name"], "isModule": setup["isModule"]}}) + "\\n")
if "-o" in args:
    out = pathlib.Path(args[args.index("-o") + 1])
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(b"olean\\x024.34.1\\x00" + out.name.encode())
    sys.exit(0)
sys.exit(1)
""",
                encoding="utf-8",
            )
            fake_lean.chmod(stat.S_IRWXU)

            manifest = prebuild_bundled_oleans.prebuild(
                anneal_root=root,
                lean_bin=fake_lean,
                lean_exec=fake_lean,
                lean_prefix=lean_prefix,
                output_dir=out_dir,
                jobs=1,
            )
            setup_by_mod = {
                row["name"]: row["isModule"]
                for row in (
                    json.loads(line)
                    for line in recorded_setups.read_text(encoding="utf-8").splitlines()
                )
            }
            by_mod = {
                e["module"]: e
                for e in manifest["entries"]
                if e["kind"] == "module"
            }
            self.assertEqual(
                setup_by_mod,
                {"Trusted.MirAst": False, "Anneal.MirWp": True},
            )
            for mod, expected in (
                ("Trusted.MirAst", False),
                ("Anneal.MirWp", True),
            ):
                self.assertEqual(by_mod[mod]["is_module"], expected)
                self.assertEqual(setup_by_mod[mod], by_mod[mod]["is_module"])

    def test_prebuild_rejects_legacy_or_tampered_library_lock(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "anneal"
            lean_prefix = Path(tmp) / "sysroot"
            out_dir = Path(tmp) / "prebuilt"
            for rel in ("lib/lean/Init", "lib/lean/Std", "src/lean/Init", "src/lean/Std", "bin"):
                (lean_prefix / rel).mkdir(parents=True)
            (lean_prefix / "lib/lean/Init/Core.olean").write_bytes(b"olean\x02synthetic")
            (root / "trusted/audit").mkdir(parents=True)
            (root / "trusted/lean").mkdir(parents=True)
            (root / "trusted/cargo-anneal/src").mkdir(parents=True)
            (root / "theory").mkdir(parents=True)
            (root / "trusted/audit/TrustedBoundary.lean").write_text("-- inspector\n", encoding="utf-8")
            (root / "trusted/lean/foundation-lock.json").write_text(
                json.dumps({"modules": {"Init.Core": {}}, "graph": {"Init.Core": []}}),
                encoding="utf-8",
            )
            (root / "trusted/cargo-anneal/src/bundle.rs").write_text(
                'pub const TRUSTED_BUNDLE_SOURCES: &[&str] = &["trusted/lean/Trusted.lean"];\n',
                encoding="utf-8",
            )
            (root / "trusted/lean/Trusted.lean").write_text("prelude\nimport Init.Core\n", encoding="utf-8")
            theory_mod = root / "theory/Anneal.lean"
            theory_mod.write_text("prelude\nimport Init.Core\n", encoding="utf-8")
            (root / "theory/bundle-manifest.json").write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "modules": [
                            {
                                "path": "theory/Anneal.lean",
                                "sha256": prebuild_bundled_oleans.sha256_file(theory_mod),
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            fake_lean = lean_prefix / "bin/lean"
            fake_lean.write_text("#!/usr/bin/env python3\nimport sys\nsys.exit(1)\n", encoding="utf-8")
            fake_lean.chmod(stat.S_IRWXU)

            lock_path = root / "trusted/audit/library-lock.json"
            lock_path.write_text(json.dumps({"modules": {}, "graph": {}}), encoding="utf-8")
            with self.assertRaisesRegex(RuntimeError, "invalid library-lock line"):
                prebuild_bundled_oleans.prebuild(
                    anneal_root=root,
                    lean_bin=fake_lean,
                    lean_exec=fake_lean,
                    lean_prefix=lean_prefix,
                    output_dir=out_dir,
                    jobs=1,
                )

            valid_lines = prebuild_bundled_oleans.render_library_lock_for_prefix(lean_prefix).splitlines()
            tampered = [f"{'0' * 64}  lean/lib/lean/Init/**"] + valid_lines[1:]
            lock_path.write_text("\n".join(tampered) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(RuntimeError, "SHA-256 mismatch"):
                prebuild_bundled_oleans.prebuild(
                    anneal_root=root,
                    lean_bin=fake_lean,
                    lean_exec=fake_lean,
                    lean_prefix=lean_prefix,
                    output_dir=out_dir,
                    jobs=1,
                )


if __name__ == "__main__":
    unittest.main()
