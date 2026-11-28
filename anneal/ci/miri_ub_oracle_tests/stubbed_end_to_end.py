# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Miri UB oracle tests for stubbed end-to-end runs."""

from __future__ import annotations

from .support import (
    hashlib,
    json,
    _make_tar_gz,
    oracle,
    Path,
    _sample_pin,
    sys,
    tarfile,
    tempfile,
    _write_executable,
)


class StubbedEndToEndCases:
    """`StubbedEndToEndTests` methods for stubbed end-to-end runs."""

    def _build_stubs(self, root: Path, *, eval_mode: str = "normal") -> tuple[Path, Path, Path]:
        sysroot = root / "sysroot"
        (sysroot / "lib").mkdir(parents=True)
        cap_bin = root / "fake-capture"
        eval_bin = root / "fake-eval"

        _write_executable(
            cap_bin,
            f"""#!{sys.executable}
import json, pathlib, sys
args = sys.argv[1:]
src = pathlib.Path(args[args.index("--crate-root") + 1]).read_text()
out = pathlib.Path(args[args.index("--out-dir") + 1])
out.mkdir(parents=True, exist_ok=True)
if "CAPTURE_REFUSE" in src:
    print(json.dumps({{"status": "unsupported", "unsupported": [{{"reason": "stub refused"}}]}}))
    sys.exit(1)
(out / "capture.json").write_text(
    json.dumps({{"marker": src.strip(), "compiler": {{"commit": "{ 'f' * 40 }"}}}})
)
print(json.dumps({{"status": "captured"}}))
""",
        )

        _write_executable(
            eval_bin,
            f"""#!{sys.executable}
import json, pathlib, sys
mode = {eval_mode!r}
args = sys.argv[1:]
cap = pathlib.Path(args[1]).read_text()
if mode == "accept_all":
    print(json.dumps({{"outcome": {{"kind": "returned", "value": {{"kind": "returned"}}}}}}))
    sys.exit(0)
if mode == "reject_all":
    print(json.dumps({{"outcome": {{"kind": "fault", "value": {{"kind": "undefined", "reason": "always ub"}}}}}}))
    sys.exit(2)
if "TRIGGER_UB" in cap:
    print(json.dumps({{"outcome": {{"kind": "fault", "value": {{"kind": "undefined", "reason": "stub ub"}}}}}}))
    sys.exit(2)
print(json.dumps({{"outcome": {{"kind": "returned", "value": {{"kind": "returned"}}}}}}))
sys.exit(0)
""",
        )
        return cap_bin, eval_bin, sysroot

    def test_stubbed_tier_a_passes_and_validates_json_schema(self):
        top = "miri-" + "a" * 40
        with tempfile.TemporaryDirectory(prefix="miri-e2e-a-") as tmp:
            tmp_path = Path(tmp)
            archive = tmp_path / "miri.tar.gz"
            ub1_bytes = b"// TRIGGER_UB\nfn main() {}\n"
            refused_bytes = b"// CAPTURE_REFUSE\nfn main() {}\n"
            archive_sha = _make_tar_gz(
                archive,
                [
                    (f"{top}/tests/fail/ub1.rs", ub1_bytes, tarfile.REGTYPE),
                    (f"{top}/tests/fail-dep/refused.rs", refused_bytes, tarfile.REGTYPE),
                ],
            )
            extract_tmp = tmp_path / "hash_check"
            oracle.safe_extract_miri_corpus(
                archive,
                extract_tmp,
                expected_top_dir=top,
                extract_subdirs=["tests/fail", "tests/fail-dep"],
            )
            manifest_sha, _ = oracle.compute_corpus_manifest_sha256(
                extract_tmp, ["tests/fail", "tests/fail-dep"]
            )
            fail_node = {
                "ub1.rs": (
                    b"100644",
                    hashlib.sha1(
                        f"blob {len(ub1_bytes)}\x00".encode("ascii") + ub1_bytes
                    ).digest(),
                )
            }
            fail_dep_node = {
                "refused.rs": (
                    b"100644",
                    hashlib.sha1(
                        f"blob {len(refused_bytes)}\x00".encode("ascii") + refused_bytes
                    ).digest(),
                )
            }
            pin_obj = _sample_pin(
                archive_sha=archive_sha,
                manifest_sha=manifest_sha,
                expected_file_count=2,
                min_caught_ub=1,
            )
            pin_obj["miri_tree_sha"] = oracle._compute_git_tree_sha1(
                {"tests": {"fail": fail_node, "fail-dep": fail_dep_node}}
            ).hex()
            pin_obj["fail_tree_sha"] = oracle._compute_git_tree_sha1(fail_node).hex()
            pin_obj["fail_dep_tree_sha"] = oracle._compute_git_tree_sha1(
                fail_dep_node
            ).hex()
            pin_path = tmp_path / "pin.json"
            pin_path.write_text(json.dumps(pin_obj), encoding="utf-8")
            cap_bin, eval_bin, sysroot = self._build_stubs(tmp_path)
            out_json = tmp_path / "report.json"
            out_md = tmp_path / "summary.md"

            rc = oracle.main([
                "--tier-a",
                "--pin", str(pin_path),
                "--archive", str(archive),
                "--no-network",
                "--capture-bin", str(cap_bin),
                "--eval-bin", str(eval_bin),
                "--sysroot", str(sysroot),
                "--workers", "2",
                "--max-memory-mb", "512",
                "--output", str(out_json),
                "--summary-markdown", str(out_md),
            ])
            self.assertEqual(rc, 0)
            report = json.loads(out_json.read_text(encoding="utf-8"))
            self.assertEqual(report["schema_version"], oracle.REPORT_SCHEMA_VERSION)
            self.assertEqual(report["tier"], "tier_a")
            self.assertTrue(report["passed"])
            self.assertNotIn("elapsed_secs", report)
            for unit in report["units"]:
                self.assertNotIn("capture_secs", unit)
                self.assertNotIn("eval_secs", unit)
            self.assertEqual(report["counts"]["caught_ub"], 1)
            self.assertEqual(report["counts"]["capture_refused"], 1)
            self.assertEqual(report["counts"]["unsound_accept"], 0)
            self.assertIn("PASS", out_md.read_text(encoding="utf-8"))

            # Re-running must produce byte-for-byte identical JSON output.
            out_json2 = tmp_path / "report2.json"
            rc2 = oracle.main([
                "--tier-a",
                "--pin", str(pin_path),
                "--archive", str(archive),
                "--no-network",
                "--capture-bin", str(cap_bin),
                "--eval-bin", str(eval_bin),
                "--sysroot", str(sysroot),
                "--workers", "2",
                "--max-memory-mb", "512",
                "--output", str(out_json2),
            ])
            self.assertEqual(rc2, 0)
            self.assertEqual(
                out_json.read_bytes(), out_json2.read_bytes()
            )

            # Unsound accept with accept_all eval must exit 1.
            cap_bin2, eval_bin2, sysroot2 = self._build_stubs(
                tmp_path / "bad", eval_mode="accept_all"
            )
            rc_bad = oracle.main([
                "--tier-a",
                "--pin", str(pin_path),
                "--archive", str(archive),
                "--no-network",
                "--capture-bin", str(cap_bin2),
                "--eval-bin", str(eval_bin2),
                "--sysroot", str(sysroot2),
                "--workers", "1",
            ])
            self.assertEqual(rc_bad, 1)

    def test_stubbed_tier_b_rejects_orphan_and_reject_all_evaluator(self):
        with tempfile.TemporaryDirectory(prefix="miri-e2e-b-") as tmp:
            tmp_path = Path(tmp)
            corpus = tmp_path / "corpus"
            corpus.mkdir()
            (corpus / "ub.rs").write_text("// TRIGGER_UB\nfn main() {}\n", encoding="utf-8")
            (corpus / "ok.rs").write_text("fn main() {}\n", encoding="utf-8")
            (corpus / "manifest.json").write_text(
                json.dumps({
                    "schema_version": 1,
                    "fixtures": [
                        {
                            "id": "ub1",
                            "path": "ub.rs",
                            "kind": "rust_ub_caught",
                            "category": "arith",
                            "expected_fault_substring": "stub ub",
                        },
                        {"id": "ok1", "path": "ok.rs", "kind": "rust_valid_control", "category": "valid"},
                    ],
                }),
                encoding="utf-8",
            )
            cap_bin, eval_bin, sysroot = self._build_stubs(tmp_path)
            rc = oracle.main([
                "--tier-b",
                "--tier-b-dir", str(corpus),
                "--capture-bin", str(cap_bin),
                "--eval-bin", str(eval_bin),
                "--sysroot", str(sysroot),
                "--workers", "2",
                "--max-memory-mb", "512",
            ])
            self.assertEqual(rc, 0)

            # A reject-all evaluator must fail Tier B on the valid control.
            cap_r, eval_r, sys_r = self._build_stubs(tmp_path / "rej", eval_mode="reject_all")
            rc_rej = oracle.main([
                "--tier-b",
                "--tier-b-dir", str(corpus),
                "--capture-bin", str(cap_r),
                "--eval-bin", str(eval_r),
                "--sysroot", str(sys_r),
                "--workers", "1",
            ])
            self.assertEqual(rc_rej, 1)

            # Adding an unlisted orphan fixture MUST fail closed (exit 2).
            (corpus / "orphan.rs").write_text("fn main() {}\n", encoding="utf-8")
            rc_orphan = oracle.main([
                "--tier-b",
                "--tier-b-dir", str(corpus),
                "--capture-bin", str(cap_bin),
                "--eval-bin", str(eval_bin),
                "--sysroot", str(sysroot),
            ])
            self.assertEqual(rc_orphan, 2)

    def test_capture_rc_status_mismatch_and_bad_tier_b_fields_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix="miri-cap-rc-") as tmp:
            tmp_path = Path(tmp)
            sysroot = tmp_path / "sysroot"
            (sysroot / "lib").mkdir(parents=True)
            cap_bad = tmp_path / "cap-bad"
            eval_ok = tmp_path / "eval-ok"
            _write_executable(
                cap_bad,
                f"""#!{sys.executable}
import json, sys
print(json.dumps({{"status": "unsupported"}}))
sys.exit(0)
""",
            )
            _write_executable(eval_ok, f"#!{sys.executable}\nimport sys; sys.exit(0)\n")
            src = tmp_path / "a.rs"
            src.write_text("fn main() {}\n", encoding="utf-8")
            rec = oracle.evaluate_rust_unit(
                src,
                "fail/a.rs",
                revision=None,
                flags=[],
                capture_bin=cap_bad,
                eval_bin=eval_ok,
                sysroot=sysroot,
                target="x86_64-unknown-linux-gnu",
                fuel=1000,
                profile="v1",
                timeout_secs=10,
                max_memory_mb=oracle.DEFAULT_MAX_MEMORY_MB,
                expect_valid=False,
            )
            self.assertEqual(rec["bucket"], "tool_error")
            self.assertIn("capture_rc_status_mismatch", str(rec["sub_bucket"]))

            # Invalid Tier B optional fields must fail closed at manifest load.
            for label, patch in (
                ("bad_profile", {"profile": "v3"}),
                ("bad_args", {"args": "ab"}),
                ("bad_fuel", {"fuel": 0}),
                ("bad_edition", {"edition": "1999"}),
                ("bad_panic", {"panic": "trap"}),
                ("missing_sub", {"expected_fault_substring": ""}),
            ):
                with self.subTest(case=label):
                    cdir = tmp_path / f"tb-{label}"
                    cdir.mkdir()
                    (cdir / "ub.rs").write_text("fn main() {}\n", encoding="utf-8")
                    (cdir / "ok.rs").write_text("fn main() {}\n", encoding="utf-8")
                    ub_entry = {
                        "id": "ub1",
                        "path": "ub.rs",
                        "kind": "rust_ub_caught",
                        "category": "arith",
                        "expected_fault_substring": "ub",
                    }
                    ub_entry.update(patch)
                    (cdir / "manifest.json").write_text(
                        json.dumps({
                            "schema_version": 1,
                            "fixtures": [
                                ub_entry,
                                {"id": "ok1", "path": "ok.rs", "kind": "rust_valid_control", "category": "valid"},
                            ],
                        }),
                        encoding="utf-8",
                    )
                    with self.assertRaises(oracle.OracleError):
                        oracle.load_tier_b_manifest(cdir)
