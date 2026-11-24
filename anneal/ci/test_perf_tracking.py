# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `perf_tracking.py`."""

from __future__ import annotations

import copy
import hashlib
import json
import math
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import unittest

import perf_tracking
import prebuild_bundled_oleans


def _make_record(
    *,
    sha_idx: int = 1,
    unix_ts: int = 1795416000,
    profile: str = "github-ubuntu-24.04-x86_64",
    cpu_model: str = "AMD EPYC 7763 64-Core Processor",
    metrics: dict[str, float | int] | None = None,
) -> dict:
    sha = f"{sha_idx:040x}"
    return {
        "schema": perf_tracking.RECORD_SCHEMA,
        "commit": {
            "sha": sha,
            "short_sha": sha[:12],
            "timestamp": "2026-11-23T06:00:00Z",
            "unix_ts": unix_ts,
            "subject": f"Commit {sha_idx}",
            "branch": "main",
        },
        "environment": {
            "profile": profile,
            "os": "Linux",
            "arch": "x86_64",
            "cpu_model": cpu_model,
            "vcpu_count": 4,
            "ram_total_kib": 16374212,
            "lean_version": "4.34.1",
            "rustc_version": "rustc 1.98.0-nightly",
        },
        "sampling": {
            "verify_repeats": 3,
            "aggregation": "median",
            "rss_method": "usr_bin_time",
        },
        "metrics": metrics
        if metrics is not None
        else {
            "verify.scalar.cold_prebuilt_total_ms": 10000.0,
            "memory_rss.verify_scalar.cold_prebuilt_maxrss_kib": 512000,
            "artifact_size.bundled_olean.total_bytes": 10000000,
            "zerocopy_proofs.suite.verified_units_count": 4,
        },
    }


class ValidationTests(unittest.TestCase):
    def test_valid_record_passes(self):
        rec = _make_record()
        self.assertEqual(perf_tracking.validate_record(rec), rec)

    def test_rejects_unknown_top_level_key(self):
        rec = _make_record()
        rec["extra"] = 1
        with self.assertRaises(perf_tracking.ValidationError):
            perf_tracking.validate_record(rec)

    def test_rejects_unsupported_schema(self):
        rec = _make_record()
        rec["schema"] = "anneal-perf-record/v99"
        with self.assertRaises(perf_tracking.ValidationError):
            perf_tracking.validate_record(rec)

    def test_rejects_bool_metric_value(self):
        rec = _make_record()
        rec["metrics"]["verify.scalar.cold_prebuilt_total_ms"] = True
        with self.assertRaises(perf_tracking.ValidationError):
            perf_tracking.validate_record(rec)

    def test_rejects_nan_inf_and_negative_metrics(self):
        for bad in (float("nan"), float("inf"), float("-inf"), -1.0, -5):
            rec = _make_record()
            rec["metrics"]["verify.scalar.cold_prebuilt_total_ms"] = bad
            with self.subTest(bad=bad):
                with self.assertRaises(perf_tracking.ValidationError):
                    perf_tracking.validate_record(rec)

    def test_rejects_invalid_commit_sha(self):
        for bad_sha in ("abc123", "A" * 40, "z" * 40, 123):
            rec = _make_record()
            rec["commit"]["sha"] = bad_sha
            with self.subTest(bad_sha=bad_sha):
                with self.assertRaises(perf_tracking.ValidationError):
                    perf_tracking.validate_record(rec)

    def test_rejects_invalid_metric_ids(self):
        for bad_id in (
            "verify.scalar",
            "Verify.scalar.total_ms",
            "unknown.scalar.total_ms",
            "verify.scalar.bad space",
        ):
            rec = _make_record(metrics={bad_id: 1.0})
            with self.subTest(bad_id=bad_id):
                with self.assertRaises(perf_tracking.ValidationError):
                    perf_tracking.validate_record(rec)

    def test_rejects_symlink_paths(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            real = root / "real.json"
            real.write_text(json.dumps(_make_record()), encoding="utf-8")
            link = root / "link.json"
            link.symlink_to(real)
            with self.assertRaises(perf_tracking.ValidationError):
                perf_tracking.load_record(link)
            with self.assertRaises(perf_tracking.ValidationError):
                perf_tracking.append_record(link, _make_record())


class SubprocessMeasurementTests(unittest.TestCase):
    def test_mock_usr_bin_time_wrapper_parses_maxrss(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake_time = root / "time"
            fake_time.write_text(
                "#!/usr/bin/env python3\n"
                "import pathlib, subprocess, sys\n"
                "args = sys.argv[1:]\n"
                "out = pathlib.Path(args[args.index('-o') + 1])\n"
                "sep = args.index('--')\n"
                "cmd = args[sep + 1:]\n"
                "res = subprocess.run(cmd)\n"
                "out.write_text('__ANNEAL_TIME_MAXRSS_KIB__=42192\\n')\n"
                "sys.exit(res.returncode)\n",
                encoding="utf-8",
            )
            fake_time.chmod(stat.S_IRWXU)
            meas = perf_tracking.run_measured_subprocess(
                [sys.executable, "-c", "print('hello')"],
                time_bin=fake_time,
            )
            self.assertEqual(meas.returncode, 0)
            self.assertEqual(meas.stdout.strip(), "hello")
            self.assertEqual(meas.maxrss_kib, 42192)
            self.assertEqual(meas.rss_method, "usr_bin_time")

    def test_fallback_fork_wait4_when_time_absent(self):
        meas = perf_tracking.run_measured_subprocess(
            [sys.executable, "-c", "print('ok')"],
            time_bin=None,
        )
        self.assertEqual(meas.returncode, 0)
        self.assertEqual(meas.stdout.strip(), "ok")
        self.assertEqual(meas.rss_method, "fallback_wait4")
        self.assertGreater(meas.maxrss_kib, 0)

    def test_real_usr_bin_time_isolates_small_child_rss(self):
        time_bin = Path("/usr/bin/time")
        true_bin = Path("/bin/true")
        if not (
            sys.platform.startswith("linux")
            and time_bin.is_file()
            and true_bin.is_file()
        ):
            self.skipTest("Linux /usr/bin/time or /bin/true unavailable")
        # Allocate 32 MiB transiently in Python parent so parent hiwater_rss
        # exceeds 32 MiB before spawning /bin/true.
        blob = bytearray(32 * 1024 * 1024)
        blob[0] = 1
        del blob
        meas = perf_tracking.run_measured_subprocess(
            [str(true_bin)],
            time_bin=time_bin,
        )
        self.assertEqual(meas.returncode, 0)
        self.assertEqual(meas.rss_method, "usr_bin_time")
        self.assertLess(meas.maxrss_kib, 16384)


class MockCollectionTests(unittest.TestCase):
    def _build_synthetic_repo(self, root: Path) -> dict[str, Path]:
        repo = root / "repo"
        anneal = repo / "anneal"
        (anneal / "trusted/audit").mkdir(parents=True)
        (anneal / "trusted/lean/Trusted").mkdir(parents=True)
        (anneal / "trusted/cargo-anneal/src").mkdir(parents=True)
        (anneal / "trusted/cargo-anneal/tests/fixtures/scalar").mkdir(parents=True)
        (anneal / "theory/Anneal").mkdir(parents=True)
        (repo / "zerocopy/src").mkdir(parents=True)
        (repo / "zerocopy/proofs/01_demo").mkdir(parents=True)

        (repo / "zerocopy/src/lib.rs").write_text("pub fn id(x: u8) -> u8 { x }\n")
        (anneal / "trusted/audit/TrustedBoundary.lean").write_text("-- inspector\n")
        (anneal / "trusted/lean/Trusted.lean").write_text("prelude\nimport Init.Core\n")
        (anneal / "trusted/lean/Trusted/MirAst.lean").write_text(
            "prelude\nimport Trusted\n"
        )
        (anneal / "trusted/cargo-anneal/src/trusted_bundle.rs").write_text(
            'pub const TRUSTED_BUNDLE_SOURCES: &[&str] = &[\n'
            '    "trusted/lean/Trusted.lean",\n'
            '    "trusted/lean/Trusted/MirAst.lean",\n'
            '];\n'
        )
        wp = anneal / "theory/Anneal/MirWp.lean"
        wp.write_text("prelude\nimport Trusted.MirAst\n")
        wp_sha = hashlib.sha256(wp.read_bytes()).hexdigest()
        (anneal / "theory/bundle-manifest.json").write_text(
            json.dumps(
                {
                    "schema_version": 1,
                    "modules": [
                        {"path": "theory/Anneal/MirWp.lean", "sha256": wp_sha}
                    ],
                }
            )
        )
        # Mock Lean sysroot + binary inside an omnibus-style bundle dir
        # (`bundle/lean` beside `bundle/share/anneal/prebuilt/manifest.json`).
        bundle_dir = root / "bundle"
        lean_prefix = bundle_dir / "lean"
        (lean_prefix / "lib/lean/Init").mkdir(parents=True)
        (lean_prefix / "lib/lean/Std").mkdir(parents=True)
        (lean_prefix / "src/lean/Init").mkdir(parents=True)
        (lean_prefix / "src/lean/Std").mkdir(parents=True)
        (lean_prefix / "bin").mkdir(parents=True)
        (bundle_dir / "share/anneal/prebuilt").mkdir(parents=True)
        (bundle_dir / "share/anneal/prebuilt/manifest.json").write_text(
            json.dumps({"schema_version": 1, "entries": []}),
            encoding="utf-8",
        )
        (lean_prefix / "lib/lean/Init/Core.olean").write_bytes(b"core")

        (anneal / "trusted/lean/foundation-lock.json").write_text(
            json.dumps({"modules": {"Init.Core": {}}, "graph": {"Init.Core": []}})
        )
        (anneal / "trusted/audit/library-lock.json").write_text(
            prebuild_bundled_oleans.render_library_lock_for_prefix(lean_prefix),
            encoding="utf-8",
        )

        # Scalar fixture
        scalar_dir = anneal / "trusted/cargo-anneal/tests/fixtures/scalar"
        for name in ("lib.rs", "Spec.lean", "Proof.lean"):
            (scalar_dir / name).write_text("// stub\n")
        (scalar_dir / "request.json").write_text(
            json.dumps({"scope": {"kind": "selected_unit", "roots": ["zero"]}})
        )

        # Zerocopy proof unit
        unit_dir = repo / "zerocopy/proofs/01_demo"
        (unit_dir / "Spec.lean").write_text("-- spec\n")
        (unit_dir / "request.json").write_text(
            json.dumps(
                {
                    "compilation": {"source_root": "../../src"},
                    "scope": {"kind": "selected_unit", "roots": ["id"]},
                    "proof": {
                        "source_root": ".",
                        "sources": [{"path": "Spec.lean"}],
                    },
                }
            )
        )

        # Initialize git repo so commit metadata collection succeeds.
        for cmd in (
            ["git", "init", "-q"],
            ["git", "config", "user.name", "Test"],
            ["git", "config", "user.email", "test@example.com"],
            ["git", "add", "."],
            ["git", "commit", "-qm", "Initial synthetic repo"],
        ):
            subprocess.run(cmd, cwd=repo, check=True)

        lean_log = root / "lean_invocations.jsonl"
        fake_lean = lean_prefix / "bin/lean"
        fake_lean.write_text(
            f"""#!/usr/bin/env python3
import json, pathlib, sys
args = sys.argv[1:]
if "--version" in args:
    print("Lean (version 4.34.1, mock)")
    sys.exit(0)
if "--print-prefix" in args:
    # Return the invoked prefix (2 levels above bin/lean) so mirrored prefixes
    # report their own path accurately without resolving back to bundle/.
    print(pathlib.Path(__file__).resolve().parent.parent)
    sys.exit(0)
if "--run" in args:
    res = {{
        "ok": True,
        "result": {{
            "headers": [
                {{"module": "Trusted", "imports": [{{"module": "Init.Core", "isExported": True, "importAll": False, "isMeta": False}}]}},
                {{"module": "Trusted.MirAst", "imports": [{{"module": "Trusted", "isExported": True, "importAll": False, "isMeta": False}}]}},
                {{"module": "Anneal.MirWp", "imports": [{{"module": "Trusted.MirAst", "isExported": True, "importAll": False, "isMeta": False}}]}},
            ]
        }},
    }}
    pathlib.Path(args[-1]).write_text(json.dumps(res))
    sys.exit(0)
if "-o" in args:
    out = pathlib.Path(args[args.index("-o") + 1])
    with open({str(lean_log)!r}, "a", encoding="utf-8") as logf:
        logf.write(json.dumps({{"src": args[-1], "args": args}}) + "\\n")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(b"olean-public-" + out.name.encode())
    out.with_suffix(".olean.server").write_bytes(b"srv")
    out.with_suffix(".olean.private").write_bytes(b"priv-bytes")
    sys.exit(0)
sys.exit(1)
""",
            encoding="utf-8",
        )
        fake_lean.chmod(stat.S_IRWXU)

        # Mock cargo-anneal CLI + auxiliary binaries
        bin_dir = root / "bin"
        bin_dir.mkdir()
        cli_log = root / "cli_invocations.jsonl"
        fake_cli = bin_dir / "cargo-anneal"
        fake_cli.write_text(
            f"""#!/usr/bin/env python3
import json, os, pathlib, sys
args = sys.argv[1:]
req = json.loads(pathlib.Path(args[args.index("--request") + 1]).read_text())
roots = req["scope"]["roots"]
lean_arg = pathlib.Path(args[args.index("--lean") + 1]) if "--lean" in args else None
has_prebuilt = False
if lean_arg is not None:
    has_prebuilt = (lean_arg.parent.parent.parent / "share/anneal/prebuilt/manifest.json").is_file()
xdg = pathlib.Path(os.environ.get("XDG_CACHE_HOME", ""))
marker = xdg / "anneal/olean-cache/warm.marker"
if "--no-cache" not in args and "--no-rebuild-bundled" not in args and not has_prebuilt:
    marker.parent.mkdir(parents=True, exist_ok=True)
    marker.write_text("warm\\n", encoding="utf-8")
if "--no-rebuild-bundled" in args and not has_prebuilt and not marker.is_file():
    sys.stderr.write("missing disk cache under --no-rebuild-bundled\\n")
    sys.exit(1)
with open({str(cli_log)!r}, "a", encoding="utf-8") as logf:
    logf.write(json.dumps({{"args": args, "has_prebuilt": has_prebuilt, "has_marker": marker.is_file()}}) + "\\n")
timing = {{"capture": 12.5, "proof_and_audit": 40.0, "total": 55.0}}
if "--no-cache" in args:
    timing = {{"capture": 15.0, "proof_and_audit": 120.0, "total": 140.0}}
receipt = {{
    "schema_version": 3,
    "status": "selected_unit_verified",
    "taint_reasons": [],
    "elaboration_sandbox": "linux_bwrap",
    "deferred": [],
    "scope": {{"kind": "selected_unit", "roots": roots}},
    "request_sha256": "reqsha",
    "capture_sha256": "capsha",
    "specification_manifest_sha256": "specsha",
    "model_manifest_sha256": "modsha",
    "timing_ms": timing,
    "audit": {{
        "exactType": True,
        "checkedAlternateProofs": 0,
        "axioms": ["propext"],
        "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
        "bindings": {{
            "requestSha256": "reqsha",
            "captureSha256": "capsha",
            "specificationManifestSha256": "specsha",
            "modelManifestSha256": "modsha",
        }},
    }},
}}
print(json.dumps(receipt))
""",
            encoding="utf-8",
        )
        fake_cli.chmod(stat.S_IRWXU)

        fake_capture = bin_dir / "anneal-rustc-capture"
        fake_capture.write_bytes(b"capture-bin-bytes")
        fake_capture.chmod(stat.S_IRWXU)
        fake_auditor = bin_dir / "anneal-audit"
        fake_auditor.write_bytes(b"auditor-bin")
        fake_auditor.chmod(stat.S_IRWXU)

        rust_sysroot = root / "rust_sysroot"
        (rust_sysroot / "bin").mkdir(parents=True)
        rustc = rust_sysroot / "bin/rustc"
        rustc.write_text("#!/bin/sh\necho 'rustc 1.98.0-nightly'\n")
        rustc.chmod(stat.S_IRWXU)

        archive = root / "omnibus.tar.zst"
        archive.write_bytes(b"zstd-archive-payload")

        fake_time = root / "time"
        fake_time.write_text(
            "#!/usr/bin/env python3\n"
            "import pathlib, subprocess, sys\n"
            "args = sys.argv[1:]\n"
            "out = pathlib.Path(args[args.index('-o') + 1])\n"
            "cmd = args[args.index('--') + 1:]\n"
            "res = subprocess.run(cmd)\n"
            "out.write_text('__ANNEAL_TIME_MAXRSS_KIB__=16384\\n')\n"
            "sys.exit(res.returncode)\n",
            encoding="utf-8",
        )
        fake_time.chmod(stat.S_IRWXU)

        return {
            "repo": repo,
            "anneal": anneal,
            "bundle": bundle_dir,
            "cli": fake_cli,
            "cli_log": cli_log,
            "capture": fake_capture,
            "auditor": fake_auditor,
            "sysroot": rust_sysroot,
            "lean": fake_lean,
            "lean_log": lean_log,
            "archive": archive,
            "time_bin": fake_time,
        }

    def test_end_to_end_collect_all_five_categories(self):
        with tempfile.TemporaryDirectory() as tmp:
            paths = self._build_synthetic_repo(Path(tmp))
            tools = {
                "cli": paths["cli"],
                "capture": paths["capture"],
                "sysroot": paths["sysroot"],
                "lean": paths["lean"],
                "auditor": paths["auditor"],
            }
            record = perf_tracking.collect_record(
                anneal_root=paths["anneal"],
                repo_root=paths["repo"],
                profile="linux-x86_64",
                categories=set(perf_tracking.CATEGORIES),
                modules=None,
                verify_repeats=2,
                cold_no_cache_repeats=1,
                tools=tools,
                omnibus_archive=paths["archive"],
                branch_override="main",
                timeout=30.0,
                time_bin=paths["time_bin"],
            )
            perf_tracking.validate_record(record)
            m = record["metrics"]
            self.assertEqual(m["verify.scalar.cold_no_cache_total_ms"], 140.0)
            self.assertEqual(m["verify.scalar.cold_prebuilt_total_ms"], 55.0)
            self.assertEqual(m["verify.scalar.warm_disk_total_ms"], 55.0)
            self.assertIn("theory_elab.trusted_mirast.cold_j1_ms", m)
            self.assertIn("theory_elab.anneal_mirwp.cold_j1_ms", m)
            self.assertIn("theory_elab.trustedboundary.cold_j1_ms", m)
            self.assertIn("theory_elab.summary.critical_path_ms", m)
            self.assertIn("artifact_size.bundled_olean.total_bytes", m)
            self.assertEqual(
                m["artifact_size.archive.omnibus_tar_zst_bytes"],
                len(b"zstd-archive-payload"),
            )
            self.assertEqual(m["zerocopy_proofs.suite.verified_units_count"], 1)
            self.assertEqual(m["zerocopy_proofs.01_demo.total_ms"], 55.0)

            # Verify `-DwarningAsError=true` is enabled ONLY for Anneal.* theory
            # modules and omitted for TrustedBoundary and Trusted.* modules.
            invocations = [
                json.loads(line)
                for line in paths["lean_log"].read_text(encoding="utf-8").splitlines()
            ]
            by_name = {Path(item["src"]).name: item["args"] for item in invocations}
            self.assertNotIn("-DwarningAsError=true", by_name["TrustedBoundary.lean"])
            self.assertNotIn("-DwarningAsError=true", by_name["Trusted.lean"])
            self.assertNotIn("-DwarningAsError=true", by_name["MirAst.lean"])
            self.assertIn("-DwarningAsError=true", by_name["MirWp.lean"])

            # Verify warm_disk ran without prebuilt manifest and used warm cache.
            cli_runs = [
                json.loads(line)
                for line in paths["cli_log"].read_text(encoding="utf-8").splitlines()
            ]
            warm_runs = [
                c
                for c in cli_runs
                if "--no-rebuild-bundled" in c["args"] and not c["has_prebuilt"]
            ]
            self.assertEqual(len(warm_runs), 2)
            self.assertTrue(all(c["has_marker"] for c in warm_runs))

    def test_verify_scalar_skips_cold_prebuilt_when_manifest_absent(self):
        with tempfile.TemporaryDirectory() as tmp:
            paths = self._build_synthetic_repo(Path(tmp))
            (paths["bundle"] / "share/anneal/prebuilt/manifest.json").unlink()
            tools = {
                "cli": paths["cli"],
                "capture": paths["capture"],
                "sysroot": paths["sysroot"],
                "lean": paths["lean"],
                "auditor": paths["auditor"],
            }
            metrics, _ = perf_tracking.collect_verify_scalar(
                anneal_root=paths["anneal"],
                tools=tools,
                verify_repeats=2,
                cold_no_cache_repeats=1,
                timeout=30.0,
                time_bin=paths["time_bin"],
            )
            self.assertIn("verify.scalar.cold_no_cache_total_ms", metrics)
            self.assertNotIn("verify.scalar.cold_prebuilt_total_ms", metrics)
            self.assertIn("verify.scalar.warm_disk_total_ms", metrics)

    def test_collect_modules_subset_filter(self):
        with tempfile.TemporaryDirectory() as tmp:
            paths = self._build_synthetic_repo(Path(tmp))
            tools = {
                "cli": paths["cli"],
                "capture": paths["capture"],
                "sysroot": paths["sysroot"],
                "lean": paths["lean"],
                "auditor": paths["auditor"],
            }
            record = perf_tracking.collect_record(
                anneal_root=paths["anneal"],
                repo_root=paths["repo"],
                profile="linux-x86_64",
                categories={"theory_elab", "memory_rss", "artifact_size"},
                modules=["Trusted.MirAst"],
                verify_repeats=1,
                cold_no_cache_repeats=1,
                tools=tools,
                omnibus_archive=None,
                branch_override=None,
                timeout=30.0,
                time_bin=paths["time_bin"],
            )
            m = record["metrics"]
            self.assertIn("theory_elab.trusted_mirast.cold_j1_ms", m)
            self.assertNotIn("theory_elab.anneal_mirwp.cold_j1_ms", m)
            self.assertNotIn("theory_elab.trustedboundary.cold_j1_ms", m)


class AppendBudgetsAndAnalysisTests(unittest.TestCase):
    def test_idempotent_append_deduplicates_by_sha_and_profile(self):
        with tempfile.TemporaryDirectory() as tmp:
            jsonl = Path(tmp) / "records.jsonl"
            r1 = _make_record(sha_idx=1, unix_ts=100, profile="p1")
            r2 = _make_record(sha_idx=2, unix_ts=200, profile="p1")
            r1_updated = copy.deepcopy(r1)
            r1_updated["metrics"]["verify.scalar.cold_prebuilt_total_ms"] = 9999.0
            r1_other_prof = _make_record(sha_idx=1, unix_ts=100, profile="p2")

            perf_tracking.append_record(jsonl, r2)
            perf_tracking.append_record(jsonl, r1)
            perf_tracking.append_record(jsonl, r1_updated)
            perf_tracking.append_record(jsonl, r1_other_prof)

            loaded = perf_tracking.load_records_jsonl(jsonl)
            self.assertEqual(len(loaded), 3)
            self.assertEqual(
                [
                    (r["commit"]["sha"], r["environment"]["profile"])
                    for r in loaded
                ],
                [
                    (r1["commit"]["sha"], "p1"),
                    (r1["commit"]["sha"], "p2"),
                    (r2["commit"]["sha"], "p1"),
                ],
            )
            self.assertEqual(
                loaded[0]["metrics"]["verify.scalar.cold_prebuilt_total_ms"],
                9999.0,
            )

    def test_check_budgets_passes_and_catches_ceilings_and_floors(self):
        budgets_path = Path(__file__).resolve().parent / "perf_budgets.json"
        cfg = perf_tracking.load_budgets(budgets_path)

        ok_rec = _make_record(
            metrics={
                "theory_elab.anneal_mirwp.cold_j1_ms": 12000.0,
                "memory_rss.theory_anneal_mirwp.cold_j1_maxrss_kib": 400000,
                "artifact_size.module.anneal_mirwp.olean_bytes": 100000,
                "artifact_size.bundled_olean.total_bytes": 20000000,
                "zerocopy_proofs.suite.verified_units_count": 4,
            }
        )
        self.assertEqual(perf_tracking.evaluate_budgets(ok_rec, cfg), [])

        bad_rec = _make_record(
            metrics={
                "theory_elab.anneal_mirwp.cold_j1_ms": 80000.0,
                "artifact_size.module.trusted.olean_bytes": 4000000,
                "artifact_size.module.anneal_mirwp.olean_bytes": 4000000,
                "zerocopy_proofs.suite.verified_units_count": 3,
            }
        )
        violations = perf_tracking.evaluate_budgets(bad_rec, cfg)
        self.assertEqual(len(violations), 4)
        self.assertEqual(
            {v["metric"] for v in violations},
            {
                "theory_elab.anneal_mirwp.cold_j1_ms",
                "artifact_size.module.trusted.olean_bytes",
                "artifact_size.module.anneal_mirwp.olean_bytes",
                "zerocopy_proofs.suite.verified_units_count",
            },
        )

    def test_rolling_median_mad_distinguishes_spike_vs_step_vs_hw_shift(self):
        baseline_vals = [1000.0, 1010.0, 995.0, 1005.0, 1000.0, 998.0, 1002.0]
        # 1. Single-commit spike -> candidate_spike only
        spike_series = baseline_vals + [1150.0]
        recs_spike = [
            _make_record(
                sha_idx=i + 1,
                unix_ts=1000 + i,
                metrics={"verify.scalar.warm_disk_total_ms": v},
            )
            for i, v in enumerate(spike_series)
        ]
        rep_spike = perf_tracking.analyze_history(recs_spike)
        kinds_spike = [a["kind"] for a in rep_spike["latest_anomalies"]]
        self.assertEqual(kinds_spike, ["candidate_spike"])

        # 2. Two-commit step shift -> confirmed_regression
        step_series = baseline_vals + [1150.0, 1155.0]
        recs_step = [
            _make_record(
                sha_idx=i + 1,
                unix_ts=1000 + i,
                metrics={"verify.scalar.warm_disk_total_ms": v},
            )
            for i, v in enumerate(step_series)
        ]
        rep_step = perf_tracking.analyze_history(recs_step)
        kinds_step = [a["kind"] for a in rep_step["latest_anomalies"]]
        self.assertIn("confirmed_regression", kinds_step)

        # 3. Hardware SKU transition resets the baseline segment and `prev_z`
        # so neither commit `t` nor post-transition commit `t+1` fires a
        # spurious regression against pre-transition SKU timings.
        recs_hw = copy.deepcopy(recs_step)
        recs_hw[-2]["environment"]["cpu_model"] = "Intel Xeon 8370C"
        recs_hw[-1]["environment"]["cpu_model"] = "Intel Xeon 8370C"
        all_hw_anoms = rep_step_hw(recs_hw)
        anoms_at_shift = [
            a["kind"]
            for a in all_hw_anoms
            if a["commit_index"] == len(recs_hw) - 2
        ]
        anoms_post_shift = [
            a["kind"]
            for a in all_hw_anoms
            if a["commit_index"] == len(recs_hw) - 1
        ]
        self.assertEqual(anoms_at_shift, ["hardware_shift"])
        self.assertEqual(anoms_post_shift, [])

        # Once the new SKU accumulates >= min_history commits, real regressions
        # on the new SKU are detected cleanly.
        for offset, val in enumerate(
            [1152.0, 1148.0, 1151.0, 1149.0, 1500.0, 1510.0],
            start=1,
        ):
            recs_hw.append(
                _make_record(
                    sha_idx=100 + offset,
                    unix_ts=2000 + offset,
                    cpu_model="Intel Xeon 8370C",
                    metrics={"verify.scalar.warm_disk_total_ms": val},
                )
            )
        rep_new_sku = perf_tracking.analyze_history(recs_hw)
        self.assertIn(
            "confirmed_regression",
            [a["kind"] for a in rep_new_sku["latest_anomalies"]],
        )

    def test_med_zero_floor_handles_zero_and_positive_jumps(self):
        zero_recs = [
            _make_record(
                sha_idx=i + 1,
                unix_ts=100 + i,
                metrics={"verify.scalar.warm_disk_capture_ms": 0.0},
            )
            for i in range(6)
        ]
        self.assertEqual(perf_tracking.analyze_history(zero_recs)["anomalies"], [])

        zero_recs.append(
            _make_record(
                sha_idx=7,
                unix_ts=107,
                metrics={"verify.scalar.warm_disk_capture_ms": 10.0},
            )
        )
        rep = perf_tracking.analyze_history(zero_recs)
        self.assertEqual(
            [a["kind"] for a in rep["latest_anomalies"]],
            ["confirmed_regression"],
        )

    def test_explicit_missing_or_symlink_budgets_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            jsonl = root / "records.jsonl"
            perf_tracking.append_record(jsonl, _make_record(sha_idx=1, unix_ts=100))
            missing_budgets = root / "missing_budgets.json"
            for cmd in ("analyze", "summary-markdown"):
                with self.assertRaises(perf_tracking.ValidationError):
                    perf_tracking.main(
                        [cmd, str(jsonl), "--budgets", str(missing_budgets)]
                    )
            real_budgets = Path(__file__).resolve().parent / "perf_budgets.json"
            link_budgets = root / "link_budgets.json"
            link_budgets.symlink_to(real_budgets)
            for cmd in ("analyze", "summary-markdown"):
                with self.assertRaises(perf_tracking.ValidationError):
                    perf_tracking.main(
                        [cmd, str(jsonl), "--budgets", str(link_budgets)]
                    )

    def test_deterministic_growth_detection_respects_byte_floor(self):
        recs = [
            _make_record(
                sha_idx=1,
                unix_ts=100,
                metrics={"artifact_size.bin.cargo_anneal_bytes": 100000},
            ),
            _make_record(
                sha_idx=2,
                unix_ts=200,
                metrics={"artifact_size.bin.cargo_anneal_bytes": 102000},
            ),
            _make_record(
                sha_idx=3,
                unix_ts=300,
                metrics={"artifact_size.bin.cargo_anneal_bytes": 115000},
            ),
        ]
        rep = perf_tracking.analyze_history(recs)
        self.assertEqual(
            [a["commit_index"] for a in rep["anomalies"]],
            [2],
        )
        self.assertEqual(rep["anomalies"][0]["kind"], "deterministic_growth")

    def test_geomean_inversion_symmetry(self):
        a = {"m1": 100.0, "m2": 200.0, "m3": 400.0}
        b = {"m1": 200.0, "m2": 100.0, "m3": 520.0}
        r_ab = perf_tracking.compute_geomean_ratio(a, b)
        r_ba = perf_tracking.compute_geomean_ratio(b, a)
        self.assertIsNotNone(r_ab)
        self.assertIsNotNone(r_ba)
        self.assertAlmostEqual(r_ab * r_ba, 1.0, places=5)
        # Balanced [2.0x, 0.5x] pair yields exact 1.0.
        self.assertAlmostEqual(
            perf_tracking.compute_geomean_ratio(
                {"x": 10.0, "y": 20.0}, {"x": 20.0, "y": 10.0}
            ),
            1.0,
            places=6,
        )

    def test_describe_metric_and_summary_markdown(self):
        desc = perf_tracking.describe_metric(
            "artifact_size.module.anneal_mirwp.olean_private_bytes"
        )
        self.assertEqual(desc["category"], "artifact_size")
        self.assertEqual(desc["group"], "artifact_size.module.anneal_mirwp")
        self.assertTrue(desc["deterministic"])
        recs = [_make_record(sha_idx=1, unix_ts=100), _make_record(sha_idx=2, unix_ts=200)]
        md = perf_tracking.render_summary_markdown(recs)
        self.assertIn("## Anneal Performance Tracking Summary", md)
        self.assertIn("verify.scalar.cold_prebuilt_total_ms", md)

    def test_cli_validate_and_check_budgets_exit_codes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            rec_path = root / "rec.json"
            rec_path.write_text(json.dumps(_make_record()), encoding="utf-8")
            self.assertEqual(perf_tracking.main(["validate", str(rec_path)]), 0)
            out_json = root / "budgets_out.json"
            self.assertEqual(
                perf_tracking.main(
                    ["check-budgets", str(rec_path), "--json-out", str(out_json)]
                ),
                0,
            )
            self.assertEqual(json.loads(out_json.read_text())["violations"], [])


def rep_step_hw(recs: list[dict]) -> list[dict]:
    return perf_tracking.analyze_history(recs)["anomalies"]


if __name__ == "__main__":
    unittest.main()
