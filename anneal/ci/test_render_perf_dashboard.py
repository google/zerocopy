# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `render_perf_dashboard.py`."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

import perf_tracking
import render_perf_dashboard


def _record(
    sha_idx: int,
    unix_ts: int,
    *,
    subject: str = "Update",
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
            "subject": subject,
            "branch": "main",
        },
        "environment": {
            "profile": "github-ubuntu-24.04-x86_64",
            "os": "Linux",
            "arch": "x86_64",
            "cpu_model": "AMD EPYC 7763 64-Core Processor",
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
            "verify.scalar.cold_prebuilt_total_ms": 10000.0 + sha_idx,
            "artifact_size.bundled_olean.total_bytes": 12000000 + sha_idx,
        },
    }


class RenderPerfDashboardTests(unittest.TestCase):
    def test_pythonhashseed_byte_determinism(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            jsonl = root / "records.jsonl"
            for i in range(1, 6):
                perf_tracking.append_record(jsonl, _record(i, 1795400000 + i * 60))

            out_a = root / "out_a"
            out_b = root / "out_b"
            script = Path(__file__).resolve().parent / "render_perf_dashboard.py"
            budgets = Path(__file__).resolve().parent / "perf_budgets.json"

            for seed, out_dir in (("1", out_a), ("987654321", out_b)):
                env = os.environ.copy()
                env["PYTHONHASHSEED"] = seed
                subprocess.run(
                    [
                        sys.executable,
                        "-B",
                        str(script),
                        "--records",
                        str(jsonl),
                        "--budgets",
                        str(budgets),
                        "--output-dir",
                        str(out_dir),
                    ],
                    env=env,
                    check=True,
                )

            self.assertEqual(
                (out_a / "data.json").read_bytes(),
                (out_b / "data.json").read_bytes(),
            )
            self.assertEqual(
                (out_a / "index.html").read_bytes(),
                (out_b / "index.html").read_bytes(),
            )

    def test_sparse_null_series_alignment_and_windowing(self):
        recs = [
            _record(1, 100, metrics={"verify.scalar.cold_prebuilt_total_ms": 10.0}),
            _record(2, 200, metrics={"artifact_size.bin.cargo_anneal_bytes": 2048}),
            _record(
                3,
                300,
                metrics={
                    "verify.scalar.cold_prebuilt_total_ms": 12.0,
                    "artifact_size.bin.cargo_anneal_bytes": 4096,
                },
            ),
        ]
        bundle = render_perf_dashboard.build_dashboard_bundle(recs, max_commits=3)
        self.assertEqual(len(bundle["commits"]), 3)
        self.assertEqual(
            bundle["series"]["verify.scalar.cold_prebuilt_total_ms"],
            [10.0, None, 12.0],
        )
        self.assertEqual(
            bundle["series"]["artifact_size.bin.cargo_anneal_bytes"],
            [None, 2048, 4096],
        )

        sliced = render_perf_dashboard.build_dashboard_bundle(recs, max_commits=2)
        self.assertEqual(len(sliced["commits"]), 2)
        self.assertEqual(
            sliced["series"]["verify.scalar.cold_prebuilt_total_ms"],
            [None, 12.0],
        )

    def test_inline_script_breakout_and_unicode_separator_sanitization(self):
        evil_subject = 'Fix </script><script>alert("xss")</script> & \u2028\u2029'
        recs = [_record(1, 100, subject=evil_subject)]
        bundle = render_perf_dashboard.build_dashboard_bundle(recs)
        html = render_perf_dashboard.render_html(bundle)

        match = re.search(
            r'<script id="anneal-perf-inline-data" type="application/json">(.*?)</script>',
            html,
            re.DOTALL,
        )
        self.assertIsNotNone(match)
        inline_raw = match.group(1)
        self.assertNotIn("</script>", inline_raw.lower())
        self.assertNotIn("<", inline_raw)
        self.assertNotIn(">", inline_raw)
        self.assertNotIn("&", inline_raw)
        self.assertNotIn("\u2028", inline_raw)
        self.assertNotIn("\u2029", inline_raw)

        decoded = json.loads(inline_raw)
        self.assertEqual(decoded["commits"][0]["subject"], evil_subject)

    def test_rejects_bad_repo_urls(self):
        for bad_url in (
            "javascript:alert(1)",
            "http://github.com/google/zerocopy",
            "https://evil.example/google/zerocopy",
            "https://github.com/google/zerocopy/blob/main",
            "https://github.com/google",
            "https://github.com/./zerocopy",
            "https://github.com/google/.",
            "https://github.com/../zerocopy",
            "https://github.com/google/..",
        ):
            with self.subTest(bad_url=bad_url):
                with self.assertRaises(perf_tracking.ValidationError):
                    render_perf_dashboard.build_dashboard_bundle(
                        [], repo_url=bad_url
                    )

    def test_explicit_missing_or_symlink_budgets_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            jsonl = root / "records.jsonl"
            perf_tracking.append_record(jsonl, _record(1, 100))
            out_dir = root / "dash"
            missing = root / "missing_budgets.json"
            with self.assertRaises(perf_tracking.ValidationError):
                render_perf_dashboard.main(
                    [
                        "--records",
                        str(jsonl),
                        "--budgets",
                        str(missing),
                        "--output-dir",
                        str(out_dir),
                    ]
                )
            real_budgets = Path(__file__).resolve().parent / "perf_budgets.json"
            symlink_budgets = root / "link_budgets.json"
            symlink_budgets.symlink_to(real_budgets)
            with self.assertRaises(perf_tracking.ValidationError):
                render_perf_dashboard.main(
                    [
                        "--records",
                        str(jsonl),
                        "--budgets",
                        str(symlink_budgets),
                        "--output-dir",
                        str(out_dir),
                    ]
                )

    def test_zero_external_http_asset_references(self):
        html = render_perf_dashboard.render_html(
            render_perf_dashboard.build_dashboard_bundle([_record(1, 100)])
        )
        # Strip HTML license comment and inline JSON payload before checking
        # markup/CSS/JS for external http(s):// asset or network references.
        no_comments = re.sub(r"<!--.*?-->", "", html, flags=re.DOTALL)
        no_inline_json = re.sub(
            r'<script id="anneal-perf-inline-data" type="application/json">.*?</script>',
            "",
            no_comments,
            flags=re.DOTALL,
        )
        # `http://www.w3.org/2000/svg` is an XML namespace identifier, not a
        # network resource fetch.
        without_svg_ns = no_inline_json.replace("http://www.w3.org/2000/svg", "")
        self.assertNotRegex(without_svg_ns, r"https?://")

    def test_cotenancy_preserves_existing_root_criterion_dashboard(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            dash_root = root / "dashboard"
            dash_root.mkdir()
            root_index = dash_root / "index.html"
            root_data = dash_root / "data.js"
            root_index.write_text("<html>Criterion Index</html>\n", encoding="utf-8")
            root_data.write_text("window.BENCHMARK_DATA = {};\n", encoding="utf-8")

            jsonl = root / "anneal/records.jsonl"
            perf_tracking.append_record(jsonl, _record(1, 100))
            budgets = Path(__file__).resolve().parent / "perf_budgets.json"

            anneal_out = dash_root / "anneal"
            render_perf_dashboard.write_dashboard(
                records_jsonl=jsonl,
                output_dir=anneal_out,
                budgets_path=budgets,
            )

            self.assertEqual(
                root_index.read_text(encoding="utf-8"),
                "<html>Criterion Index</html>\n",
            )
            self.assertEqual(
                root_data.read_text(encoding="utf-8"),
                "window.BENCHMARK_DATA = {};\n",
            )
            self.assertTrue((anneal_out / "index.html").is_file())
            self.assertTrue((anneal_out / "data.json").is_file())
            data = json.loads((anneal_out / "data.json").read_text(encoding="utf-8"))
            self.assertEqual(data["schema"], render_perf_dashboard.DASHBOARD_SCHEMA)


if __name__ == "__main__":
    unittest.main()
