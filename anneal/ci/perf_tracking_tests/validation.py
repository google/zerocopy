# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Record validation tests for `perf_tracking.py`."""

from __future__ import annotations

import json
from pathlib import Path
import tempfile

import perf_tracking
from perf_tracking_tests.support import _make_record


class ValidationCases:
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
