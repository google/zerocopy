# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Record appending, budget, history analysis, and summary tests for
`perf_tracking.py`."""

from __future__ import annotations

import copy
import json
from pathlib import Path
import tempfile

import perf_tracking
from perf_tracking_tests.support import _make_record


class AppendBudgetsAndAnalysisCases:
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
        budgets_path = Path(__file__).resolve().parent.parent / "perf_budgets.json"
        cfg = perf_tracking.load_budgets(budgets_path)

        ok_rec = _make_record(
            metrics={
                "theory_elab.anneal_mirwp.cold_j1_ms": 12000.0,
                "memory_rss.theory_anneal_mirwp.cold_j1_maxrss_kib": 400000,
                "artifact_size.module.anneal_mirwp.olean_bytes": 100000,
                "artifact_size.bundled_olean.total_bytes": 20000000,
                "zerocopy_proofs.suite.verified_units_count": 5,
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
            real_budgets = Path(__file__).resolve().parent.parent / "perf_budgets.json"
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
