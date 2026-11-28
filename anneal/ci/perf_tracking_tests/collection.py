# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Metric collection tests for `perf_tracking.py`, run against the
synthetic repository and fake tools of `SyntheticRepoFixture`."""

from __future__ import annotations

import json
from pathlib import Path
import tempfile
from unittest import mock

import perf_tracking
from perf_tracking_tests.support import _make_record


class MockCollectionCases:
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
            self.assertEqual(len(perf_tracking.COLLECTABLE_CATEGORIES), 5)
            self.assertNotIn(
                "differential_oracle", perf_tracking.COLLECTABLE_CATEGORIES
            )
            record = perf_tracking.collect_record(
                anneal_root=paths["anneal"],
                repo_root=paths["repo"],
                profile="linux-x86_64",
                categories=set(perf_tracking.COLLECTABLE_CATEGORIES),
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

            # Verify every CLI invocation (including zerocopy_proofs) passes
            # `--format json` explicitly under the human-default CLI contract.
            cli_runs = [
                json.loads(line)
                for line in paths["cli_log"].read_text(encoding="utf-8").splitlines()
            ]
            self.assertGreaterEqual(len(cli_runs), 4)
            for run in cli_runs:
                self.assertIn("--format", run["args"])
                fmt_idx = run["args"].index("--format")
                self.assertEqual(run["args"][fmt_idx + 1], "json")
            warm_runs = [
                c
                for c in cli_runs
                if "--no-rebuild-bundled" in c["args"] and not c["has_prebuilt"]
            ]
            self.assertEqual(len(warm_runs), 2)
            self.assertTrue(all(c["has_marker"] for c in warm_runs))

    def test_collect_zerocopy_proofs_forwards_instantiations(self):
        with tempfile.TemporaryDirectory() as tmp:
            paths = self._build_synthetic_repo(Path(tmp))
            base_req = json.loads(
                (
                    paths["repo"] / "zerocopy/proofs/01_demo/request.json"
                ).read_text(encoding="utf-8")
            )
            mono_dir = paths["repo"] / "zerocopy/proofs/02_mono"
            mono_dir.mkdir(parents=True)
            (mono_dir / "Spec.lean").write_text(
                "prelude\ndef specs : Specs := ⟨(), ()⟩\n", encoding="utf-8"
            )
            (mono_dir / "Proof.lean").write_text("prelude\n", encoding="utf-8")
            mono_scope = {
                "kind": "selected_unit",
                "roots": [],
                "instantiations": [{"path": "core::id", "args": ["u32"]}],
            }
            (mono_dir / "request.json").write_text(
                json.dumps(dict(base_req, scope=mono_scope)),
                encoding="utf-8",
            )
            tools = {
                "cli": paths["cli"],
                "capture": paths["capture"],
                "sysroot": paths["sysroot"],
                "lean": paths["lean"],
                "time_bin": paths["time_bin"],
            }
            metrics, rss_methods = perf_tracking.collect_zerocopy_proofs(
                repo_root=paths["repo"],
                tools=tools,
                timeout=30,
                time_bin=paths["time_bin"],
            )
            self.assertEqual(rss_methods, {"usr_bin_time"})
            self.assertEqual(metrics["zerocopy_proofs.suite.verified_units_count"], 2)
            self.assertEqual(metrics["zerocopy_proofs.02_mono.total_ms"], 55.0)

            # 1. Fail closed on instantiation-only unit when receipt emits
            # a different valid instantiation (intrinsically non-empty scope).
            cli_text = paths["cli"].read_text(encoding="utf-8")
            paths["cli"].write_text(
                cli_text.replace(
                    '"instantiations": instantiations',
                    '"instantiations": [{"path": "core::id", "args": ["u8"]}]',
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(RuntimeError, "scope mismatch"):
                perf_tracking.collect_zerocopy_proofs(
                    repo_root=paths["repo"],
                    tools=tools,
                    timeout=30,
                    time_bin=paths["time_bin"],
                )

            # 2. Fail closed on mixed unit (`roots` + `instantiations`)
            # when receipt omits `instantiations`.
            mixed_scope = {
                "kind": "selected_unit",
                "roots": ["id"],
                "instantiations": [{"path": "core::id", "args": ["u32"]}],
            }
            (mono_dir / "request.json").write_text(
                json.dumps(dict(base_req, scope=mixed_scope)),
                encoding="utf-8",
            )
            paths["cli"].write_text(
                cli_text.replace(
                    '**({"instantiations": instantiations} if instantiations else {})',
                    "**{}",
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(RuntimeError, "scope mismatch"):
                perf_tracking.collect_zerocopy_proofs(
                    repo_root=paths["repo"],
                    tools=tools,
                    timeout=30,
                    time_bin=paths["time_bin"],
                )

            # 3. Fail closed when receipt `audit.specification` drifts from
            # `request.json`.
            paths["cli"].write_text(
                cli_text.replace('"Spec.specs"', '"WeakSpec.specs"'),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(RuntimeError, "audit\\.specification"):
                perf_tracking.collect_zerocopy_proofs(
                    repo_root=paths["repo"],
                    tools=tools,
                    timeout=30,
                    time_bin=paths["time_bin"],
                )

            # 4. Fail closed when receipt embeds `configuration.stdlib_crate`.
            paths["cli"].write_text(
                cli_text.replace(
                    '"endian": "little",',
                    '"endian": "little", "stdlib_crate": {"crate_type": "core"},',
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                RuntimeError, "unexpected configuration keys=\\['stdlib_crate'\\]"
            ):
                perf_tracking.collect_zerocopy_proofs(
                    repo_root=paths["repo"],
                    tools=tools,
                    timeout=30,
                    time_bin=paths["time_bin"],
                )

    def test_collect_zerocopy_proofs_rejects_profile_and_config_mismatch(self):
        with tempfile.TemporaryDirectory() as tmp:
            paths = self._build_synthetic_repo(Path(tmp))
            base_req = json.loads(
                (
                    paths["repo"] / "zerocopy/proofs/01_demo/request.json"
                ).read_text(encoding="utf-8")
            )
            v2_dir = paths["repo"] / "zerocopy/proofs/02_v2"
            v2_dir.mkdir(parents=True)
            (v2_dir / "Spec.lean").write_text(
                "prelude\ndef specs : SpecsV2 := ⟨(), ()⟩\n", encoding="utf-8"
            )
            (v2_dir / "Proof.lean").write_text("prelude\n", encoding="utf-8")
            v2_req = dict(
                base_req,
                scope={
                    "kind": "selected_unit",
                    "roots": ["byte_slice::split"],
                },
            )
            (v2_dir / "request.json").write_text(
                json.dumps(v2_req),
                encoding="utf-8",
            )
            tools = {
                "cli": paths["cli"],
                "capture": paths["capture"],
                "sysroot": paths["sysroot"],
                "lean": paths["lean"],
            }
            # `Spec.lean` is Profile v2, while mock CLI emits Profile v1
            # (`UnitTheorem`) -> fails closed on Profile v2 mismatch.
            with self.assertRaisesRegex(RuntimeError, "does not match Profile v2"):
                perf_tracking.collect_zerocopy_proofs(
                    repo_root=paths["repo"],
                    tools=tools,
                    timeout=30,
                    time_bin=paths["time_bin"],
                )

            # Divergent `compilation` config across units fails closed at
            # discovery.
            bad_comp = dict(base_req["compilation"], cfg=["kani"])
            (v2_dir / "request.json").write_text(
                json.dumps(dict(v2_req, compilation=bad_comp)),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                RuntimeError, "compilation config inconsistent with 01_demo"
            ):
                perf_tracking.collect_zerocopy_proofs(
                    repo_root=paths["repo"],
                    tools=tools,
                    timeout=30,
                    time_bin=paths["time_bin"],
                )

    def test_collect_zerocopy_proofs_rejects_symlinks(self):
        with tempfile.TemporaryDirectory() as tmp:
            paths = self._build_synthetic_repo(Path(tmp))
            tools = {
                "cli": paths["cli"],
                "capture": paths["capture"],
                "sysroot": paths["sysroot"],
                "lean": paths["lean"],
                "time_bin": paths["time_bin"],
            }
            proofs_dir = paths["repo"] / "zerocopy/proofs"
            real_proofs = paths["repo"] / "real_proofs"
            proofs_dir.rename(real_proofs)
            proofs_dir.symlink_to(real_proofs)
            with self.assertRaisesRegex(
                RuntimeError, "symlink disallowed in proofs"
            ):
                perf_tracking.collect_zerocopy_proofs(
                    repo_root=paths["repo"],
                    tools=tools,
                    timeout=30,
                    time_bin=paths["time_bin"],
                )
            proofs_dir.unlink()
            real_proofs.rename(proofs_dir)

            zc_dir = paths["repo"] / "zerocopy"
            real_zc = paths["repo"] / "real_zc"
            zc_dir.rename(real_zc)
            zc_dir.symlink_to(real_zc)
            with self.assertRaisesRegex(
                RuntimeError, "symlink disallowed in proofs"
            ):
                perf_tracking.collect_zerocopy_proofs(
                    repo_root=paths["repo"],
                    tools=tools,
                    timeout=30,
                    time_bin=paths["time_bin"],
                )

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

    def test_collect_excludes_differential_oracle_by_default_and_rejects_explicit(
        self,
    ):
        # (i) Default category resolution excludes `differential_oracle`.
        default_cats = perf_tracking._parse_categories(None)
        self.assertEqual(default_cats, set(perf_tracking.COLLECTABLE_CATEGORIES))
        self.assertNotIn("differential_oracle", default_cats)
        self.assertEqual(
            perf_tracking._parse_categories(""),
            set(perf_tracking.COLLECTABLE_CATEGORIES),
        )
        with self.assertRaises(perf_tracking.ValidationError):
            perf_tracking._parse_categories(" , ")

        with tempfile.TemporaryDirectory() as tmp:
            paths = self._build_synthetic_repo(Path(tmp))
            out_default = Path(tmp) / "default-collect.json"
            rc = perf_tracking.main(
                [
                    "collect",
                    "--anneal-root",
                    str(paths["anneal"]),
                    "--repo-root",
                    str(paths["repo"]),
                    "--profile",
                    "linux-x86_64",
                    "--cli",
                    str(paths["cli"]),
                    "--capture",
                    str(paths["capture"]),
                    "--sysroot",
                    str(paths["sysroot"]),
                    "--lean",
                    str(paths["lean"]),
                    "--auditor",
                    str(paths["auditor"]),
                    "--omnibus-archive",
                    str(paths["archive"]),
                    "--verify-repeats",
                    "1",
                    "--cold-no-cache-repeats",
                    "1",
                    "--time-bin",
                    str(paths["time_bin"]),
                    "--output",
                    str(out_default),
                ]
            )
            self.assertEqual(rc, 0)
            collected = perf_tracking.load_record(out_default)
            self.assertFalse(
                any(
                    k.startswith("differential_oracle.")
                    for k in collected["metrics"]
                )
            )

            tools = {
                "cli": paths["cli"],
                "capture": paths["capture"],
                "sysroot": paths["sysroot"],
                "lean": paths["lean"],
                "auditor": paths["auditor"],
            }

            # (ii) & (iii) Both solo and mixed `differential_oracle` selections
            # fail closed immediately before any collector or tool lookup runs.
            for bad_raw, bad_set in (
                ("differential_oracle", {"differential_oracle"}),
                (
                    "verify,differential_oracle",
                    {"verify", "differential_oracle"},
                ),
            ):
                with self.subTest(selection=bad_raw):
                    with self.assertRaises(perf_tracking.ValidationError):
                        perf_tracking._parse_categories(bad_raw)
                    with (
                        mock.patch.object(
                            perf_tracking, "collect_verify_scalar"
                        ) as verify_mock,
                        mock.patch.object(
                            perf_tracking, "_discover_tools"
                        ) as discover_mock,
                    ):
                        with self.assertRaises(perf_tracking.ValidationError):
                            perf_tracking.collect_record(
                                anneal_root=paths["anneal"],
                                repo_root=paths["repo"],
                                profile="linux-x86_64",
                                categories=bad_set,
                                modules=None,
                                verify_repeats=1,
                                cold_no_cache_repeats=1,
                                tools=tools,
                                omnibus_archive=None,
                                branch_override=None,
                                timeout=30.0,
                                time_bin=paths["time_bin"],
                            )
                        verify_mock.assert_not_called()
                        with self.assertRaises(perf_tracking.ValidationError):
                            perf_tracking.main(
                                [
                                    "collect",
                                    "--anneal-root",
                                    str(paths["anneal"]),
                                    "--categories",
                                    bad_raw,
                                ]
                            )
                        discover_mock.assert_not_called()
                        verify_mock.assert_not_called()

        # (iv) `validate_record` and `describe_metric` still accept
        # `differential_oracle` telemetry records emitted by
        # `ci/check_mir_differential.py`.
        diff_rec = _make_record(
            metrics={
                "differential_oracle.litmus.compared_count": 39,
                "differential_oracle.litmus.unsound_missed_fault_count": 0,
                "differential_oracle.mutants.killed_pct": 100.0,
            }
        )
        self.assertEqual(perf_tracking.validate_record(diff_rec), diff_rec)
        self.assertEqual(
            perf_tracking.describe_metric(
                "differential_oracle.litmus.compared_count"
            )["direction"],
            "higher_is_better",
        )
        self.assertEqual(
            perf_tracking.describe_metric(
                "differential_oracle.litmus.unsound_missed_fault_count"
            )["direction"],
            "lower_is_better",
        )
        self.assertEqual(
            perf_tracking.describe_metric(
                "differential_oracle.mutants.killed_pct"
            )["unit"],
            "%",
        )
        import render_perf_dashboard

        html = render_perf_dashboard.render_html(
            render_perf_dashboard.build_dashboard_bundle(
                [
                    _make_record(
                        sha_idx=1,
                        unix_ts=100,
                        metrics={"differential_oracle.mutants.killed_pct": 100.0},
                    )
                ]
            )
        )
        self.assertIn('if (unit === "%")', html)
        self.assertIn('+ "%"', html)
