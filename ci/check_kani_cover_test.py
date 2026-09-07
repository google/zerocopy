#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


CHECKER = Path(__file__).with_name("check_kani_cover.py")


class CheckKaniCoverTest(unittest.TestCase):
    def setUp(self):
        self.temporary_directory = tempfile.TemporaryDirectory()
        self.target = Path(self.temporary_directory.name)
        self.metadata_dir = self.target / "kani" / "target" / "debug" / "deps"
        self.metadata_dir.mkdir(parents=True)
        self.result_dir = self.target / "result_output_dir"
        self.result_dir.mkdir()

    def tearDown(self):
        self.temporary_directory.cleanup()

    def write_metadata(self, names, filename="fixture.kani-metadata.json"):
        metadata = {
            "crate_name": "fixture",
            "proof_harnesses": [{"pretty_name": name} for name in names],
            "test_harnesses": [],
        }
        (self.metadata_dir / filename).write_text(
            json.dumps(metadata), encoding="utf-8"
        )

    def write_result(self, name, contents):
        path = self.result_dir / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents, encoding="utf-8")
        return path

    def write_single_cover_result(self, name, status, thread=None):
        satisfied = 1 if status == "SATISFIED" else 0
        breakdown = {
            "UNDETERMINED": " (1 undetermined)",
            "UNREACHABLE": " (1 unreachable)",
        }.get(status, "")
        thread_header = f"Thread {thread}:\n" if thread is not None else ""
        return self.write_result(
            name,
            f"""{thread_header}
RESULTS:
Check 1: {name}.cover.1
\t - Status: {status}
\t - Description: "cover fixture"


SUMMARY:
 ** 0 of 0 failed

 ** {satisfied} of 1 cover properties satisfied{breakdown}


VERIFICATION:- SUCCESSFUL
Verification Time: 0.01s

""",
        )

    def run_checker(self):
        return subprocess.run(
            [sys.executable, str(CHECKER), str(self.target)],
            check=False,
            capture_output=True,
            text=True,
        )

    def test_satisfied_cover_fixture_passes(self):
        self.write_metadata(["fixture::satisfied"])
        self.write_result(
            "fixture::satisfied",
            """
RESULTS:
Check 1: fixture::satisfied.assertion.1
\t - Status: UNREACHABLE
\t - Description: "assertion failed: true"

Check 2: fixture::satisfied.cover.1
\t - Status: SATISFIED
\t - Description: "reachable cover"


SUMMARY:
 ** 0 of 1 failed (1 unreachable)

 ** 1 of 1 cover properties satisfied


VERIFICATION:- SUCCESSFUL
Verification Time: 0.01s

""",
        )

        result = self.run_checker()

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("all 1 cover properties are SATISFIED", result.stdout)

    def test_harness_without_cover_fixture_passes(self):
        self.write_metadata(["fixture::no_cover"])
        self.write_result(
            "fixture::no_cover",
            """
RESULTS:
Check 1: fixture::no_cover.assertion.1
\t - Status: SUCCESS
\t - Description: "assertion failed: true"


SUMMARY:
 ** 0 of 1 failed

VERIFICATION:- SUCCESSFUL
Verification Time: 0.01s

""",
        )

        result = self.run_checker()

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("all 0 cover properties are SATISFIED", result.stdout)

    def test_uncovered_fixture_fails(self):
        self.write_metadata(["fixture::uncovered"])
        self.write_single_cover_result("fixture::uncovered", "UNSATISFIABLE")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("is UNSATISFIABLE, not SATISFIED", result.stderr)

    def test_unreachable_cover_fixture_fails(self):
        self.write_metadata(["fixture::unreachable"])
        self.write_single_cover_result("fixture::unreachable", "UNREACHABLE")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("is UNREACHABLE, not SATISFIED", result.stderr)

    def test_undetermined_cover_fixture_fails(self):
        self.write_metadata(["fixture::undetermined"])
        self.write_single_cover_result("fixture::undetermined", "UNDETERMINED")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("is UNDETERMINED, not SATISFIED", result.stderr)

    def test_missing_result_fixture_fails(self):
        self.write_metadata(["fixture::missing"])

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("no per-harness result files", result.stderr)

    def test_malformed_summary_fixture_fails(self):
        self.write_metadata(["fixture::malformed"])
        self.write_result(
            "fixture::malformed",
            """
RESULTS:
Check 1: fixture::malformed.cover.1
\t - Status: SATISFIED
\t - Description: "reachable cover"


SUMMARY:
 ** 0 of 0 failed

 ** 1 of 2 cover properties satisfied


VERIFICATION:- SUCCESSFUL
Verification Time: 0.01s

""",
        )

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("cover summary reports 1 of 2, but parsed 1 of 1", result.stderr)

    def test_malformed_status_breakdown_fixture_fails(self):
        self.write_metadata(["fixture::malformed_breakdown"])
        self.write_result(
            "fixture::malformed_breakdown",
            """
RESULTS:
Check 1: fixture::malformed_breakdown.assertion.1
\t - Status: UNREACHABLE
\t - Description: "assertion failed: true"


SUMMARY:
 ** 0 of 1 failed (1 undetermined)

VERIFICATION:- SUCCESSFUL
Verification Time: 0.01s

""",
        )

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn(
            "summary breakdown is '1 undetermined', but parsed '1 unreachable'",
            result.stderr,
        )

    def test_cover_summary_after_footer_fixture_fails(self):
        self.write_metadata(["fixture::late_cover_summary"])
        self.write_result(
            "fixture::late_cover_summary",
            """
RESULTS:
Check 1: fixture::late_cover_summary.cover.1
\t - Status: SATISFIED
\t - Description: "reachable cover"


SUMMARY:
 ** 0 of 0 failed

VERIFICATION:- SUCCESSFUL
 ** 1 of 1 cover properties satisfied
Verification Time: 0.01s

""",
        )

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("malformed Kani summary/footer ordering", result.stderr)

    def test_nonempty_data_after_footer_fixture_fails(self):
        self.write_metadata(["fixture::trailing"])
        path = self.write_single_cover_result("fixture::trailing", "SATISFIED")
        with path.open("a", encoding="utf-8") as result_file:
            result_file.write("MALFORMED TRAILING RECORD\n")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("nonempty data follows", result.stderr)

    def test_malformed_time_footer_fixture_fails(self):
        self.write_metadata(["fixture::bad_time"])
        path = self.write_single_cover_result("fixture::bad_time", "SATISFIED")
        contents = path.read_text(encoding="utf-8")
        path.write_text(
            contents.replace("Verification Time: 0.01s", "Verification Time: +s"),
            encoding="utf-8",
        )

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("exactly one verification-time footer; found 0", result.stderr)

    def test_impossible_rendered_status_fixture_fails(self):
        self.write_metadata(["fixture::covered_status"])
        self.write_result(
            "fixture::covered_status",
            """
RESULTS:
Check 1: fixture::covered_status.assertion.1
\t - Status: COVERED
\t - Description: "impossible regular result status"


SUMMARY:
 ** 0 of 1 failed

VERIFICATION:- SUCCESSFUL
Verification Time: 0.01s

""",
        )

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("unknown Kani status 'COVERED'", result.stderr)

    def test_thread_header_fixture_passes(self):
        self.write_metadata(["fixture::thread"])
        self.write_single_cover_result("fixture::thread", "SATISFIED", thread=7)

        result = self.run_checker()

        self.assertEqual(result.returncode, 0, result.stderr)

    def test_stale_result_inventory_fixture_fails(self):
        self.write_metadata(["fixture::expected"])
        self.write_single_cover_result("fixture::stale", "SATISFIED")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("missing: 'fixture::expected'", result.stderr)
        self.assertIn("unexpected: 'fixture::stale'", result.stderr)

    def test_multiple_populated_metadata_inventories_fail(self):
        self.write_metadata(["fixture::first"], "first.kani-metadata.json")
        self.write_metadata(["fixture::second"], "second.kani-metadata.json")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("exactly one metadata inventory; found 2", result.stderr)

    def test_second_empty_metadata_inventory_fails(self):
        self.write_metadata(["fixture::selected"], "selected.kani-metadata.json")
        self.write_metadata([], "stale-empty.kani-metadata.json")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("exactly one metadata inventory; found 2", result.stderr)


if __name__ == "__main__":
    unittest.main()
