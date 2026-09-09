#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import json
import os
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

    def metadata(self, names):
        harnesses = []
        for item in names:
            name, should_panic = item if isinstance(item, tuple) else (item, False)
            harnesses.append(
                {
                    "pretty_name": name,
                    "crate_name": "zerocopy",
                    "attributes": {"should_panic": should_panic},
                }
            )
        return {
            "crate_name": "zerocopy",
            "proof_harnesses": harnesses,
            "unsupported_features": [],
            "test_harnesses": [],
            "contracted_functions": [],
            "autoharness_md": None,
        }

    def write_metadata(self, names, filename="fixture.kani-metadata.json"):
        (self.metadata_dir / filename).write_text(
            json.dumps(self.metadata(names)), encoding="utf-8"
        )

    def write_result(self, name, contents):
        path = self.result_dir / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents, encoding="utf-8")
        return path

    def write_single_cover_result(self, name, status, thread=None, property_name=None):
        satisfied = 1 if status == "SATISFIED" else 0
        breakdown = {
            "UNDETERMINED": " (1 undetermined)",
            "UNREACHABLE": " (1 unreachable)",
        }.get(status, "")
        thread_header = f"Thread {thread}:\n" if thread is not None else ""
        property_name = property_name or f"{name}.cover.1"
        return self.write_result(
            name,
            f"""{thread_header}
RESULTS:
Check 1: {property_name}
\t - Status: {status}
\t - Description: "cover fixture"


SUMMARY:
 ** 0 of 0 failed

 ** {satisfied} of 1 cover properties satisfied{breakdown}


VERIFICATION:- SUCCESSFUL
Verification Time: 0.01s

""",
        )

    def write_expected_panic_result(
        self, name, property_class="assertion", include_failure_location=True
    ):
        failure_location = (
            ' File: "src/lib.rs", line 7, in fixture::panic\n'
            if include_failure_location
            else ""
        )
        return self.write_result(
            name,
            f"""
RESULTS:
Check 1: {name}.{property_class}.1
\t - Status: FAILURE
\t - Description: "expected panic"

Check 2: {name}.cover.1
\t - Status: SATISFIED
\t - Description: "panic input is reachable"


SUMMARY:
 ** 1 of 1 failed

 ** 1 of 1 cover properties satisfied

Failed Checks: expected panic
{failure_location}
VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)
Verification Time: 0.01s

""",
        )

    def write_raw_metadata(self, contents, filename="fixture.kani-metadata.json"):
        (self.metadata_dir / filename).write_text(contents, encoding="utf-8")

    def run_checker(self, target=None):
        return subprocess.run(
            [sys.executable, str(CHECKER), str(target or self.target)],
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

    def test_harness_without_cover_passes_when_another_harness_has_cover(self):
        self.write_metadata(["fixture::no_cover", "fixture::covered"])
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
        self.write_single_cover_result("fixture::covered", "SATISFIED")

        result = self.run_checker()

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("all 1 cover properties are SATISFIED", result.stdout)

    def test_all_harnesses_without_cover_fail(self):
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

        self.assertEqual(result.returncode, 1)
        self.assertIn("contains no cover properties", result.stderr)

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
        self.assertIn("canonical cover-property summary", result.stderr)

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
        self.assertIn("canonical normal-property summary", result.stderr)

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
        self.assertIn("canonical cover-property summary", result.stderr)

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
        self.assertIn("canonical verification-time footer", result.stderr)

    def test_crlf_and_bare_cr_line_endings_fail(self):
        self.write_metadata(["fixture::bad_line_endings"])
        for line_ending in (b"\r\n", b"\r"):
            with self.subTest(line_ending=line_ending):
                path = self.write_single_cover_result(
                    "fixture::bad_line_endings", "SATISFIED"
                )
                path.write_bytes(path.read_bytes().replace(b"\n", line_ending))

                result = self.run_checker()

                self.assertEqual(result.returncode, 1)
                self.assertIn("non-Kani control character", result.stderr)

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

    def test_expected_panic_assertion_failure_passes(self):
        self.write_metadata([("fixture::panic", True)])
        self.write_expected_panic_result("fixture::panic")

        result = self.run_checker()

        self.assertEqual(result.returncode, 0, result.stderr)

    def test_expected_panic_without_failure_location_passes(self):
        self.write_metadata([("fixture::panic", True)])
        self.write_expected_panic_result(
            "fixture::panic", include_failure_location=False
        )

        result = self.run_checker()

        self.assertEqual(result.returncode, 0, result.stderr)

    def test_expected_panic_without_cover_passes_with_covered_peer(self):
        self.write_metadata(
            [("fixture::panic_no_cover", True), "fixture::covered_peer"]
        )
        self.write_result(
            "fixture::panic_no_cover",
            """
RESULTS:
Check 1: fixture::panic_no_cover.assertion.1
\t - Status: FAILURE
\t - Description: "expected panic"


SUMMARY:
 ** 1 of 1 failed
Failed Checks: expected panic

VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)
Verification Time: 0.01s

""",
        )
        self.write_single_cover_result("fixture::covered_peer", "SATISFIED")

        result = self.run_checker()

        self.assertEqual(result.returncode, 0, result.stderr)

    def test_ordinary_success_banner_with_failure_fails(self):
        self.write_metadata(["fixture::ordinary"])
        path = self.write_expected_panic_result("fixture::ordinary")
        contents = path.read_text(encoding="utf-8").replace(
            "VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)",
            "VERIFICATION:- SUCCESSFUL",
        )
        path.write_text(contents, encoding="utf-8")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("ordinary successful verification contains failed", result.stderr)

    def test_expected_panic_nonassertion_failure_fails(self):
        self.write_metadata([("fixture::panic", True)])
        self.write_expected_panic_result(
            "fixture::panic", property_class="array_bounds"
        )

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("contains non-assertion failure", result.stderr)

    def test_expected_panic_without_failure_fails(self):
        self.write_metadata([("fixture::panic", True)])
        path = self.write_single_cover_result("fixture::panic", "SATISFIED")
        contents = path.read_text(encoding="utf-8").replace(
            "VERIFICATION:- SUCCESSFUL",
            "VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)",
        )
        path.write_text(contents, encoding="utf-8")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("contains no failed assertion", result.stderr)

    def test_multiline_description_and_location_pass(self):
        self.write_metadata(["fixture::multiline"])
        self.write_result(
            "fixture::multiline",
            """
RESULTS:
Check 1: module.with.dot.cover.4294967295
\t - Status: SATISFIED
\t - Description: "first line
middle line
last line"
\t - Location: src/lib.rs:7:9 in function fixture::multiline


SUMMARY:
 ** 0 of 0 failed

 ** 1 of 1 cover properties satisfied


VERIFICATION:- SUCCESSFUL
Verification Time: 1s

""",
        )

        result = self.run_checker()

        self.assertEqual(result.returncode, 0, result.stderr)

    def test_cover_without_function_name_passes(self):
        self.write_metadata(["fixture::bare_cover"])
        self.write_single_cover_result(
            "fixture::bare_cover", "SATISFIED", property_name="cover.0"
        )

        result = self.run_checker()

        self.assertEqual(result.returncode, 0, result.stderr)

    def test_malformed_property_names_fail(self):
        cases = (
            ("fixture::bad.cover.1 ", "whitespace/control"),
            ("fixture::bad.cover.01", "noncanonical Kani property id"),
            ("fixture::bad.cover.4294967296", "exceeds 4294967295"),
            ("fixture::bad.Cover.1", "malformed Kani property class"),
            ("fixture::bad.cover.1.extra", "malformed Kani property class"),
        )
        self.write_metadata(["fixture::bad"])
        for property_name, error in cases:
            with self.subTest(property_name=property_name):
                path = self.write_single_cover_result("fixture::bad", "SATISFIED")
                contents = path.read_text(encoding="utf-8").replace(
                    "fixture::bad.cover.1", property_name
                )
                path.write_text(contents, encoding="utf-8")

                result = self.run_checker()

                self.assertEqual(result.returncode, 1)
                self.assertIn(error, result.stderr)

    def test_classes_outside_audited_corpus_fail(self):
        name = "fixture::unknown_class"
        self.write_metadata([name])
        for property_class in (
            "not_a_kani_class",
            "NaN",
            "finite_check",
            "recursion",
        ):
            with self.subTest(property_class=property_class):
                self.write_result(
                    name,
                    f"""
RESULTS:
Check 1: {name}.{property_class}.1
\t - Status: SUCCESS
\t - Description: "fabricated ordinary property"

Check 2: {name}.cover.1
\t - Status: SATISFIED
\t - Description: "authentic cover class keeps the global obligation"


SUMMARY:
 ** 0 of 1 failed

 ** 1 of 1 cover properties satisfied


VERIFICATION:- SUCCESSFUL
Verification Time: 0.01s

""",
                )

                result = self.run_checker()

                self.assertEqual(result.returncode, 1)
                self.assertIn("outside the audited zerocopy vocabulary", result.stderr)

    def test_duplicate_property_name_fails(self):
        name = "fixture::duplicate_property"
        self.write_metadata([name])
        self.write_result(
            name,
            f"""
RESULTS:
Check 1: {name}.cover.1
\t - Status: SATISFIED
\t - Description: "first copy"

Check 2: {name}.cover.1
\t - Status: SATISFIED
\t - Description: "second copy"


SUMMARY:
 ** 0 of 0 failed

 ** 2 of 2 cover properties satisfied


VERIFICATION:- SUCCESSFUL
Verification Time: 0.01s

""",
        )

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("duplicate Kani property name", result.stderr)

    def test_trailing_space_cannot_reclassify_cover_as_noncover(self):
        self.write_metadata(["fixture::bad"])
        path = self.write_single_cover_result("fixture::bad", "UNREACHABLE")
        contents = path.read_text(encoding="utf-8").replace(
            "fixture::bad.cover.1", "fixture::bad.cover.1 "
        )
        path.write_text(contents, encoding="utf-8")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("whitespace/control", result.stderr)

    def test_malformed_check_and_thread_numbers_fail(self):
        cases = (("Check 1:", "Check 01:"), ("Thread 7:", "Thread 07:"))
        for old, new in cases:
            with self.subTest(new=new):
                self.write_metadata(["fixture::number"])
                path = self.write_single_cover_result(
                    "fixture::number", "SATISFIED", thread=7
                )
                contents = path.read_text(encoding="utf-8").replace(old, new)
                path.write_text(contents, encoding="utf-8")

                result = self.run_checker()

                self.assertEqual(result.returncode, 1)
                self.assertIn("malformed Kani", result.stderr)

    def test_noncanonical_summary_counts_fail(self):
        self.write_metadata(["fixture::summary"])
        path = self.write_single_cover_result("fixture::summary", "SATISFIED")
        contents = path.read_text(encoding="utf-8").replace(
            " ** 0 of 0 failed", " ** 00 of 0 failed"
        )
        path.write_text(contents, encoding="utf-8")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("canonical normal-property summary", result.stderr)

    def test_noncanonical_time_values_fail(self):
        self.write_metadata(["fixture::time"])
        for time_value in ("00.01", "0.010", "1e-2", "+0.01"):
            with self.subTest(time_value=time_value):
                path = self.write_single_cover_result("fixture::time", "SATISFIED")
                contents = path.read_text(encoding="utf-8").replace(
                    "Verification Time: 0.01s",
                    f"Verification Time: {time_value}s",
                )
                path.write_text(contents, encoding="utf-8")

                result = self.run_checker()

                self.assertEqual(result.returncode, 1)
                self.assertIn("canonical verification-time footer", result.stderr)

    def test_unterminated_description_fails(self):
        self.write_metadata(["fixture::description"])
        path = self.write_single_cover_result("fixture::description", "SATISFIED")
        contents = path.read_text(encoding="utf-8").replace(
            'Description: "cover fixture"', 'Description: "cover fixture'
        )
        path.write_text(contents, encoding="utf-8")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("control record in unterminated description", result.stderr)

    def test_control_record_inside_multiline_description_fails(self):
        self.write_metadata(["fixture::description"])
        path = self.write_single_cover_result("fixture::description", "SATISFIED")
        contents = path.read_text(encoding="utf-8").replace(
            'Description: "cover fixture"',
            'Description: "first line\nCheck 2: fake.cover.1\nlast line"',
        )
        path.write_text(contents, encoding="utf-8")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("control record", result.stderr)

    def test_reordered_or_duplicate_check_fields_fail(self):
        cases = (
            (
                '\t - Status: SATISFIED\n\t - Description: "cover fixture"',
                '\t - Description: "cover fixture"\n\t - Status: SATISFIED',
            ),
            (
                "\t - Status: SATISFIED",
                "\t - Status: SATISFIED\n\t - Status: SATISFIED",
            ),
            (
                '\t - Description: "cover fixture"',
                '\t - Description: "cover fixture"\n' '\t - Description: "duplicate"',
            ),
        )
        self.write_metadata(["fixture::fields"])
        for old, new in cases:
            with self.subTest(new=new):
                path = self.write_single_cover_result("fixture::fields", "SATISFIED")
                contents = path.read_text(encoding="utf-8").replace(old, new)
                path.write_text(contents, encoding="utf-8")

                result = self.run_checker()

                self.assertEqual(result.returncode, 1)

    def test_malformed_optional_locations_fail(self):
        self.write_metadata(["fixture::location"])
        path = self.write_single_cover_result("fixture::location", "SATISFIED")
        contents = path.read_text(encoding="utf-8").replace(
            '\t - Description: "cover fixture"',
            '\t - Description: "cover fixture"\n\t - Location: ',
        )
        path.write_text(contents, encoding="utf-8")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("malformed location", result.stderr)

    def test_noncanonical_failure_detail_line_number_fails(self):
        self.write_metadata([("fixture::panic", True)])
        path = self.write_expected_panic_result("fixture::panic")
        contents = path.read_text(encoding="utf-8").replace("line 7", "line 07")
        path.write_text(contents, encoding="utf-8")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("malformed failed-check location", result.stderr)

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

    def test_metadata_root_must_match_pinned_schema_and_crate(self):
        self.write_single_cover_result("fixture::covered", "SATISFIED")
        cases = []

        missing = self.metadata(["fixture::covered"])
        del missing["contracted_functions"]
        cases.append(("missing field", missing, "metadata root does not match"))

        unexpected = self.metadata(["fixture::covered"])
        unexpected["future_field"] = []
        cases.append(("unexpected field", unexpected, "metadata root does not match"))

        wrong_crate = self.metadata(["fixture::covered"])
        wrong_crate["crate_name"] = "different_crate"
        cases.append(("wrong crate", wrong_crate, "expected crate_name 'zerocopy'"))

        wrong_unsupported = self.metadata(["fixture::covered"])
        wrong_unsupported["unsupported_features"] = {}
        cases.append(("unsupported type", wrong_unsupported, "is not an array"))

        wrong_contracted = self.metadata(["fixture::covered"])
        wrong_contracted["contracted_functions"] = None
        cases.append(("contracts type", wrong_contracted, "is not an array"))

        autoharness = self.metadata(["fixture::covered"])
        autoharness["autoharness_md"] = {"chosen": [], "skipped": {}}
        cases.append(("autoharness", autoharness, "forbids autoharness metadata"))

        for description, metadata, error in cases:
            with self.subTest(description=description):
                self.write_raw_metadata(json.dumps(metadata))

                result = self.run_checker()

                self.assertEqual(result.returncode, 1)
                self.assertIn(error, result.stderr)

    def test_proof_and_test_harness_protocol_is_separate(self):
        name = "fixture::covered"
        proof = self.metadata([name])["proof_harnesses"][0]
        self.write_single_cover_result(name, "SATISFIED")

        test_only = self.metadata([])
        test_only["test_harnesses"] = [proof]
        self.write_raw_metadata(json.dumps(test_only))
        result = self.run_checker()
        self.assertEqual(result.returncode, 1)
        self.assertIn("metadata contains no proof harnesses", result.stderr)

        mixed = self.metadata([name])
        mixed["test_harnesses"] = [proof]
        self.write_raw_metadata(json.dumps(mixed))
        result = self.run_checker()
        self.assertEqual(result.returncode, 1)
        self.assertIn("canonical proof protocol forbids test harnesses", result.stderr)

    def test_nested_harness_crate_must_match_root(self):
        metadata = self.metadata(["fixture::covered"])
        metadata["proof_harnesses"][0]["crate_name"] = "different_crate"
        self.write_raw_metadata(json.dumps(metadata))
        self.write_single_cover_result("fixture::covered", "SATISFIED")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("proof_harnesses[0].crate_name must be 'zerocopy'", result.stderr)

    def test_control_characters_in_harness_names_fail(self):
        for control in ("\n", "\t", "\x7f"):
            with self.subTest(control=repr(control)):
                name = f"fixture::{control}bad"
                self.write_metadata([name])
                self.write_single_cover_result(
                    name, "SATISFIED", property_name="cover.0"
                )

                result = self.run_checker()

                self.assertEqual(result.returncode, 1)
                self.assertIn("pretty_name contains a control character", result.stderr)

    def test_duplicate_root_metadata_key_fails(self):
        self.write_raw_metadata("""{
  "crate_name": "fixture",
  "proof_harnesses": [],
  "proof_harnesses": [
    {"pretty_name": "fixture::duplicate", "attributes": {"should_panic": false}}
  ],
  "test_harnesses": []
}""")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("duplicate JSON object key 'proof_harnesses'", result.stderr)

    def test_duplicate_nested_metadata_key_fails(self):
        self.write_raw_metadata("""{
  "crate_name": "fixture",
  "proof_harnesses": [
    {
      "pretty_name": "fixture::first",
      "pretty_name": "fixture::second",
      "attributes": {"should_panic": false}
    }
  ],
  "test_harnesses": []
}""")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("duplicate JSON object key 'pretty_name'", result.stderr)

    def test_nonfinite_json_constants_fail(self):
        for constant in ("NaN", "Infinity", "-Infinity"):
            with self.subTest(constant=constant):
                self.write_raw_metadata(
                    "{"
                    '"crate_name":"fixture",'
                    '"proof_harnesses":[],"test_harnesses":[],'
                    f'"unexpected":{constant}'
                    "}"
                )

                result = self.run_checker()

                self.assertEqual(result.returncode, 1)
                self.assertIn("non-finite JSON constant", result.stderr)

    def test_metadata_should_panic_must_be_boolean(self):
        self.write_raw_metadata("""{
  "crate_name": "zerocopy",
  "proof_harnesses": [
    {
      "pretty_name": "fixture::bad",
      "crate_name": "zerocopy",
      "attributes": {"should_panic": 1}
    }
  ],
  "unsupported_features": [],
  "test_harnesses": [],
  "contracted_functions": [],
  "autoharness_md": null
}""")

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("should_panic is not a boolean", result.stderr)

    def test_noncanonical_metadata_result_path_fails(self):
        self.write_metadata(["fixture//bad"])

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("unsafe harness result path", result.stderr)

    def test_symlink_metadata_leaf_fails(self):
        with tempfile.TemporaryDirectory() as external_directory:
            metadata = {
                "crate_name": "fixture",
                "proof_harnesses": [],
                "test_harnesses": [],
            }
            external_path = Path(external_directory) / "outside.kani-metadata.json"
            external_path.write_text(json.dumps(metadata), encoding="utf-8")
            (self.metadata_dir / "fixture.kani-metadata.json").symlink_to(external_path)

            result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("symlink is forbidden in Kani metadata tree", result.stderr)

    def test_symlink_result_root_fails(self):
        self.write_metadata(["fixture::covered"])
        self.result_dir.rmdir()
        with tempfile.TemporaryDirectory() as external_directory:
            self.result_dir.symlink_to(external_directory, target_is_directory=True)

            result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("Kani result root is not a real directory", result.stderr)

    def test_symlink_result_leaf_fails(self):
        self.write_metadata(["fixture::covered"])
        with tempfile.TemporaryDirectory() as external_directory:
            external_path = Path(external_directory) / "outside-result"
            external_path.write_text("not trusted\n", encoding="utf-8")
            (self.result_dir / "fixture::covered").symlink_to(external_path)

            result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("symlink is forbidden in Kani result tree", result.stderr)

    def test_nonregular_result_leaf_fails(self):
        self.write_metadata(["fixture::covered"])
        fifo = self.result_dir / "fixture::covered"
        os.mkfifo(fifo)

        result = self.run_checker()

        self.assertEqual(result.returncode, 1)
        self.assertIn("non-regular path in Kani result tree", result.stderr)


if __name__ == "__main__":
    unittest.main()
