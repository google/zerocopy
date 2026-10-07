# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import copy
import subprocess
import unittest

import run


BYTE, ELEMENT = run.APPROVED_CONTRACTS
BYTE_PROOF = "layout::TrailingSliceLayout::" + run.APPROVED_CONTRACTS[BYTE]
ELEMENT_PROOF = "layout::TrailingSliceLayout::" + run.APPROVED_CONTRACTS[ELEMENT]
CALLER = "layout::proofs::caller"


def harness(name, dependencies=(), target=None):
    return {"pretty_name": name, "original_file": "src/layout.rs",
            "original_start_line": 1, "original_end_line": 3, "attributes": {
        "kind": {"ProofForContract": {"target_fn": target}} if target else "Proof",
        "should_panic": False, "solver": None, "unwind_value": None,
        "stubs": [], "verified_stubs": list(dependencies),
    }}


def inventory():
    foundation = harness(run.FOUNDATION)
    foundation["attributes"]["unwind_value"] = 65
    foundation["original_file"] = "src/util/mod.rs"
    foundation["original_end_line"] = len(run.FOUNDATION_BODY.splitlines())
    return {"crate_name": "zerocopy", "unsupported_features": [],
            "test_harnesses": [], "proof_harnesses": [
                foundation, harness(BYTE_PROOF, target=BYTE),
                harness(ELEMENT_PROOF, target=ELEMENT),
                harness(CALLER, [ELEMENT])],}


def plan(metadata, selected=(), altered_source=None):
    def read_source(filename):
        if altered_source is not None:
            return altered_source
        return (run.FOUNDATION_BODY if filename == "src/util/mod.rs"
                else "zerocopy_kani_macros::contract(\n target = " + BYTE + ", target = " + ELEMENT + "\n)")
    return run.verification_plan(metadata, selected, read_source)


class FailClosedTests(unittest.TestCase):
    def test_macro_token_spacing_is_normalized(self):
        metadata = inventory()
        for h in metadata["proof_harnesses"]:
            kind = h["attributes"]["kind"]
            if isinstance(kind, dict):
                kind["ProofForContract"]["target_fn"] = (
                    kind["ProofForContract"]["target_fn"].replace("::", " :: "))
        plan(metadata)

    def test_filtered_caller_automatically_verifies_its_contract(self):
        self.assertEqual(plan(inventory(), [CALLER]),
                         ([[run.FOUNDATION, ELEMENT_PROOF]], [CALLER]))

    def test_prerequisite_failure_never_runs_consumer(self):
        calls = []

        def failing_process(args):
            calls.append(args)
            raise subprocess.CalledProcessError(1, args)

        with self.assertRaises(subprocess.CalledProcessError):
            run.verify(["kani"], [[BYTE_PROOF], [ELEMENT_PROOF]], [CALLER],
                       failing_process)
        self.assertEqual(calls, [["kani", "--exact", "--harness", BYTE_PROOF]])

    def test_narrowed_or_rewritten_prerequisite_body_is_rejected(self):
        altered = run.FOUNDATION_BODY.replace("let value:",
                                               "kani::assume(false); let value:")
        with self.assertRaises(ValueError):
            plan(inventory(), altered_source=altered)
        metadata = inventory()
        metadata["proof_harnesses"][1]["original_file"] = "other.rs"
        with self.assertRaises(ValueError):
            plan(metadata)

    def test_missing_proof_fails_before_execution(self):
        metadata = inventory()
        metadata["proof_harnesses"].pop(2)
        with self.assertRaises(ValueError):
            plan(metadata, [CALLER])

    def test_expected_panic_cannot_verify_contract(self):
        metadata = inventory()
        metadata["proof_harnesses"][1]["attributes"]["should_panic"] = True
        with self.assertRaises(ValueError):
            plan(metadata)

    def test_substitutions_in_generated_proofs_are_rejected(self):
        metadata = inventory()
        metadata["proof_harnesses"][1]["attributes"]["verified_stubs"] = [ELEMENT]
        with self.assertRaises(ValueError):
            plan(metadata)

    def test_unchecked_and_unreviewed_stubs_are_rejected(self):
        for field, value in [("stubs", ["replacement"]),
                             ("verified_stubs", ["unreviewed"]),
                             ("unknown_attribute", True)]:
            metadata = inventory()
            metadata["proof_harnesses"][-1]["attributes"][field] = value
            with self.assertRaises(ValueError):
                plan(metadata)

    def test_missing_or_altered_foundation_fails(self):
        metadata = inventory()
        metadata["proof_harnesses"][0]["attributes"]["unwind_value"] = 0
        with self.assertRaises(ValueError):
            plan(metadata)
        metadata["proof_harnesses"].pop(0)
        with self.assertRaises(KeyError):
            plan(metadata)

    def test_nested_and_ambiguous_generated_proofs_are_rejected(self):
        metadata = inventory()
        copied = copy.deepcopy(metadata["proof_harnesses"][1])
        copied["pretty_name"] = "layout::{closure#0}::" + run.APPROVED_CONTRACTS[BYTE]
        metadata["proof_harnesses"].append(copied)
        with self.assertRaises(ValueError):
            plan(metadata)
        copied["pretty_name"] = "other::" + run.APPROVED_CONTRACTS[BYTE]
        with self.assertRaises(ValueError):
            plan(metadata)

    def test_manifest_cannot_inject_unsafe_options(self):
        overrides = {"flags": {"no-assert-contracts": True}}
        for metadata in [{"kani": overrides},
                         {"package": {"metadata": {"kani": overrides}}},
                         {"workspace": {"metadata": {"kani": overrides}}}]:
            with self.assertRaises(ValueError):
                run.validate_manifest(metadata)
        run.validate_manifest({"package": {"name": "zerocopy"}})

    def test_unknown_filter_and_unsupported_features_fail(self):
        with self.assertRaises(ValueError):
            plan(inventory(), ["nonexistent"])
        metadata = inventory()
        metadata["unsupported_features"] = ["unsupported"]
        with self.assertRaises(ValueError):
            plan(metadata)


if __name__ == "__main__":
    unittest.main()
