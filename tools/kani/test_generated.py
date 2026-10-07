# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import copy
import unittest
from check_generated import validate_generated


def inventory():
    return {"proof_harnesses": [{
        "pretty_name": "Example::__kani_contract_f_all",
        "attributes": {"kind": {"ProofForContract": {"target_fn": "Example::f"}},
                       "should_panic": False, "solver": None, "unwind_value": None,
                       "stubs": [], "verified_stubs": []},
        "contract": {"recursion_tracker": None},
    }], "test_harnesses": []}


class GeneratedProofTests(unittest.TestCase):
    def test_generated_proofs_execute_implementations(self):
        self.assertEqual(validate_generated(inventory()), ["Example::__kani_contract_f_all"])
        for field, value in [("stubs", [["f", "g"]]), ("verified_stubs", ["g"]),
                             ("should_panic", True), ("kind", "Proof")]:
            metadata = inventory()
            metadata["proof_harnesses"][0]["attributes"][field] = value
            with self.assertRaises(ValueError):
                validate_generated(metadata)

    def test_handwritten_callers_may_substitute(self):
        metadata = inventory()
        caller = copy.deepcopy(metadata["proof_harnesses"][0])
        caller["pretty_name"] = "caller"
        caller["attributes"]["kind"] = "Proof"
        caller["attributes"]["verified_stubs"] = ["Example::f"]
        metadata["proof_harnesses"].append(caller)
        self.assertEqual(len(validate_generated(metadata)), 1)

    def test_nested_duplicate_recursive_or_unrecognized_proofs_fail(self):
        for edit in [lambda h: h.update(pretty_name="Example::__kani_contract_f_all::{closure#0}"),
                     lambda h: h.update(pretty_name="f::{closure#0}::__kani_contract_f_all"),
                     lambda h: h["contract"].update(recursion_tracker="tracker"),
                     lambda h: h["attributes"].update(unknown_flag=True)]:
            metadata = inventory()
            edit(metadata["proof_harnesses"][0])
            with self.assertRaises(ValueError):
                validate_generated(metadata)
        metadata = inventory()
        metadata["proof_harnesses"].append(copy.deepcopy(metadata["proof_harnesses"][0]))
        with self.assertRaises(ValueError):
            validate_generated(metadata)


if __name__ == "__main__":
    unittest.main()
