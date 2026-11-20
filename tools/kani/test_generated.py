# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import copy
import unittest
from check_generated import validate_checking_graph, validate_dependencies, validate_generated, ignored_proofs, select_harnesses


def inventory():
    return {"proof_harnesses": [{
        "pretty_name": "Example::__kani_contract_f_all",
        "attributes": {"kind": {"ProofForContract": {"target_fn": "Example::f"}},
                       "should_panic": False, "solver": None, "unwind_value": None,
                       "stubs": [], "verified_stubs": []},
        "contract": {"recursion_tracker": None},
    }], "test_harnesses": [], "contracted_functions": [{
        "function": "Example::f", "file": "src/lib.rs",
        "harnesses": ["Example::__kani_contract_f_all"],
    }]}


class GeneratedProofTests(unittest.TestCase):
    def test_generated_proofs_execute_implementations(self):
        self.assertEqual(validate_generated(inventory()), ["Example::__kani_contract_f_all"])
        for field, value in [("stubs", [["f", "g"]]),
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

    def test_every_contract_must_have_its_own_discovered_proof(self):
        metadata = inventory()
        metadata["contracted_functions"].append({
            "function": "outer::f", "file": "src/lib.rs", "harnesses": [],
        })
        with self.assertRaisesRegex(ValueError, "no discovered"):
            validate_generated(metadata)
        for mapping in ([], ["missing"], ["Example::__kani_contract_f_all"] * 2):
            metadata = inventory()
            metadata["contracted_functions"][0]["harnesses"] = mapping
            with self.assertRaises(ValueError):
                validate_generated(metadata)
        metadata = inventory()
        metadata["contracted_functions"] = []
        with self.assertRaisesRegex(ValueError, "not linked"):
            validate_generated(metadata)
        metadata = inventory()
        metadata["contracted_functions"][0]["unknown"] = True
        with self.assertRaisesRegex(ValueError, "schema"):
            validate_generated(metadata)

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


def goto_function(name, mode=None):
    instructions = []
    if mode is not None:
        u8 = {"id": "unsignedbv", "namedSub": {"width": {"id": "8"}}}
        marker = {"id": "symbol", "namedSub": {
            "identifier": {"id": name + "::1::kani_contract_mode"}, "type": u8,
        }}
        instructions = [
            {"instructionId": "DECL", "operands": [marker]},
            {"instructionId": "ASSIGN", "operands": [marker, {"id": "constant", "namedSub": {
                "type": u8, "value": {"id": str(mode)},
            }}]},
        ]
    return {"name": name, "isBodyAvailable": True, "instructions": instructions}


class CheckingGraphTests(unittest.TestCase):
    def graph_inventory(self):
        harness = {"mangled_name": "proof", "pretty_name": "__kani_contract_f_all",
                   "contract": {"contracted_function_name": "wrapper"}}
        functions = [goto_function("proof"), goto_function("f_u8", 2),
                     goto_function("wrapper"), goto_function("dependency", 4),
                     goto_function("helper"), goto_function("f_u16", 2)]
        functions[0]["instructions"].append({"instructionId": "FUNCTION_CALL", "operands": [
            {}, {"id": "symbol", "namedSub": {"identifier": {"id": "f_u8"}}}, {},
        ]})
        graph = "proof -> f_u8\nf_u8 -> wrapper\nwrapper -> dependency\n"
        return functions, graph, harness

    def test_assert_dependencies_and_unreached_check_instances_are_allowed(self):
        functions, graph, harness = self.graph_inventory()
        validate_checking_graph(functions, graph, harness)
        functions[3] = goto_function("dependency", 0)
        validate_checking_graph(functions, graph, harness)

    def test_direct_indirect_and_cross_instance_reentry_are_rejected(self):
        for calls in ["wrapper -> f_u8\n", "wrapper -> helper\nhelper -> f_u8\n",
                      "wrapper -> f_u16\n"]:
            functions, graph, harness = self.graph_inventory()
            with self.assertRaisesRegex(ValueError, "nested contract checking"):
                validate_checking_graph(functions, graph + calls, harness)

    def test_argument_generation_and_repeated_direct_calls_are_rejected(self):
        functions, graph, harness = self.graph_inventory()
        with self.assertRaisesRegex(ValueError, "argument generation"):
            validate_checking_graph(functions, graph + "proof -> helper\nhelper -> f_u8\n", harness)
        functions[0]["instructions"].append(copy.deepcopy(functions[0]["instructions"][0]))
        with self.assertRaisesRegex(ValueError, "exactly once"):
            validate_checking_graph(functions, graph, harness)

    def test_missing_ambiguous_and_wrong_wrapper_models_are_rejected(self):
        functions, graph, harness = self.graph_inventory()
        for changed in [graph.replace("proof -> f_u8\n", ""), graph + "proof -> f_u16\n",
                        graph.replace("f_u8 -> wrapper\n", "")]:
            with self.assertRaises(ValueError):
                validate_checking_graph(functions, changed, harness)
        functions[1]["instructions"].pop()
        with self.assertRaisesRegex(ValueError, "missing Kani contract mode assignment"):
            validate_checking_graph(functions, graph, harness)

    def test_unrecognized_or_narrowing_modes_and_graph_schema_are_rejected(self):
        for mode in [1, 3, 5]:
            functions, graph, harness = self.graph_inventory()
            functions[1] = goto_function("f_u8", mode)
            with self.assertRaises(ValueError):
                validate_checking_graph(functions, graph, harness)
        functions, graph, harness = self.graph_inventory()
        for malformed in [graph + "unexpected status\n", graph + "helper -> missing\n"]:
            with self.assertRaises(ValueError):
                validate_checking_graph(functions, malformed, harness)
        functions[1]["instructions"].append(copy.deepcopy(functions[1]["instructions"][1]))
        with self.assertRaisesRegex(ValueError, "assignments"):
            validate_checking_graph(functions, graph, harness)


class DependencyGraphTests(unittest.TestCase):
    def test_chain_and_diamond_are_allowed(self):
        models = [(None, "top", {"left", "right"}), (None, "left", {"leaf"}),
                  (None, "right", {"leaf"}), (None, "leaf", set())]
        self.assertEqual(set(validate_dependencies(models)), {"top", "left", "right", "leaf"})

    def test_missing_or_unproved_concrete_instance_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "no generated full-domain proof"):
            validate_dependencies([(None, "f_u8", {"g_u16"}), (None, "g_u8", set())])

    def test_self_mutual_and_transitive_cycles_are_rejected(self):
        for models in [[(None, "f", {"f"})],
                       [(None, "f", {"g"}), (None, "g", {"f"})],
                       [(None, "f", {"g"}), (None, "g", {"h"}), (None, "h", {"f"})]]:
            with self.assertRaisesRegex(ValueError, "cyclic"):
                validate_dependencies(models)

    def test_duplicate_dispatcher_providers_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "duplicate proof"):
            validate_dependencies([(None, "f", set()), (None, "f", set())])

    def test_replacements_require_opt_in_and_are_bound_by_compiled_symbols(self):
        functions, graph, harness = CheckingGraphTests().graph_inventory()
        functions[3] = goto_function("dependency", 3)
        with self.assertRaises(ValueError):
            validate_checking_graph(functions, graph, harness)
        checking, used = validate_checking_graph(functions, graph, harness,
                                                allow_replacements=True)
        self.assertEqual(checking, "f_u8")
        self.assertEqual(used, {"dependency"})


class IgnoreSelectionTests(unittest.TestCase):
    def inventory(self):
        metadata = inventory()
        base = metadata["proof_harnesses"][0]
        ignored = copy.deepcopy(base)
        ignored["pretty_name"] = "Example::__kani_contract_slow_all__zerocopy_ignore_" + "slow 🐢".encode().hex()
        ignored["attributes"]["kind"] = {"ProofForContract": {"target_fn": "Example::slow"}}
        metadata["proof_harnesses"].append(ignored)
        metadata["contracted_functions"].append({
            "function": "Example::slow", "file": "src/lib.rs",
            "harnesses": [ignored["pretty_name"]],
        })
        metadata["proof_harnesses"].append({
            "pretty_name": "handwritten", "attributes": {"verified_stubs": []},
        })
        names = [h["pretty_name"] for h in metadata["proof_harnesses"]]
        dependencies = {name: set() for name in names}
        return metadata, dependencies, names

    def test_default_preserves_handwritten_and_reports_reason(self):
        metadata, dependencies, names = self.inventory()
        selected, ignored = select_harnesses(metadata, dependencies)
        self.assertEqual(selected, [names[0], names[2]])
        self.assertEqual(ignored, {names[1]: "slow 🐢"})
        self.assertEqual(len(validate_generated(metadata)), 2)

    def test_include_and_ignored_close_providers(self):
        metadata, dependencies, names = self.inventory()
        dependencies[names[1]] = {names[0]}
        self.assertEqual(select_harnesses(metadata, dependencies, include_ignored=True)[0], names)
        self.assertEqual(select_harnesses(metadata, dependencies, only_ignored=True)[0], names[:2])
        self.assertEqual(select_harnesses(metadata, dependencies, harnesses=[names[1]])[0], names[:2])

    def test_enabled_roots_cannot_assume_ignored_provider_even_indirectly(self):
        metadata, dependencies, names = self.inventory()
        dependencies[names[2]] = {names[0]}
        dependencies[names[0]] = {names[1]}
        for options in [{}, {"harnesses": [names[0]]}, {"harnesses": [names[2]]}]:
            with self.assertRaisesRegex(ValueError, "relies on ignored"):
                select_harnesses(metadata, dependencies, **options)
        self.assertEqual(select_harnesses(metadata, dependencies,
                                         harnesses=[names[2]], include_ignored=True)[0], names)

    def test_each_explicit_root_is_checked_separately(self):
        metadata, dependencies, names = self.inventory()
        dependencies[names[0]] = {names[1]}
        with self.assertRaisesRegex(ValueError, "relies on ignored"):
            select_harnesses(metadata, dependencies, harnesses=names[:2])

    def test_unknown_empty_conflicting_or_incomplete_inventory_fails(self):
        metadata, dependencies, names = self.inventory()
        with self.assertRaisesRegex(ValueError, "unknown exact"):
            select_harnesses(metadata, dependencies, harnesses=["typo"])
        with self.assertRaisesRegex(ValueError, "mutually exclusive"):
            select_harnesses(metadata, dependencies, include_ignored=True, only_ignored=True)
        with self.assertRaisesRegex(ValueError, "requires ignored"):
            select_harnesses(metadata, dependencies, only_ignored=True, harnesses=[names[0]])
        with self.assertRaisesRegex(ValueError, "every harness"):
            select_harnesses(metadata, {names[0]: set()})
        dependencies[names[0]] = {"missing"}
        with self.assertRaisesRegex(ValueError, "missing compiled"):
            select_harnesses(metadata, dependencies)
        clean = inventory()
        with self.assertRaisesRegex(ValueError, "no harnesses selected"):
            select_harnesses(clean, {clean["proof_harnesses"][0]["pretty_name"]: set()},
                             only_ignored=True)

    def test_reason_byte_limit_accepts_ascii_and_unicode_boundary(self):
        for reason in ["a" * 32, "λ" * 16]:
            metadata = inventory()
            name = metadata["proof_harnesses"][0]["pretty_name"] + "__zerocopy_ignore_" + reason.encode().hex()
            metadata["proof_harnesses"][0]["pretty_name"] = name
            metadata["contracted_functions"][0]["harnesses"] = [name]
            self.assertEqual(ignored_proofs(metadata), {name: reason})

    def test_malformed_noncanonical_and_spoofed_markers_fail(self):
        for suffix in ["", "1", "ff", "C3A9", "20", "00ff", "6f6b::nested",
                       "6f6b__zerocopy_ignore_6f6b", "61" * 33, "cebb" * 17]:
            metadata = inventory()
            name = metadata["proof_harnesses"][0]["pretty_name"] + "__zerocopy_ignore_" + suffix
            metadata["proof_harnesses"][0]["pretty_name"] = name
            metadata["contracted_functions"][0]["harnesses"] = [name]
            with self.assertRaises(ValueError):
                ignored_proofs(metadata)
        metadata, _, _ = self.inventory()
        metadata["proof_harnesses"][-1]["pretty_name"] += "__zerocopy_ignore_6f6b"
        with self.assertRaisesRegex(ValueError, "outside a generated"):
            ignored_proofs(metadata)

    def test_handwritten_replacement_discovery_avoids_generated_restrictions(self):
        functions, graph, harness = CheckingGraphTests().graph_inventory()
        functions[1] = goto_function("f_u8", 0)
        functions[3] = goto_function("dependency", 3)
        checking, used = validate_checking_graph(functions, graph, harness, generated=False)
        self.assertIsNone(checking)
        self.assertEqual(used, {"dependency"})
        # Unreachable dispatcher bodies cannot create dependencies.
        checking, used = validate_checking_graph(functions, graph.replace("wrapper -> dependency\n", ""),
                                                harness, generated=False)
        self.assertEqual(used, set())


if __name__ == "__main__":
    unittest.main()
