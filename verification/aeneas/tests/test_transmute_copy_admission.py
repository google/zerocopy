# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Admission diagnostics, without claiming the unit callback is a drop proof.

Set AENEAS_TRANSMUTE_PROBE to a directory containing the historical probe's
probe.before.ullbc and probe.llbc to exercise real compiler mutations too.
Final verification must run KernelDrops against the fresh production snapshots.
"""
import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'verification/aeneas'))
import admission
import drop_ownership
import prepare

PROBE = os.environ.get('AENEAS_TRANSMUTE_PROBE')


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


class ClosureTests(unittest.TestCase):
    def fixture(self, edges, bodies=None):
        checked = admission.Admission.__new__(admission.Admission)
        bodies = bodies or {}
        checked.functions = {i: {'item_meta': {'name': [
            {'Ident': [part, 0]} for part in
            (admission.TRANSMUTE_COPY if i == 9 else 'owner' + str(i)).split('::')]},
            'generics': {'types': [{'index': 0}, {'index': 1}]},
            'body': bodies.get(i, {'Structured': {'body': {'statements': []}}})}
            for i in {9, *edges, *(c for cs in edges.values() for c in cs)}}
        checked.calls = [{'caller_def_id': owner, 'callee_def_id': child,
                          'type_arguments': ['T0', 'T1']}
                         for owner, children in edges.items() for child in children]
        return checked

    def test_single_choice_through_forwarders(self):
        self.fixture({1: [2], 2: [9]}).audit_copy_closures()

    def test_direct_primitive_retains_nominal_manually_drop_endpoint(self):
        checked = self.fixture({1: [9]})
        checked.calls[0]['type_arguments'] = [admission.MANUALLY_DROP + '<T0>', 'T1']
        checked.audit_copy_closures()

    def test_concrete_forwarding_fails_closed(self):
        for arguments in (['u32', 'T1'], ['T0', 'u32'], ['ManuallyDrop<T0>', 'T1'],
                          [], ['T0', 'T2'], ['T0', 'T-1'], ['T0', 'T01']):
            with self.subTest(arguments=arguments):
                checked = self.fixture({1: [2], 2: [9]})
                checked.calls[0]['type_arguments'] = arguments
                with self.assertRaisesRegex(ValueError, 'forwarding requires original type variables'):
                    checked.audit_copy_closures()

    def test_monomorphic_forwarder_fails_closed(self):
        checked = self.fixture({1: [2], 2: [9]})
        checked.functions[1]['generics']['types'] = []
        with self.assertRaisesRegex(ValueError, 'forwarding requires original type variables'):
            checked.audit_copy_closures()

    def test_monomorphic_copy_owner_fails_closed(self):
        checked = self.fixture({1: [9]})
        checked.functions[1]['generics']['types'] = []
        with self.assertRaisesRegex(ValueError, 'local bodies must be type generic'):
            checked.audit_copy_closures()

    def test_generic_forwarding_uses_actual_source_indices(self):
        checked = self.fixture({1: [2], 2: [9]})
        checked.functions[1]['generics']['types'] = [{'index': 3}, {'index': 4}]
        checked.calls[0]['type_arguments'] = ['T4', 'T3']
        checked.audit_copy_closures()

    def test_duplicate_calls_to_same_helper_count_twice(self):
        with self.assertRaisesRegex(ValueError, 'multiple byte choices'):
            self.fixture({1: [2, 2], 2: [9]}).audit_copy_closures()

    def test_mutual_recursion_reaching_copy(self):
        with self.assertRaisesRegex(ValueError, 'recursive calls'):
            self.fixture({1: [2], 2: [1, 9]}).audit_copy_closures()

    def test_structured_loop_reaching_copy(self):
        with self.assertRaisesRegex(ValueError, 'body loop'):
            self.fixture({1: [9]}, {1: {'Structured': {
                'body': {'kind': {'Loop': {'statements': []}}}}}}).audit_copy_closures()

    def test_cfg_cycle_reaching_copy(self):
        with self.assertRaisesRegex(ValueError, 'CFG cycle'):
            self.fixture({1: [9]}, {1: {'Unstructured': {'body': [
                {'terminator': {'kind': {'Goto': 0}}}]}}}).audit_copy_closures()

    def test_unrelated_loops_and_recursion_keep_existing_admission(self):
        self.fixture({1: [9], 2: [2]}, {2: {'Structured': {
            'body': {'kind': {'Loop': {}}}}}}).audit_copy_closures()

    def test_generic_model_capture_follows_size_and_copy_forwarders(self):
        source = ('public import Aeneas\n'
                  'def sizes (S D : Type) : Result Bool := do\n'
                  '  let a ← core.mem.size_of S\n  let b ← core.mem.size_of D\n'
                  '  ok (a = b)\n'
                  'def helper {S D : Type} (x : S) : Result D := do\n'
                  '  core.mem.transmute_copy D x\n'
                  'def caller {S D : Type} (x : S) : Result D := helper x\n')
        result = prepare.retain_native_models(source)
        self.assertNotIn('native_models def sizes', result)
        for name in ('helper', 'caller'):
            self.assertIn('native_models def ' + name, result)


@unittest.skipUnless(PROBE, 'Set AENEAS_TRANSMUTE_PROBE for compiler snapshot diagnostics')
class CompilerProbeTests(unittest.TestCase):
    def setUp(self):
        self.registry = json.loads((ROOT / 'verification/aeneas/external.json').read_text())
        self.snapshots = []
        for filename in ('probe.before.ullbc', 'probe.llbc'):
            data = json.loads((Path(PROBE) / filename).read_text())
            options = data['translated']['options']
            # Preserve historical files; adapt only their reviewed option roster.
            options['exclude'] = list(admission.EXCLUDED_PROVIDED_METHODS)
            options['opaque'] = [row['rust'] for row in self.registry if row.get('opaque')]
            options['opaque'] += [admission.INTERFACE_ONLY_VALIDATORS,
                                  *admission.INTERFACE_ONLY_TYPES]
            self.snapshots.append(data)
        self.root = 'zerocopy::util::macro_util::aeneas_transmute_copy_caller_probe'

    @staticmethod
    def diagnostic_empty_drop(function):
        # Deliberately no kernel proof. This callback isolates admission guards;
        # it is unsuitable for extraction or any successful verification report.
        return {'function_def_id': function['def_id'],
                'body_sha256': drop_ownership.body_digest(function['body'])}

    def check(self, data, registry=None):
        return admission.Admission(data, registry or self.registry,
            ['zerocopy::IntoBytes', 'zerocopy::FromBytes'],
            certify_drops=self.diagnostic_empty_drop).audit([self.root])

    def test_both_real_compiler_stages_keep_ordered_endpoints_and_global_edge(self):
        reports = [self.check(data) for data in self.snapshots]
        self.assertEqual(reports[0]['calls'], reports[1]['calls'])
        for report in reports:
            row = next(row for row in report['calls']
                       if row.get('callee') == admission.TRANSMUTE_COPY)
            self.assertEqual(row['type_arguments'], [admission.MANUALLY_DROP + '<T0>', 'T1'])
            self.assertEqual((row['caller_def_id'], row['callee_def_id']), (20, 23))
            global_read = next(row for row in report['calls'] if row.get('kind') == 'global')
            self.assertEqual(global_read['callee_def_id'], 25)
            self.assertEqual(global_read['type_arguments'], ['T0', 'T1'])

    def test_selected_endpoint_swap_and_region_change_fail_closed(self):
        for data in self.snapshots:
            for mutation in ('swap', 'region'):
                bad = copy.deepcopy(data)
                function = next(f for f in bad['translated']['fun_decls']
                                if f and f['def_id'] == 20)
                call = next(node['Regular'] for node in nodes(function['body'])
                            if node.get('Regular', {}).get('kind') == {'Fun': 23})
                if mutation == 'swap':
                    call['generics']['types'].reverse()
                else:
                    call['generics']['regions'] = []
                with self.assertRaisesRegex(ValueError, 'transmute_copy endpoints or regions'):
                    self.check(bad)

    def test_duplicate_and_recursive_compiler_closures_fail_closed(self):
        for data in self.snapshots:
            bad = copy.deepcopy(data)
            caller = bad['translated']['fun_decls'][11]
            stage, body = admission.variant(caller['body'])
            if stage == 'Structured':
                statements = body['body']['statements']
                original = next(stmt for stmt in statements
                                if isinstance(stmt['kind'], dict) and 'Call' in stmt['kind'])
                duplicate = copy.deepcopy(original)
                duplicate['id'] = 100000
                statements.insert(statements.index(original), duplicate)
            else:
                blocks = body['body']
                original = next(block for block in blocks if
                    isinstance(block['terminator']['kind'], dict) and
                    'Call' in block['terminator']['kind'])
                blocks.append(copy.deepcopy(original))
            with self.assertRaisesRegex(ValueError, 'multiple byte choices'):
                self.check(bad)
            # Add a recursive call alongside the existing path to copy.
            call = next(node['Regular'] for node in nodes(caller['body'])
                        if node.get('Regular', {}).get('kind') == {'Fun': 20})
            call['kind'] = {'Fun': 11}
            with self.assertRaisesRegex(ValueError, 'recursive calls'):
                self.check(bad)

    def test_signature_and_carrier_mutations_fail_closed(self):
        for data in self.snapshots:
            bad = copy.deepcopy(data)
            bad['translated']['fun_decls'][23]['signature']['is_unsafe'] = False
            with self.assertRaisesRegex(ValueError, 'No reviewed interpretation'):
                self.check(bad)
            for key, value in (('kind', {'Struct': []}), ('generics', {
                    'types': [], 'regions': [], 'const_generics': []})):
                bad = copy.deepcopy(data)
                bad['translated']['type_decls'][6][key] = value
                with self.assertRaisesRegex(ValueError, 'ManuallyDrop shape'):
                    self.check(bad)

    def test_registry_extension_and_external_body_are_exact(self):
        for data in self.snapshots:
            registry = copy.deepcopy(self.registry)
            next(row for row in registry if row['rust'] == admission.TRANSMUTE_COPY)[
                'interpretation_extension'] = 'unchecked'
            with self.assertRaisesRegex(ValueError, 'external boundary changed'):
                self.check(data, registry)
            bad = copy.deepcopy(data)
            bad['translated']['fun_decls'][23]['body'] = {'Intrinsic': {'name': 'transmute'}}
            with self.assertRaisesRegex(ValueError, 'external boundary changed'):
                self.check(bad)

    def test_native_template_signatures_are_checked(self):
        evidence = {'stages': {'llbc': self.check(self.snapshots[1])}}
        template = (Path(PROBE) / 'native/FunsExternal_Template.lean').read_text()
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp) / 'Zerocopy'
            directory.mkdir()
            target = directory / 'FunsExternal_Template.lean'
            target.write_text(template)
            admission.check_translation(Path(tmp), evidence)
            target.write_text(template.replace('Src → Result Dst', 'Dst → Result Src'))
            with self.assertRaisesRegex(ValueError, 'generated failure-capable signature'):
                admission.check_translation(Path(tmp), evidence)


if __name__ == '__main__':
    unittest.main()
