# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Mutate a real pinned pre-transformation extraction, preserving each cause.

These controls do not execute invalid Rust. Admission failures are separate
from the kernel tests of the guarded primitives and their caller contracts.
"""
import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'verification/aeneas'))
import admission


class AdmissionTests(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((Path(__file__).with_name('admission') /
                                'boolean.before.ullbc').read_text())
        self.registry = json.loads((ROOT / 'verification/aeneas/external.json').read_text())
        self.root = 'zerocopy::util::safety_checks::checked_bool'

    def check(self):
        return admission.Admission(self.data, self.registry).audit([self.root])

    def body(self):
        return self.data['translated']['fun_decls'][0]['body']['Unstructured']['body']

    def test_transitive_registered_boundary(self):
        report = self.check()
        self.assertEqual(report['roots'], [self.root])
        self.assertIn('zerocopy::util::transmute_unchecked',
                      [row['rust'] for row in report['executions']])

    def test_missing_registration_is_not_an_opaque_success(self):
        self.registry = [r for r in self.registry if not r.get('opaque')]
        self.data['translated']['options']['opaque'] = []
        with self.assertRaisesRegex(ValueError, 'No reviewed interpretation'):
            self.check()

    def test_callee_annotations_never_exempt_unsupported_effects(self):
        # This callee has a valid-looking proof comment, but no registered
        # interpretation. Inspecting the caller must still reject its assembly.
        callee = self.data['translated']['fun_decls'][1]
        self.registry = [r for r in self.registry if not r.get('opaque')]
        self.data['translated']['options']['opaque'] = []
        callee['item_meta']['attr_info']['attributes'] = [{'DocComment': '```aeneas'}]
        callee['body'] = copy.deepcopy(self.data['translated']['fun_decls'][0]['body'])
        callee['body']['Unstructured']['body'][0]['terminator']['kind'] = {'InlineAsm': {
            'asm': '', 'kind': 'Normal', 'targets': [], 'on_unwind': 0}}
        with self.assertRaisesRegex(ValueError, 'InlineAsm'):
            self.check()

    def test_unsupported_instantiation_even_with_same_named_boundary(self):
        for block in self.body():
            call = block['terminator']['kind']
            if isinstance(call, dict) and 'Call' in call:
                types = call['Call']['call']['func']['Regular']['generics']['types']
                types[0] = {'Untagged': {'Scalar': {'Integer': {'Unsigned': 'U16'}}}}
        with self.assertRaisesRegex(ValueError, 'Unsupported transmute instantiation'):
            self.check()

    def test_drop_before_cleanup_and_on_unwind_is_rejected(self):
        for index in [0, len(self.body()) - 1]:
            with self.subTest(block=index):
                previous = self.body()[index]['terminator']['kind']
                self.body()[index]['terminator']['kind'] = {'Drop': {}}
                with self.assertRaisesRegex(ValueError, 'original terminator Drop'):
                    self.check()
                self.body()[index]['terminator']['kind'] = previous

    def test_new_operations_attributes_and_configuration_fail_closed(self):
        original = copy.deepcopy(self.data)
        mutations = [
            lambda: self.body()[0]['statements'].append({
                'span': None, 'comments_before': [], 'kind': {'NewEffect': 0}}),
            lambda: self.data['translated']['fun_decls'][0]['item_meta']['attr_info']['attributes'].append(
                {'Unknown': {'path': 'target_feature', 'args': 'enable="x"'}}),
            lambda: self.data['translated']['options'].update(skip_borrowck=True),
            lambda: self.data['translated']['options'].update(new_erasure=True),
            lambda: self.data['translated']['options'].update(ops_to_function_calls=False),
            lambda: self.data['translated']['fun_decls'][0]['item_meta']['attr_info']['attributes'].append(
                {'NewAttribute': None}),
            lambda: self.data['translated']['target_information'][0]['value'].update(target_pointer_size=4),
        ]
        for mutate in mutations:
            self.data = copy.deepcopy(original)
            mutate()
            with self.assertRaises(ValueError):
                self.check()

    def test_padding_and_raw_storage_cannot_be_logical_values(self):
        self.data['translated']['fun_decls'][0]['body']['Unstructured']['locals']['locals'][0]['ty'] = {
            'Untagged': {'RawPtr': []}}
        with self.assertRaisesRegex(ValueError, 'raw pointers and storage'):
            self.check()

    def test_bit_invalid_production_cannot_be_an_infallible_cast(self):
        self.body()[0]['statements'].append({
            'span': None, 'comments_before': [], 'kind': {'Assign': [
                {'kind': {'Local': 0}, 'ty': {'Untagged': {'Scalar': 'Bool'}}},
                {'UnaryOp': [{'Cast': {'Transmute': []}}, {'Const': None}]}]}})
        with self.assertRaisesRegex(ValueError, 'Unreviewed cast Transmute'):
            self.check()

    def test_ub_abort_must_not_become_unwind_termination(self):
        self.body()[0]['terminator']['kind'] = {'Abort': 'UnwindTerminate'}
        with self.assertRaisesRegex(ValueError, 'Unreviewed abort UnwindTerminate'):
            self.check()

    def test_guarded_translation_must_remain_failure_capable(self):
        evidence = {'stages': {'llbc': {'executions': [
            {'rust': 'zerocopy::util::transmute_unchecked',
             'lean': 'util.transmute_unchecked'}]}}}
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            (work / 'Zerocopy').mkdir()
            template = work / 'Zerocopy/FunsExternal_Template.lean'
            signature = 'axiom util.transmute_unchecked {Src : Type} (Dst : Type) : Src → Result Dst'
            template.write_text(signature)
            admission.check_translation(work, evidence)
            for mutant in [signature.replace('Result Dst', 'Dst'), '']:
                template.write_text(mutant)
                with self.assertRaisesRegex(ValueError, 'failure-capable signature'):
                    admission.check_translation(work, evidence)

    def test_compiler_override_is_rejected_before_compilation(self):
        with mock.patch.dict(os.environ, RUSTFLAGS='-Zmir-opt-level=2'):
            with self.assertRaisesRegex(ValueError, 'compiler override RUSTFLAGS'):
                admission.input_identity(ROOT)

    def test_snapshot_is_mandatory(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, 'Missing mandatory before'):
                admission.inspect(ROOT, Path(directory), [self.root], 'source-digest')


if __name__ == '__main__':
    unittest.main()
