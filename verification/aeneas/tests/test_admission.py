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
        # The preserved fixture predates interface-only IntoBytes extraction.
        # Only unused provided methods can be excluded; any executable reference
        # is a compiler error, also covered by native front-end controls.
        self.data['translated']['options']['exclude'] = list(admission.EXCLUDED_PROVIDED_METHODS)
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

    def abstract_trait_fixture(self):
        checked = admission.Admission(self.data, self.registry, ['zerocopy::Codec'])
        params = {'types': [], 'regions': [], 'const_generics': [], 'trait_clauses': []}
        signature = {'abi': 'Rust', 'is_variadic': False, 'is_unsafe': False,
                     'inputs': [], 'output': {'Untagged': {'Scalar': 'Bool'}}}
        trait = {'def_id': 0, 'item_meta': {'name': [{'Ident': ['zerocopy', 0]},
            {'Ident': ['Codec', 0]}]}, 'methods': [{'params': params,
                'kind': {'TraitMethod': [0, 0]}, 'skip_binder': {'signature': signature,
                    'item_meta': {'has_errors': False, 'is_extern': False}}}]}
        checked.crate['trait_decls'] = [trait]
        poly = {'regions': [], 'skip_binder': {'id': 0, 'generics': {
            'types': [{'Untagged': {'TypeVar': {'Free': 0}}}], 'regions': [],
            'const_generics': [], 'trait_refs': []}}}
        checked.current_function = {'generics': {'trait_clauses': [{'clause_id': 3, 'trait_': poly}]}}
        reference = {'kind': {'Clause': {'Free': 3}}, 'trait_decl_ref': poly}
        return checked, trait, reference

    def test_abstract_dispatch_is_an_exact_declared_generic_input(self):
        checked, trait, reference = self.abstract_trait_fixture()
        checked.trait_call([reference, 0], {'types': [], 'regions': [],
            'const_generics': [], 'trait_refs': []}, [])
        self.assertEqual(checked.calls[0]['method'], 0)
        reference['kind']['Clause']['Free'] = 8
        with self.assertRaisesRegex(ValueError, 'outside the exact generic clauses'):
            checked.abstract_dictionary(reference)
        reference['kind']['Clause']['Free'] = 3
        with self.assertRaisesRegex(ValueError, 'declared method'):
            checked.trait_call([reference, 1], {}, [])
        checked.law_traits.clear()
        with self.assertRaisesRegex(ValueError, 'lacks an admitted trait law'):
            checked.abstract_dictionary(reference)

    def test_trait_impl_methods_remain_executable_admission_roots(self):
        checked, trait, _ = self.abstract_trait_fixture()
        ident = next(iter(checked.functions))
        function = checked.functions[ident]
        function['src'] = {'TraitImpl': {'impl_ref': {'id': 0},
                                       'trait_ref': {'id': 0}, 'item_id': 0}}
        function['body']['Unstructured']['body'][0]['terminator']['kind'] = {'InlineAsm': {
            'asm': '', 'kind': 'Normal', 'targets': [], 'on_unwind': 0}}
        implementation = {'def_id': 0, 'methods': [{'kind': {'TraitMethod': [0, 0]},
                                                  'skip_binder': {'id': ident}}]}
        with self.assertRaisesRegex(ValueError, 'InlineAsm'):
            checked.audit_implementation(implementation, trait)
        implementation['methods'] = []
        with self.assertRaisesRegex(ValueError, 'missing a method body'):
            checked.audit_implementation(implementation, trait)
        implementation['methods'] = [{'kind': {'TraitMethod': [0, 1]}, 'skip_binder': {'id': ident}}]
        with self.assertRaisesRegex(ValueError, 'wrong compiler owner'):
            checked.audit_implementation(implementation, trait)

    def test_supertrait_dispatch_preserves_original_clause_and_parent_application(self):
        checked, trait, reference = self.abstract_trait_fixture()
        child_reference = copy.deepcopy(reference)
        child_reference['trait_decl_ref']['skip_binder']['id'] = 1
        checked.current_function['generics']['trait_clauses'][0]['trait_'] = child_reference['trait_decl_ref']
        parent_clause = {'clause_id': 6, 'trait_': copy.deepcopy(reference['trait_decl_ref'])}
        parent_clause['trait_']['skip_binder']['generics']['types'] = [{'TypeVar': {'Bound': [1, 0]}}]
        child = {'def_id': 1, 'methods': [], 'item_meta': {'name': [{'Ident': ['zerocopy', 0]},
                 {'Ident': ['Child', 0]}]}, 'implied_clauses': [parent_clause]}
        checked.crate['trait_decls'].append(child)
        reference['kind'] = {'ParentClause': [child_reference, 6]}
        self.assertIs(checked.abstract_dictionary(reference), trait)
        reference['kind']['ParentClause'][1] = 7
        with self.assertRaisesRegex(ValueError, 'declared parent clause'):
            checked.abstract_dictionary(reference)

    def test_unreviewed_exclusions_fail_closed(self):
        for exclusions in ([], [*admission.EXCLUDED_PROVIDED_METHODS, 'zerocopy::unsafe_helper']):
            self.data['translated']['options']['exclude'] = exclusions
            with self.assertRaisesRegex(ValueError, 'Unreviewed extraction option exclude'):
                self.check()

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

    def test_input_identity_covers_the_full_source_tree_and_shared_models(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tools = root / 'runtime'
            tools.mkdir()
            (tools / 'aeneas-build.json').write_text('{}')
            (root / 'zerocopy/src').mkdir(parents=True)
            (root / 'zerocopy/src/lib.rs').write_text('fn f() {}')
            with mock.patch.dict(os.environ, {'AENEAS_TOOLCHAIN_DIR': str(tools),
                    'CARGO_HOME': str(root / 'cargo')}, clear=True):
                baseline = admission.input_identity(root)
                for name in ('zerocopy/src/vendor/new.rs', 'zerocopy/src/.lake/new.rs',
                             'zerocopy/Cargo.lock', 'tools/aeneas-inline/Cargo.toml',
                             'anneal/lean/Rust/Layout.lean', 'anneal/lean/golden/Model.lean',
                             'anneal/flake.nix'):
                    path = root / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text('new verification input')
                    with self.subTest(name=name):
                        self.assertNotEqual(admission.input_identity(root), baseline)
                    path.unlink()
                    self.assertEqual(admission.input_identity(root), baseline)
                for name in ('golden/Funs.lean', 'projections/Specs.lean'):
                    path = root / 'verification/aeneas' / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text('reviewed output')
                    self.assertEqual(admission.input_identity(root), baseline)

    def test_snapshot_is_mandatory(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, 'Missing mandatory before'):
                admission.inspect(ROOT, Path(directory), [self.root], 'source-digest')


if __name__ == '__main__':
    unittest.main()
