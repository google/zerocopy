# Copyright 2026 The Fuchsia Authors
# SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

"""Mutate compiler owner evidence independently of executable-body checks."""

import copy
from pathlib import Path
import sys
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import admission
import trait_invariants as traits


def arguments(types=(), references=(), consts=()):
    return {'regions': [], 'types': list(types), 'const_generics': list(consts),
            'trait_refs': list(references)}


def parameter(depth=None, index=0):
    return {'TypeVar': {'Free': index} if depth is None else {'Bound': [depth, index]}}


def metadata(rust):
    return {'name': [{'Ident': [p, 0]} for p in rust.split('::')],
            'span': {'source': rust}, 'is_local': True}


def binder(reference):
    return {'regions': [], 'skip_binder': reference}


def trait_reference(types, trait=0):
    return {'id': trait, 'generics': arguments(types)}


def default_fixture():
    params = {'types': [], 'regions': [], 'const_generics': [], 'trait_clauses': []}
    function = {'def_id': 3, 'item_meta': metadata('zerocopy::Marker::make'),
        'src': {'TraitDefault': {'trait_ref': trait_reference([parameter()]), 'item_id': 2}},
        'generics': {'types': [{'name': 'Self'}], 'trait_clauses': []}}
    method = {'params': params, 'kind': {'TraitMethod': [0, 2]}, 'skip_binder': {
        'name': 'make', 'item_meta': copy.deepcopy(function['item_meta']),
        'default': {'id': 3, 'generics': arguments([parameter()])}}}
    trait = {'def_id': 0, 'item_meta': metadata('zerocopy::Marker'),
             'generics': {'types': [{'name': 'Self'}]}, 'methods': [None, None, method]}
    final = {'trait_decls': [trait], 'fun_decls': [function]}
    before = copy.deepcopy(final)
    old = before['fun_decls'][0]
    old['src']['TraitDefault']['trait_ref']['generics']['types'] = [parameter(0)]
    old['generics']['trait_clauses'] = [{'clause_id': 0, 'origin': 'TraitSelf',
        'trait_': binder(trait_reference([parameter(1)]))}]
    before['trait_decls'][0]['methods'][2]['skip_binder']['default']['generics'] = arguments(
        [parameter(1)], [{'kind': 'SelfId',
                         'trait_decl_ref': binder(trait_reference([parameter(2)]))}])
    annotation = {'default_trait': 'Marker', 'generics': ['Self'], 'trait_bounds': []}
    return annotation, function, final, before


class DefaultOwnerTests(unittest.TestCase):
    def setUp(self):
        self.annotation, self.function, self.final, self.before = default_fixture()

    def check(self):
        return traits.check_function_bounds(self.annotation, self.function,
                                            self.final, self.before, {'zerocopy::Marker'})

    def test_exact_default_retains_only_the_erased_self_obligation(self):
        self.assertEqual(self.check(), [])
        self.assertEqual(self.annotation['erased_self_bound'], {
            'rust': 'zerocopy::Marker', 'arguments': [['parameter', 0]],
            'trait_def_id': 0, 'method_id': 2})

    def test_missing_or_changed_source_and_compiler_owner_reject(self):
        mutations = [
            lambda: self.annotation.pop('default_trait'),
            lambda: self.annotation.update(default_trait='Other'),
            lambda: self.function.update(src='TopLevel'),
            lambda: self.before['fun_decls'][0].update(src='TopLevel'),
            lambda: self.before['fun_decls'].clear(),
            lambda: self.function['src']['TraitDefault'].pop('trait_ref'),
            lambda: self.before['fun_decls'][0]['src']['TraitDefault'].pop('trait_ref'),
            lambda: self.before['fun_decls'][0]['src']['TraitDefault'].update(item_id=1),
            lambda: self.final['trait_decls'][0]['item_meta'].update(name=metadata('zerocopy::Other')['name']),
        ]
        for mutate in mutations:
            self.setUp()
            mutate()
            with self.subTest(mutation=mutate), self.assertRaises(ValueError):
                self.check()

    def test_top_level_string_without_default_annotation_remains_ordinary(self):
        self.annotation.pop('default_trait')
        self.function['src'] = 'TopLevel'
        self.assertEqual(traits.default_method_owner(
            self.annotation, self.function, self.final, self.before), None)

    def test_missing_or_wrong_declared_default_slot_rejects(self):
        for stage in ('before', 'final'):
            for mutation in ('missing', 'required', 'wrong_function', 'wrong_kind', 'wrong_name'):
                self.setUp()
                crate = getattr(self, stage)
                slot = crate['trait_decls'][0]['methods'][2]
                if mutation == 'missing':
                    crate['trait_decls'][0]['methods'][2] = None
                elif mutation == 'required':
                    slot['skip_binder']['default'] = None
                elif mutation == 'wrong_function':
                    slot['skip_binder']['default']['id'] += 1
                elif mutation == 'wrong_kind':
                    slot['kind']['TraitMethod'][1] = 1
                else:
                    slot['skip_binder']['item_meta'] = metadata('zerocopy::Marker::other')
                with self.subTest(stage=stage, mutation=mutation), self.assertRaises(ValueError):
                    self.check()

    def test_same_id_default_slot_type_or_dictionary_mutations_reject(self):
        for stage in ('before', 'final'):
            for mutation in ('slot_type', 'source_extra_args', 'slot_extra_args', 'dictionary'):
                self.setUp()
                crate = getattr(self, stage)
                slot = crate['trait_decls'][0]['methods'][2]['skip_binder']['default']
                if mutation == 'slot_type':
                    slot['generics']['types'] = [{'Scalar': 'Bool'}]
                elif mutation == 'source_extra_args':
                    crate['fun_decls'][0]['src']['TraitDefault']['trait_ref']['generics']['trait_refs'] = ['SelfId']
                elif mutation == 'slot_extra_args':
                    slot['generics']['regions'] = ['Static']
                elif stage == 'before':
                    slot['generics']['trait_refs'][0]['trait_decl_ref']['skip_binder']['generics']['types'] = [{'Scalar': 'Bool'}]
                else:
                    slot['generics']['trait_refs'] = [{'kind': 'SelfId'}]
                with self.subTest(stage=stage, mutation=mutation), self.assertRaises(ValueError):
                    self.check()

    def test_erased_self_never_licenses_erasure_of_another_bound(self):
        self.before['fun_decls'][0]['generics']['trait_clauses'].append({
            'clause_id': 1, 'origin': 'WhereClauseOnFn',
            'trait_': binder(trait_reference([parameter(1)]))})
        with self.assertRaisesRegex(ValueError, 'lost or changed'):
            self.check()


class DefaultAdmissionTests(unittest.TestCase):
    def setUp(self):
        _, function, final, before = default_fixture()
        self.function = function
        self.trait = final['trait_decls'][0]
        self.implementation = {'def_id': 0, 'impl_trait': trait_reference([{'Scalar': 'Bool'}]),
            'generics': {'types': [], 'const_generics': [], 'trait_clauses': []},
            'methods': [None, None, {'kind': {'TraitMethod': [0, 2]},
                'skip_binder': {'id': 3, 'generics': arguments([{'Scalar': 'Bool'}])}}]}
        self.checked = object.__new__(admission.Admission)
        self.checked.before = False
        self.checked.crate = final
        self.checked.functions = {3: function}
        self.checked.visit = mock.Mock()

    def check(self):
        self.checked.audit_implementation(self.implementation, self.trait)

    def original_dictionary(self):
        self.checked.before = True
        self.reference = {'kind': {'TraitImpl': {'id': 0, 'generics': arguments()}},
            'trait_decl_ref': binder(trait_reference([{'Scalar': 'Bool'}]))}
        self.implementation['methods'][2]['skip_binder']['generics']['trait_refs'] = [self.reference]

    def test_shared_actual_default_is_visited_after_ownership_validation(self):
        for original in (False, True):
            if original:
                self.original_dictionary()
            self.check()
        self.assertEqual(self.checked.visit.call_args_list, [mock.call(3), mock.call(3)])

    def test_top_level_string_is_controlled_rejection(self):
        self.function['src'] = 'TopLevel'
        with self.assertRaisesRegex(ValueError, 'native implementation owner'):
            self.check()

    def test_wrong_default_owner_slot_and_type_reject_before_visiting(self):
        for mutation in ('owner', 'slot', 'type', 'function'):
            self.setUp()
            if mutation == 'owner':
                self.function['src']['TraitDefault']['trait_ref']['id'] = 1
            elif mutation == 'slot':
                self.function['src']['TraitDefault']['item_id'] = 1
            elif mutation == 'type':
                self.implementation['methods'][2]['skip_binder']['generics']['types'] = [parameter()]
            else:
                self.trait['methods'][2]['skip_binder']['default']['id'] = 4
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                self.check()
            self.checked.visit.assert_not_called()

    def test_same_dictionary_ids_with_wrong_trait_application_reject(self):
        self.original_dictionary()
        self.reference['trait_decl_ref']['skip_binder']['generics']['types'] = [{'Scalar': 'Char'}]
        with self.assertRaisesRegex(ValueError, 'Self dictionary'):
            self.check()
        self.checked.visit.assert_not_called()

    def test_same_dictionary_id_with_unjustified_impl_arguments_reject(self):
        for field, value in [('types', [{'Scalar': 'Bool'}]),
                             ('const_generics', ['invented']), ('trait_refs', ['invented'])]:
            self.setUp()
            self.original_dictionary()
            self.reference['kind']['TraitImpl']['generics'][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'Self dictionary'):
                self.check()
            self.checked.visit.assert_not_called()

    def generic_dictionary(self):
        self.original_dictionary()
        def length(depth, index=0):
            return [{'Var': {'Bound': [depth, index]}}, traits.USIZE]
        def array(depth):
            return {'Array': [parameter(depth), length(depth), None]}
        self.implementation['generics'] = {
            'types': [{'name': 'T'}],
            'const_generics': [{'index': 0, 'name': 'N', 'ty': traits.USIZE}],
            'trait_clauses': [{'clause_id': 7,
                'trait_': binder(trait_reference([parameter(1)]))}]}
        self.implementation['impl_trait']['generics']['types'] = [array(0)]
        self.implementation['methods'][2]['skip_binder']['generics']['types'] = [array(1)]
        self.reference['trait_decl_ref']['skip_binder']['generics']['types'] = [array(2)]
        self.reference['kind']['TraitImpl']['generics'] = arguments(
            [parameter(1)], [{'kind': {'Clause': {'Bound': [1, 7]}},
                'trait_decl_ref': binder(trait_reference([parameter(2)]))}], [length(1)])

    def test_generic_self_dictionary_keeps_types_consts_and_bound_dictionary(self):
        self.generic_dictionary()
        self.check()
        self.checked.visit.assert_called_once_with(3)

    def test_generic_self_dictionary_mutations_reject(self):
        for mutation in ('type', 'const', 'clause_id', 'clause_type'):
            self.setUp()
            self.generic_dictionary()
            supplied = self.reference['kind']['TraitImpl']['generics']
            if mutation == 'type':
                supplied['types'][0] = parameter(1, 1)
            elif mutation == 'const':
                supplied['const_generics'][0][0]['Var']['Bound'][1] = 1
            elif mutation == 'clause_id':
                supplied['trait_refs'][0]['kind']['Clause']['Bound'][1] = 8
            else:
                supplied['trait_refs'][0]['trait_decl_ref']['skip_binder']['generics']['types'] = [{'Scalar': 'Bool'}]
            with self.subTest(mutation=mutation), self.assertRaisesRegex(ValueError, 'Self dictionary'):
                self.check()
            self.checked.visit.assert_not_called()

    def test_missing_or_retained_self_dictionary_rejects(self):
        self.checked.before = True
        with self.assertRaisesRegex(ValueError, 'Self dictionary'):
            self.check()
        self.original_dictionary()
        self.checked.before = False
        with self.assertRaisesRegex(ValueError, 'retained default-method Self dictionary'):
            self.check()


class InterfaceValidatorTests(unittest.TestCase):
    def setUp(self):
        function = {'def_id': 3, 'item_meta': metadata('zerocopy::validator'),
            'body': 'Opaque', 'src': {'TraitImpl': {
                'impl_ref': {'id': 0}, 'trait_ref': {'id': 0}, 'item_id': 1}}}
        trait = {'def_id': 0, 'item_meta': metadata('zerocopy::TryFromBytes'),
            'methods': [None, {'skip_binder': {'name': 'is_safe'}}]}
        implementation = {'def_id': 0, 'impl_trait': {'id': 0},
            'methods': [None, {'skip_binder': {'id': 3}}]}
        self.checked = object.__new__(admission.Admission)
        self.checked.crate = {'trait_decls': [trait], 'trait_impls': [implementation]}
        self.checked.functions = {3: function}
        self.checked.visited = {}
        self.checked.law_traits = set()
        self.reference = {'kind': {'TraitImpl': {'id': 0}},
                          'trait_decl_ref': {'skip_binder': {'id': 0}}}

    def test_carrying_signature_only_dictionary_does_not_admit_its_execution(self):
        self.checked.dictionary(self.reference)
        self.assertEqual(self.checked.visited, {})
        with self.assertRaisesRegex(ValueError, 'signature-only TryFromBytes validator'):
            self.checked.visit(3)
        self.assertEqual(self.checked.visited, {})

    def test_actual_trait_dispatch_to_validator_rejects(self):
        with self.assertRaisesRegex(ValueError, 'signature-only TryFromBytes validator'):
            self.checked.trait_call([self.reference, 1], arguments(), [])
        self.assertEqual(self.checked.visited, {})


if __name__ == '__main__':
    unittest.main()
