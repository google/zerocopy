# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import native_types as native
import trait_invariants as traits


def params(names=()):
    result = {key: [] for key in native.PARAM_FIELDS}
    result['types'] = [{'index': index, 'name': name} for index, name in enumerate(names)]
    return result


def args(types=(), references=()):
    return {'regions': [], 'types': list(types), 'const_generics': [], 'trait_refs': list(references)}


def meta(name):
    return {'name': [{'Ident': [part, 0]} for part in name.split('::')], 'span': {}}


def fixture(primitive='U8', signed=False):
    scalar = {'Scalar': {'Integer': {'Signed' if signed else 'Unsigned': primitive}}}
    inner = {'Adt': {'id': 2, 'builtin': None, 'generics': args()}}
    reference = {'kind': {'TraitImpl': {'id': 3, 'generics': args()}},
                 'trait_decl_ref': {'regions': [], 'skip_binder': {'id': 1, 'generics': args([scalar])}}}
    source = {'Adt': {'id': 0, 'builtin': None, 'generics': args([scalar], [reference])}}
    nonzero = {'def_id': 0, 'item_meta': meta(native.NONZERO), 'generics': params(['T'])}
    nonzero['generics']['trait_clauses'] = [{'clause_id': 0, 'trait_': {
        'regions': [], 'skip_binder': {'id': 1, 'generics': args([{'TypeVar': {'Bound': [1, 0]}}])}}}]
    trait = {'def_id': 1, 'item_meta': meta(native.ZEROABLE), 'generics': params(['Self']),
             'types': [{'params': params(), 'kind': {'TraitType': [1, 0]},
                        'skip_binder': {'name': 'NonZeroInner', 'default': None}}]}
    inner_decl = {'def_id': 2, 'item_meta': meta('core::num::niche_types::NonZero' + primitive + 'Inner'),
                  'generics': params()}
    dictionary = {'def_id': 3, 'item_meta': meta('native'), 'is_negative': False,
                  'generics': params(), 'impl_trait': {'id': 1, 'generics': args([scalar])},
                  'types': [{'params': params(), 'kind': {'TraitType': [1, 0]},
                             'skip_binder': {'value': inner}}]}
    before = {'type_decls': [nonzero, inner_decl], 'trait_decls': [trait], 'trait_impls': [dictionary]}
    final = copy.deepcopy(before)
    final['type_decls'][0]['generics'] = params(['T', 'Clause0_NonZeroInner'])
    final['trait_decls'][0]['generics'] = params(['Self', 'Self_NonZeroInner'])
    final['trait_decls'][0]['types'] = [None]
    final['trait_impls'][0]['types'] = [None]
    final['trait_impls'][0]['impl_trait']['generics']['types'].append(inner)
    expected = {'Adt': {'id': 0, 'builtin': None, 'generics': args([scalar, inner])}}
    return before, final, source, expected


class NativeAssociatedTypeTests(unittest.TestCase):
    def test_all_twelve_concrete_dictionaries_preserve_nominal_inner(self):
        for sign, primitives in native.PRIMITIVES.items():
            for primitive in primitives:
                with self.subTest(sign=sign, primitive=primitive):
                    before, final, source, expected = fixture(primitive, sign == 'Signed')
                    untouched = copy.deepcopy(source)
                    lifted = native.lift_original_type(source, before, final)
                    self.assertEqual(lifted, expected)
                    self.assertEqual(traits.simple_type(lifted, before), traits.simple_type(expected, final))
                    self.assertEqual(source, untouched)
                    self.assertEqual(traits.simple_type(lifted, before)[2][1][0], 'nominal')

    def test_option_array_and_slice_recurse_without_erasing_the_carrier(self):
        before, final, source, expected = fixture()
        option = {'def_id': 4, 'item_meta': meta('core::option::Option'), 'generics': params(['T'])}
        before['type_decls'].append(option)
        final['type_decls'].append(copy.deepcopy(option))
        wrap = lambda value: {'Adt': {'id': 4, 'builtin': None, 'generics': args([value])}}
        self.assertEqual(native.lift_original_type(wrap(source), before, final), wrap(expected))
        array = {'Array': [source, [{'Integer': {'Unsigned': ['Usize', '2']}}, traits.USIZE], None]}
        lifted = native.lift_original_type(array, before, final)
        self.assertEqual(lifted['Array'][0], expected)
        self.assertEqual(lifted['Array'][1:], array['Array'][1:])
        sliced = {'Slice': [source, None]}
        self.assertEqual(native.lift_original_type(sliced, before, final),
                         {'Slice': [expected, None]})

    def test_rejects_changed_native_evidence(self):
        mutations = {
            'bound trait': lambda b, f, s: b['trait_decls'][0]['item_meta'].update(name=meta('fake::ZeroablePrimitive')['name']),
            'bound Self': lambda b, f, s: b['type_decls'][0]['generics']['trait_clauses'][0]['trait_']['skip_binder']['generics'].update(types=[{'TypeVar': {'Bound': [1, 1]}}]),
            'reference trait': lambda b, f, s: s['Adt']['generics']['trait_refs'][0]['trait_decl_ref']['skip_binder'].update(id=99),
            'dictionary trait': lambda b, f, s: b['trait_impls'][0]['impl_trait'].update(id=99),
            'dictionary Self': lambda b, f, s: b['trait_impls'][0]['impl_trait']['generics'].update(types=[{'Scalar': {'Integer': {'Unsigned': 'U16'}}}]),
            'associated name': lambda b, f, s: b['trait_decls'][0]['types'][0]['skip_binder'].update(name='Other'),
            'associated slot': lambda b, f, s: b['trait_impls'][0]['types'][0].update(kind={'TraitType': [1, 1]}),
            'unknown associated': lambda b, f, s: b['type_decls'][1]['item_meta'].update(name=meta('fake::NonZeroU8Inner')['name']),
            'final associated': lambda b, f, s: f['trait_impls'][0]['impl_trait']['generics']['types'].__setitem__(1, {'Scalar': {'Integer': {'Unsigned': 'U8'}}}),
            'polarity': lambda b, f, s: b['trait_impls'][0].update(is_negative=True),
            'application arity': lambda b, f, s: s['Adt']['generics']['types'].append({'Scalar': {'Integer': {'Unsigned': 'U8'}}}),
            'generic dictionary': lambda b, f, s: b['trait_impls'][0].update(generics=params(['T'])),
            'generic substitution': lambda b, f, s: s['Adt']['generics']['trait_refs'][0]['kind']['TraitImpl']['generics']['types'].append({'TypeVar': {'Free': 0}}),
            'unresolved dictionary': lambda b, f, s: s['Adt']['generics']['trait_refs'][0].update(kind={'Clause': 0}),
            'recursive associated': lambda b, f, s: b['trait_impls'][0]['types'][0]['skip_binder'].update(value=copy.deepcopy(s)),
            'duplicate nominal': lambda b, f, s: b['type_decls'].append({**copy.deepcopy(b['type_decls'][0]), 'def_id': 5}),
            'final lifted prefix': lambda b, f, s: f['type_decls'][0]['generics']['types'][0].update(name='Other'),
        }
        for label, mutate in mutations.items():
            with self.subTest(label=label):
                before, final, source, _ = fixture()
                mutate(before, final, source)
                with self.assertRaises(ValueError):
                    native.lift_original_type(source, before, final)

    def test_unsupported_carrier_dictionary_still_fails_existing_type_check(self):
        before, final, source, _ = fixture()
        before['type_decls'][0]['item_meta'] = meta('fake::NonZero')
        lifted = native.lift_original_type(source, before, final)
        with self.assertRaises(ValueError):
            traits.simple_type(lifted, before)

    def test_changed_final_application_still_fails_exact_equality(self):
        before, final, source, expected = fixture()
        lifted = traits.simple_type(native.lift_original_type(source, before, final), before)
        changed = copy.deepcopy(expected)
        changed['Adt']['generics']['types'][0] = {'Scalar': {'Integer': {'Unsigned': 'U16'}}}
        self.assertNotEqual(lifted, traits.simple_type(changed, final))


if __name__ == '__main__':
    unittest.main()
