# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Native layout gates for the documented physical wrapper providers."""
import copy
import unittest
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import physical_models as physical


def declaration(owner, fields, transparent=True, number=1):
    return {'def_id': number,
            'item_meta': {'name': [{'Ident': [part, 0]} for part in owner.split('::')],
                          'is_local': owner.startswith('zerocopy::'),
                          'opacity': 'Transparent' if owner.startswith('zerocopy::') else 'Foreign',
                          'has_errors': False},
            'generics': {'types': [{'index': 0, 'name': 'T'}], 'regions': [],
                         'const_generics': [], 'trait_clauses': [], 'regions_outlive': [],
                         'types_outlive': [], 'trait_type_constraints': []},
            'kind': {'Struct': fields},
            'layout': [{'key': 'target', 'value': {'repr': {
                'repr_algo': 'Rust' if transparent else 'C',
                'align_modif': None if transparent else {'Pack': 1},
                'transparent': transparent, 'explicit_discr_type': None}}}]}


def field(name='_0', ty=None):
    return {'name': name, 'is_positional': name.startswith('_'),
            'ty': physical._typevar() if ty is None else ty}


class PhysicalWrapperTests(unittest.TestCase):
    def setUp(self):
        self.owner = 'zerocopy::wrappers::Unalign'
        self.raw = declaration(self.owner, [field()], transparent=False)
        self.final = {'type_decls': [self.raw]}

    def test_packed_payload_is_explicit_plan(self):
        plan = physical.validate_physical_wrapper_plans(self.final, copy.deepcopy(self.final))[self.owner]
        self.assertEqual(physical.physical_model_suffix(plan), ' with_physical 0')
        self.assertEqual(plan['phantom_fields'], [])
        self.assertEqual(plan['native']['layout'], self.raw['layout'])

    def test_default_repr_cannot_reuse_proof(self):
        self.raw['layout'][0]['value']['repr']['repr_algo'] = 'Rust'
        with self.assertRaisesRegex(ValueError, 'native repr'):
            physical.validate_physical_wrapper_plans(self.final)

    def test_replaced_payload_cannot_reuse_proof(self):
        self.raw['kind']['Struct'][0]['ty'] = {'Untagged': {'Scalar': 'Bool'}}
        with self.assertRaisesRegex(ValueError, 'payload field'):
            physical.validate_physical_wrapper_plans(self.final)

    def test_added_field_cannot_reuse_proof(self):
        self.raw['kind']['Struct'].append(field('_1'))
        with self.assertRaisesRegex(ValueError, 'field count'):
            physical.validate_physical_wrapper_plans(self.final)

    def test_missing_layout_fails_closed(self):
        self.raw['layout'] = []
        with self.assertRaisesRegex(ValueError, 'layout unavailable'):
            physical.validate_physical_wrapper_plans(self.final)

    def test_generic_shape_cannot_reuse_proof(self):
        self.raw['generics']['const_generics'] = [{'index': 0}]
        with self.assertRaisesRegex(ValueError, 'generic constraints'):
            physical.validate_physical_wrapper_plans(self.final)

    def test_whole_final_repr_identity(self):
        before = copy.deepcopy(self.final)
        before['type_decls'][0]['layout'][0]['value']['repr']['transparent'] = True
        with self.assertRaisesRegex(ValueError, 'whole/final'):
            physical.validate_physical_wrapper_plans(self.final, before)

    def test_no_structural_universal_fallback(self):
        other = declaration('local::Transparent', [field()])
        empty = declaration('local::Zst', [])
        self.assertEqual(physical.validate_physical_wrapper_plans({'type_decls': [other, empty]}), {})

    def test_wrapping_requires_native_transparent_repr(self):
        wrapping = declaration('core::num::wrapping::Wrapping', [field()])
        final = {'type_decls': [wrapping]}
        self.assertIn('core::num::wrapping::Wrapping', physical.validate_physical_wrapper_plans(final))
        wrapping['layout'][0]['value']['repr']['transparent'] = False
        with self.assertRaisesRegex(ValueError, 'native repr'):
            physical.validate_physical_wrapper_plans(final)

    def test_byteorder_requires_bytes_and_only_phantom(self):
        phantom = declaration('core::marker::PhantomData', [], number=3)
        phantom['layout'][0]['value'].update(
            size={'chosen': physical._constant(0)}, align={'chosen': physical._constant(1)})
        bytes_ty = {'Untagged': {'Array': [
            {'Untagged': {'Scalar': {'Integer': {'Unsigned': 'U8'}}}},
            physical._constant(2)['Untagged']['Constant'], None]}}
        phantom_ty = {'Untagged': {'Adt': {'id': 3,
            'generics': {'regions': [], 'types': [physical._typevar()],
                         'const_generics': [], 'trait_refs': []}, 'builtin': None}}}
        raw = declaration('zerocopy::byteorder::U16', [field(ty=bytes_ty), field('_1', phantom_ty)])
        final = {'type_decls': [raw, phantom]}
        plan = physical.validate_physical_wrapper_plans(final)['zerocopy::byteorder::U16']
        self.assertEqual(plan['phantom_fields'], [1])
        phantom['layout'][0]['value']['align']['chosen'] = physical._constant(2)
        with self.assertRaisesRegex(ValueError, 'alignment one'):
            physical.validate_physical_wrapper_plans(final)


if __name__ == '__main__':
    unittest.main()
