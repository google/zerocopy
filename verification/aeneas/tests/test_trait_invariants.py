# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import inline
import trait_invariants as traits


def meta(rust):
    return {'name': [{'Ident': [p, 0]} for p in rust.split('::')], 'is_local': True,
            'span': {'Untagged': {'data': {'file_id': 0, 'beg': {'line': 1, 'col': 0},
                'end': {'line': 4, 'col': 1}}, 'generated_from_span': None}}}


def args(types):
    return {'types': types, 'regions': [], 'const_generics': [], 'trait_refs': []}


def generics(clauses=(), names=('T',)):
    return {'types': [{'name': n} for n in names], 'regions': [], 'const_generics': [],
            'trait_clauses': list(clauses), 'trait_type_constraints': []}


def clause(index=0, variable=None):
    variable = {'Free': 0} if variable is None else variable
    return {'clause_id': index, 'trait_': {'regions': [], 'skip_binder': {
        'id': 0, 'generics': args([{'TypeVar': variable}])}}}


class TraitBindingsTests(unittest.TestCase):
    def setUp(self):
        self.trait = {'def_id': 0, 'item_meta': meta('zerocopy::Marker'),
                      'generics': generics(names=('Self',)), 'types': []}
        self.function = {'def_id': 1, 'item_meta': meta('zerocopy::f'),
                         'generics': generics([clause(7)])}
        self.final = {'trait_decls': [self.trait], 'fun_decls': [self.function],
                      'trait_impls': [], 'files': [{'id': 0, 'name': {'Local': 'src/lib.rs'}}]}
        self.before = copy.deepcopy(self.final)
        self.before['fun_decls'][0]['generics']['trait_clauses'] = [clause(2, {'Bound': [1, 0]})]
        self.annotation = {'generics': ['T'], 'trait_bounds': [{'subject': 'T', 'trait': 'Marker'}]}

    def test_unused_bound_joins_by_application_not_clause_ordinal(self):
        result = traits.check_function_bounds(self.annotation, self.function,
                                              self.final, self.before, {'zerocopy::Marker'})
        self.assertEqual(result[0]['clause_id'], 7)
        self.assertEqual(result[0]['arguments'], [['parameter', 0]])

    def test_missing_bound_and_lifted_type_fail_closed(self):
        for mutation in (lambda: self.function['generics'].update(trait_clauses=[]),
                         lambda: self.function['generics']['types'].append({'name': 'Assoc'})):
            saved = copy.deepcopy(self.function)
            mutation()
            with self.assertRaises(ValueError):
                traits.check_function_bounds(self.annotation, self.function,
                    self.final, self.before, {'zerocopy::Marker'})
            self.function.clear(); self.function.update(saved)

    def test_erased_marker_law_is_rejected(self):
        self.trait['item_meta'] = meta('core::marker::Send')
        with self.assertRaisesRegex(ValueError, 'erased'):
            traits.retained_clauses(self.function, self.final, {'core::marker::Send'})

    def test_reference_and_box_origins_cannot_alias_laws(self):
        for ty in ({'Ref': [None, {'Scalar': 'Bool'}, 'Shared']},
                   {'Adt': {'id': 0, 'builtin': 'Box', 'generics': args([{'Scalar': 'Bool'}])}}):
            with self.assertRaisesRegex(ValueError, 'carrier erasure'):
                traits.simple_type(ty, self.final)

    def test_only_empty_rust_tuple_has_unit_identity(self):
        unit = {'Adt': {'id': 0, 'builtin': 'Tuple', 'generics': args([])}}
        self.assertEqual(traits.simple_type(unit, self.final), ['unit'])
        unit['Adt']['generics']['types'] = [{'Scalar': 'Bool'}]
        with self.assertRaisesRegex(ValueError, 'carrier erasure'):
            traits.simple_type(unit, self.final)

    def test_slice_retains_element_identity_and_rejects_unknown_metadata(self):
        element = {'TypeVar': {'Free': 0}}
        self.assertEqual(traits.simple_type({'Slice': [element, None]}, self.final),
                         ['slice', ['parameter', 0]])
        for ty in ({'Slice': [element]}, {'Slice': [element, {'unknown': 0}]},
                   {'Slice': [{'RawPtr': [element, 'Shared']}, None]},
                   {'Ref': [None, {'Slice': [element, None]}, 'Mut']}):
            with self.assertRaisesRegex(ValueError, 'carrier erasure'):
                traits.simple_type(ty, self.final)

    def test_slice_impl_rejects_changed_element_and_reference_carrier(self):
        annotations = inline.Annotations()
        annotations['zerocopy::Marker'] = {'kind': 'trait', 'rust': 'zerocopy::Marker',
            'generics': ['Self'], 'theorem': 'marker', 'predicate': 'Self = Self'}
        sliced = {'Untagged': {'Slice': [{'TypeVar': {'Free': 0}}, None]}}
        implementation = {'def_id': 2, 'item_meta': meta('zerocopy::SliceMarkerImpl'),
            'impl_trait': {'id': 0, 'generics': args([sliced])},
            'generics': generics()}
        self.final['trait_impls'] = [implementation]
        self.before['trait_impls'] = [copy.deepcopy(implementation)]
        original = self.before['trait_impls'][0]
        original['impl_trait']['generics']['types'][0]['Untagged']['Slice'][0] = {
            'TypeVar': {'Bound': [0, 0]}}
        location = {'file': 'src/lib.rs', 'begin_line': 1, 'end_line': 4}
        native = {'crate': 'zerocopy', 'charon_version': '0.1.276',
            'aeneas_version': 'nightly-2026.10.01-ca282ec+nominal-tuple-structs.1',
            'trait_decls': [{'def_id': 0, 'lean_name': 'Zerocopy.Marker',
                'rust_name': 'zerocopy::Marker', 'is_local': True, 'source': location}],
            'trait_impls': [{'def_id': 2, 'lean_name': 'Zerocopy.Slice.Insts.Marker',
                'impl_trait_def_id': 0, 'impl_trait_rust_name': 'zerocopy::Marker',
                'is_local': True, 'source': location}]}
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp); (work / 'Zerocopy').mkdir()
            (work / 'Zerocopy/translation.json').write_text(json.dumps(native))
            def bind():
                return traits.bind_laws(annotations, work, self.final, self.before)
            self.assertEqual(bind()[1][0]['rust_type'], [['slice', ['parameter', 0]]])
            for changed in (
                    {'Untagged': {'Slice': [{'Scalar': 'Bool'}, None]}},
                    {'Untagged': {'Ref': [None, sliced, 'Mut']}}):
                with self.subTest(carrier=changed):
                    implementation['impl_trait']['generics']['types'] = [changed]
                    with self.assertRaises(ValueError):
                        bind()

    def test_native_mapping_requires_complete_exact_dictionary_identity(self):
        annotations = inline.Annotations()
        annotations['zerocopy::Marker'] = {'kind': 'trait', 'rust': 'zerocopy::Marker',
            'generics': ['Self'], 'theorem': 'marker', 'predicate': 'Self = Self'}
        native = {'crate': 'zerocopy', 'charon_version': '0.1.276',
            'aeneas_version': 'nightly-2026.10.01-ca282ec+nominal-tuple-structs.1',
            'trait_decls': [{'def_id': 0, 'lean_name': 'Zerocopy.Marker',
                'rust_name': 'zerocopy::Marker', 'is_local': True,
                'source': {'file': 'src/lib.rs', 'begin_line': 1, 'end_line': 4}}], 'trait_impls': []}
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp); (work / 'Zerocopy').mkdir()
            path = work / 'Zerocopy/translation.json'; path.write_text(json.dumps(native))
            laws, implementations, _ = traits.bind_laws(annotations, work, self.final, self.before)
            self.assertEqual(laws[0]['raw'], 'Zerocopy.Marker')
            self.assertEqual(implementations, [])
            native['trait_decls'] = []
            path.write_text(json.dumps(native))
            with self.assertRaisesRegex(ValueError, 'lacks a native dictionary'):
                traits.bind_laws(annotations, work, self.final, self.before)

    def test_every_local_impl_requires_binding_and_proof_selection(self):
        annotations = inline.Annotations()
        annotations['zerocopy::Marker'] = {'kind': 'trait', 'rust': 'zerocopy::Marker',
            'generics': ['Self'], 'theorem': 'marker', 'predicate': 'Self = Self'}
        implementation = {'def_id': 2, 'item_meta': meta('zerocopy::MarkerImpl'),
            'impl_trait': {'id': 0, 'generics': args([{'Scalar': 'Bool'}])},
            'generics': generics(names=())}
        self.final['trait_impls'] = [implementation]
        self.before['trait_impls'] = [copy.deepcopy(implementation)]
        location = {'file': 'src/lib.rs', 'begin_line': 1, 'end_line': 4}
        native = {'crate': 'zerocopy', 'charon_version': '0.1.276',
            'aeneas_version': 'nightly-2026.10.01-ca282ec+nominal-tuple-structs.1',
            'trait_decls': [{'def_id': 0, 'lean_name': 'Zerocopy.Marker',
                'rust_name': 'zerocopy::Marker', 'is_local': True, 'source': location}],
            'trait_impls': [{'def_id': 2, 'lean_name': 'Zerocopy.Bool.Insts.Marker',
                'impl_trait_def_id': 0, 'impl_trait_rust_name': 'zerocopy::Marker',
                'is_local': True, 'source': location}]}
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp); (work / 'Zerocopy').mkdir()
            path = work / 'Zerocopy/translation.json'
            path.write_text(json.dumps(native))
            _, implementations, _ = traits.bind_laws(annotations, work, self.final, self.before)
            self.assertEqual(implementations[0]['proof'], 'Zerocopy.Proofs.Bool.Insts.Marker_law')
            original = self.before['trait_impls'][0]
            for mutate in [
                lambda: original['impl_trait'].update(id=1),
                lambda: original['item_meta'].update(name=meta('zerocopy::OtherImpl')['name']),
                lambda: original['item_meta'].update(is_local=False),
            ]:
                saved = copy.deepcopy(original)
                mutate()
                with self.assertRaisesRegex(ValueError, 'original compiler owner'):
                    traits.bind_laws(annotations, work, self.final, self.before)
                original.clear(); original.update(saved)

            annotations.trait_proofs = [{'file': 'zerocopy/src/elsewhere.rs', 'syntax': '__impl',
                'theorem': None, 'open_line': 1, 'open_col': 0, 'end_line': 4, 'end_col': 1}]
            with self.assertRaisesRegex(ValueError, 'was not bound and checked'):
                traits.bind_laws(annotations, work, self.final, self.before)
            annotations.trait_proofs = []
            native['trait_impls'][0]['impl_trait_def_id'] = 1
            path.write_text(json.dumps(native))
            with self.assertRaisesRegex(ValueError, 'different Rust trait'):
                traits.bind_laws(annotations, work, self.final, self.before)
            native['trait_impls'] = []
            path.write_text(json.dumps(native))
            with self.assertRaisesRegex(ValueError, 'lacks its native dictionary'):
                traits.bind_laws(annotations, work, self.final, self.before)

    def test_function_root_nested_unannotated_impl_is_not_a_proof_marker(self):
        annotations = inline.Annotations()
        annotations['zerocopy::Marker'] = {'kind': 'trait', 'rust': 'zerocopy::Marker',
            'generics': ['Self'], 'theorem': 'marker', 'predicate': 'Self = Self'}
        nested_trait = {'def_id': 3,
            'item_meta': meta('zerocopy::helper::StaticAssert'),
            'generics': generics(names=('Self',)), 'types': []}
        annotated = {'def_id': 2, 'item_meta': meta('zerocopy::MarkerImpl'),
            'impl_trait': {'id': 0, 'generics': args([{'Scalar': 'Bool'}])},
            'generics': generics(names=())}
        nested = {'def_id': 4, 'item_meta': meta('zerocopy::helper::StaticAssertImpl'),
            'impl_trait': {'id': 3, 'generics': args([{'Scalar': 'Bool'}])},
            'generics': generics(names=())}
        nested['item_meta']['started_from'] = True
        self.final['trait_decls'].append(nested_trait)
        self.before['trait_decls'].append(copy.deepcopy(nested_trait))
        self.final['trait_impls'] = [annotated, nested]
        self.before['trait_impls'] = copy.deepcopy(self.final['trait_impls'])
        location = {'file': 'src/lib.rs', 'begin_line': 1, 'end_line': 4}
        native = {'crate': 'zerocopy', 'charon_version': '0.1.276',
            'aeneas_version': 'nightly-2026.10.01-ca282ec+nominal-tuple-structs.1',
            'trait_decls': [{'def_id': ident, 'lean_name': raw,
                'rust_name': rust, 'is_local': True, 'source': location}
                for ident, raw, rust in [
                    (0, 'Zerocopy.Marker', 'zerocopy::Marker'),
                    (3, 'Zerocopy.helper.StaticAssert', 'zerocopy::helper::StaticAssert')]],
            'trait_impls': [{'def_id': ident, 'lean_name': raw,
                'impl_trait_def_id': trait, 'impl_trait_rust_name': rust,
                'is_local': True, 'source': location}
                for ident, raw, trait, rust in [
                    (2, 'Zerocopy.Bool.Insts.Marker', 0, 'zerocopy::Marker'),
                    (4, 'Zerocopy.helper.Bool.Insts.StaticAssert', 3,
                     'zerocopy::helper::StaticAssert')]]}
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            (work / 'Zerocopy').mkdir()
            (work / 'Zerocopy/translation.json').write_text(json.dumps(native))

            def bind():
                return traits.bind_laws(annotations, work, self.final, self.before)

            laws, obligations, _ = bind()
            self.assertEqual([law['def_id'] for law in laws], [0])
            # The unmarked annotated dependency still needs its exact proof.
            self.assertEqual([row['def_id'] for row in obligations], [2])
            self.assertEqual(obligations[0]['proof'],
                             'Zerocopy.Proofs.Bool.Insts.Marker_law')
            # Neither compiler stage may independently root an unmarked owner
            # of an annotated trait, even beside a legitimate nested root.
            for crate in (self.before, self.final):
                crate['trait_impls'][0]['item_meta']['started_from'] = True
                with self.assertRaisesRegex(ValueError, 'roots disagree with bound markers'):
                    bind()
                crate['trait_impls'][0]['item_meta']['started_from'] = False
            for crate in (self.before, self.final):
                crate['trait_impls'][0]['item_meta']['started_from'] = True
            annotations.trait_proofs = [{'file': 'zerocopy/src/lib.rs',
                'syntax': '__marker_impl', 'theorem': None,
                'generics': [], 'const_generics': [],
                'open_line': 1, 'open_col': 0, 'end_line': 4, 'end_col': 1}]
            self.assertEqual([row['def_id'] for row in bind()[1]], [2])

    def test_array_impl_retains_usize_const_and_original_application(self):
        annotations = inline.Annotations()
        annotations['zerocopy::Marker'] = {'kind': 'trait', 'rust': 'zerocopy::Marker',
            'generics': ['Self'], 'theorem': 'marker', 'predicate': 'Self = Self'}
        const = {'index': 0, 'name': 'N', 'ty': {'Untagged': traits.USIZE}}
        length = {'Untagged': [{'Var': {'Free': 0}}, {'Untagged': traits.USIZE}]}
        array = {'Untagged': {'Array': [{'TypeVar': {'Free': 0}}, length, None]}}
        implementation = {'def_id': 2, 'item_meta': meta('zerocopy::ArrayMarkerImpl'),
            'impl_trait': {'id': 0, 'generics': args([array])},
            'generics': generics([clause()])}
        implementation['generics']['const_generics'] = [const]
        self.final['trait_impls'] = [implementation]
        self.before['trait_impls'] = [copy.deepcopy(implementation)]
        original = self.before['trait_impls'][0]
        original_array = original['impl_trait']['generics']['types'][0]['Untagged']['Array']
        original_array[0]['TypeVar'] = {'Bound': [0, 0]}
        original_array[1]['Untagged'][0]['Var'] = {'Bound': [0, 0]}
        location = {'file': 'src/lib.rs', 'begin_line': 1, 'end_line': 4}
        native = {'crate': 'zerocopy', 'charon_version': '0.1.276',
            'aeneas_version': 'nightly-2026.10.01-ca282ec+nominal-tuple-structs.1',
            'trait_decls': [{'def_id': 0, 'lean_name': 'Zerocopy.Marker',
                'rust_name': 'zerocopy::Marker', 'is_local': True, 'source': location}],
            'trait_impls': [{'def_id': 2, 'lean_name': 'Zerocopy.Array.Insts.Marker',
                'impl_trait_def_id': 0, 'impl_trait_rust_name': 'zerocopy::Marker',
                'is_local': True, 'source': location}]}
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp); (work / 'Zerocopy').mkdir()
            (work / 'Zerocopy/translation.json').write_text(json.dumps(native))
            def bind():
                return traits.bind_laws(annotations, work, self.final, self.before)
            _, rows, _ = bind()
            self.assertEqual(rows[0]['const_parameters'], [{'index': 0, 'name': 'N', 'type': 'usize'}])
            self.assertEqual(rows[0]['rust_type'],
                [['array', ['parameter', 0], ['const_parameter', 0]]])
            marker = {'file': 'zerocopy/src/lib.rs', 'syntax': '__array_impl',
                'theorem': None, 'generics': ['T'], 'const_generics': ['N'],
                'open_line': 1, 'open_col': 0,
                'end_line': 4, 'end_col': 1}
            annotations.trait_proofs = [marker]
            # A caller-reachable dictionary alone does not satisfy a marker.
            with self.assertRaisesRegex(ValueError, 'independently request'):
                bind()
            original['item_meta']['started_from'] = True
            implementation['item_meta']['started_from'] = True
            self.assertEqual(bind()[1][0]['proof'], 'Zerocopy.Proofs.Array.Insts.Marker_law')
            for key, value in [('generics', []),
                               ('const_generics', ['Other']), ('open_col', 1)]:
                saved = marker[key]
                marker[key] = value
                with self.assertRaises(ValueError):
                    bind()
                marker[key] = saved
            annotations.trait_proofs = []
            original['item_meta']['started_from'] = False
            implementation['item_meta']['started_from'] = False

            mutations = [
                lambda: implementation['generics'].update(const_generics=[]),
                lambda: implementation['generics']['const_generics'][0].update(name='Other'),
                lambda: implementation['generics']['const_generics'][0].update(ty={'Scalar': 'Bool'}),
                lambda: implementation['impl_trait']['generics']['types'][0]['Untagged']['Array'][1]
                    ['Untagged'][0].update(Var={'Free': 1}),
                lambda: implementation['impl_trait']['generics']['types'][0]['Untagged']['Array'][1]
                    ['Untagged'].__setitem__(0, {'Integer': {'Unsigned': ['Usize', '3']}}),
            ]
            for mutation in mutations:
                saved = copy.deepcopy(implementation)
                mutation()
                with self.assertRaises(ValueError):
                    bind()
                implementation.clear(); implementation.update(saved)

    def test_const_expressions_and_non_usize_lengths_fail_closed(self):
        for value in [
                [{'Var': {'Free': 0}}, {'Scalar': 'Bool'}],
                [{'Global': 3}, traits.USIZE],
                [{'Integer': {'Unsigned': ['U32', '3']}}, traits.USIZE]]:
            with self.assertRaises(ValueError):
                traits.simple_const(value)

    def parameterized_function(self):
        self.trait['item_meta'] = meta('zerocopy::TransmuteFrom')
        self.trait['generics'] = generics(names=('Self', 'Src', 'SV', 'DV'))
        self.function['generics'] = generics([clause(7)], names=('Src', 'Dst', 'SV', 'DV'))
        self.function['generics']['trait_clauses'][0]['trait_']['skip_binder']['generics'] = args(
            [{'TypeVar': {'Free': i}} for i in (1, 0, 2, 3)])
        self.before = copy.deepcopy(self.final)
        original = self.before['fun_decls'][0]['generics']['trait_clauses'][0]
        original['clause_id'] = 2
        original['trait_']['skip_binder']['generics'] = args(
            [{'TypeVar': {'Bound': [1, i]}} for i in (1, 0, 2, 3)])
        self.annotation = {'generics': ['Src', 'Dst', 'SV', 'DV'],
            'trait_bounds': [{'subject': 'Dst', 'trait': 'TransmuteFrom', 'argument_count': 3}]}

        def check():
            return traits.check_function_bounds(self.annotation, self.function,
                self.final, self.before, {'zerocopy::TransmuteFrom'})
        return check

    def test_parameterized_bound_matches_original_self_and_arity(self):
        check = self.parameterized_function()
        self.assertEqual(check()[0]['arguments'],
                         [['parameter', i] for i in (1, 0, 2, 3)])
        bound = self.annotation['trait_bounds'][0]
        for key, wrong in [('subject', 'Src'), ('subject', None),
                           ('argument_count', 2), ('argument_count', 4),
                           ('argument_count', -1), ('argument_count', True)]:
            saved = bound[key]
            bound[key] = wrong
            with self.subTest(key=key, value=wrong), self.assertRaises(ValueError):
                check()
            bound[key] = saved
        bound.pop('argument_count')
        with self.assertRaisesRegex(ValueError, 'exact resolved compiler application'):
            check()

    def test_parameterized_bound_keeps_every_argument_identity_and_order(self):
        check = self.parameterized_function()
        application = self.function['generics']['trait_clauses'][0]['trait_']['skip_binder']
        original = copy.deepcopy(application['generics']['types'])
        for left in range(4):
            for right in range(left + 1, 4):
                changed = copy.deepcopy(original)
                changed[left], changed[right] = changed[right], changed[left]
                application['generics']['types'] = changed
                with self.subTest(swap=(left, right)), self.assertRaisesRegex(
                        ValueError, 'lost or changed a required source bound'):
                    check()
        for changed in [original[:-1], original + original[-1:],
                        original[:-1] + original[:1]]:
            application['generics']['types'] = changed
            with self.assertRaises(ValueError):
                check()
        application['generics']['types'] = original
        self.function['generics']['trait_clauses'].append(copy.deepcopy(
            self.function['generics']['trait_clauses'][0]))
        with self.assertRaisesRegex(ValueError, 'lost or changed a required source bound'):
            check()

    def test_parameterized_trait_declaration_preserves_generic_and_implied_bounds(self):
        self.parameterized_function()
        validity = {'def_id': 3, 'item_meta': meta('zerocopy::Validity'),
                    'generics': generics(names=('Self',)), 'types': []}
        parent = {'def_id': 4, 'item_meta': meta('zerocopy::Parent'),
                  'generics': generics(names=('Self',)), 'types': []}
        for crate in (self.final, self.before):
            crate['trait_decls'].extend(copy.deepcopy([validity, parent]))
            for index in (2, 3):
                bound = clause(index, {'Free': index})
                bound['trait_']['skip_binder']['id'] = 3
                crate['trait_decls'][0]['generics']['trait_clauses'].append(bound)
            implied = clause(0)
            implied['trait_']['skip_binder']['id'] = 4
            crate['trait_decls'][0]['implied_clauses'] = [implied]
        annotations = inline.Annotations()
        annotations['zerocopy::TransmuteFrom'] = {
            'kind': 'trait', 'rust': 'zerocopy::TransmuteFrom',
            'generics': ['Self', 'Src', 'SV', 'DV'],
            'trait_bounds': [{'subject': 'SV', 'trait': 'Validity'},
                             {'subject': 'DV', 'trait': 'Validity'},
                             {'subject': 'Self', 'trait': 'Parent'}],
            'theorem': 'transmute_from', 'predicate': 'True'}
        location = {'file': 'src/lib.rs', 'begin_line': 1, 'end_line': 4}
        native = {'crate': 'zerocopy', 'charon_version': '0.1.276',
            'aeneas_version': 'nightly-2026.10.01-ca282ec+nominal-tuple-structs.1',
            'trait_decls': [{'def_id': ident, 'lean_name': 'Zerocopy.' + label,
                'rust_name': 'zerocopy::' + label, 'is_local': True, 'source': location}
                for ident, label in [(0, 'TransmuteFrom'), (3, 'Validity'), (4, 'Parent')]],
            'trait_impls': []}
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            (work / 'Zerocopy').mkdir()
            (work / 'Zerocopy/translation.json').write_text(json.dumps(native))

            def bind():
                return traits.bind_laws(annotations, work, self.final, self.before)

            self.assertEqual(bind()[0][0]['generic_count'], 4)
            # Actual Charon output puts both parameter bounds in implied_clauses.
            for crate in (self.final, self.before):
                declaration = crate['trait_decls'][0]
                declaration['implied_clauses'].extend(declaration['generics']['trait_clauses'])
                declaration['generics']['trait_clauses'] = []
            self.assertEqual(bind()[0][0]['generic_count'], 4)
            for crate in (self.final, self.before):
                declaration = crate['trait_decls'][0]
                declaration['generics']['trait_clauses'] = declaration['implied_clauses'][1:]
                declaration['implied_clauses'] = declaration['implied_clauses'][:1]
            parameters = self.trait['generics']['types']
            parameters[2], parameters[3] = parameters[3], parameters[2]
            with self.assertRaisesRegex(ValueError, 'original type-only parameters'):
                bind()
            parameters[2], parameters[3] = parameters[3], parameters[2]
            # Clause order and ordinals may change; semantic identities may not.
            self.trait['generics']['trait_clauses'].reverse()
            self.assertEqual(bind()[0][0]['generic_count'], 4)
            for field in ('trait_clauses', 'implied_clauses'):
                container = self.trait['generics'] if field == 'trait_clauses' else self.trait
                saved = copy.deepcopy(container[field])
                container[field] = []
                with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'dictionary law'):
                    bind()
                container[field] = saved
            bound = self.trait['generics']['trait_clauses'][0]
            application = bound['trait_']['skip_binder']['generics']
            application['types'][0] = {'TypeVar': {'Free': 1}}
            with self.assertRaisesRegex(ValueError, 'generic normalization'):
                bind()
            application['types'][0] = {'TypeVar': {'Free': 3}}
            for crate in (self.final, self.before):
                crate['trait_decls'][0]['generics']['trait_clauses'] = []
            with self.assertRaisesRegex(ValueError, 'exact resolved compiler application'):
                bind()

    def test_parameterized_function_cannot_omit_either_stage_bound(self):
        for crate_name in ('final', 'before'):
            check = self.parameterized_function()
            getattr(self, crate_name)['fun_decls'][0]['generics']['trait_clauses'] = []
            with self.subTest(stage=crate_name), self.assertRaisesRegex(
                    ValueError, 'lost or changed a required source bound'):
                check()

    def test_parameterized_impl_preserves_the_complete_native_application(self):
        self.parameterized_function()
        annotations = inline.Annotations()
        annotations['zerocopy::TransmuteFrom'] = {
            'kind': 'trait', 'rust': 'zerocopy::TransmuteFrom',
            'generics': ['Self', 'Src', 'SV', 'DV'],
            'theorem': 'transmute_from', 'predicate': 'True'}
        implementation = {'def_id': 2, 'item_meta': meta('zerocopy::TransmuteImpl'),
            'impl_trait': {'id': 0, 'generics': args([
                {'TypeVar': {'Free': i}} for i in (1, 0, 2, 3)])},
            'generics': generics(names=('Src', 'Dst', 'SV', 'DV'))}
        self.final['trait_impls'] = [implementation]
        self.before['trait_impls'] = [copy.deepcopy(implementation)]
        location = {'file': 'src/lib.rs', 'begin_line': 1, 'end_line': 4}
        native = {'crate': 'zerocopy', 'charon_version': '0.1.276',
            'aeneas_version': 'nightly-2026.10.01-ca282ec+nominal-tuple-structs.1',
            'trait_decls': [{'def_id': 0, 'lean_name': 'Zerocopy.TransmuteFrom',
                'rust_name': 'zerocopy::TransmuteFrom', 'is_local': True, 'source': location}],
            'trait_impls': [{'def_id': 2, 'lean_name': 'Zerocopy.TransmuteImpl',
                'impl_trait_def_id': 0, 'impl_trait_rust_name': 'zerocopy::TransmuteFrom',
                'is_local': True, 'source': location}]}
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            (work / 'Zerocopy').mkdir()
            (work / 'Zerocopy/translation.json').write_text(json.dumps(native))

            def bind():
                return traits.bind_laws(annotations, work, self.final, self.before)

            self.assertEqual(bind()[1][0]['rust_type'],
                             [['parameter', i] for i in (1, 0, 2, 3)])
            for crate_name in ('final', 'before'):
                application = getattr(self, crate_name)['trait_impls'][0]['impl_trait']['generics']
                for field in ('regions', 'const_generics', 'trait_refs'):
                    application[field] = [{}]
                    try:
                        with self.subTest(stage=crate_name, field=field), self.assertRaisesRegex(
                                ValueError, 'Unsupported dependent trait-law arguments'):
                            bind()
                    finally:
                        application[field] = []
                original = copy.deepcopy(application['types'])
                for left in range(4):
                    for right in range(left + 1, 4):
                        changed = copy.deepcopy(original)
                        changed[left], changed[right] = changed[right], changed[left]
                        application['types'] = changed
                        with self.subTest(stage=crate_name, swap=(left, right)), self.assertRaisesRegex(
                                ValueError, 'lost its original Rust type application'):
                            bind()
                for changed in (original[:-1], original + original[-1:],
                                original[:-1] + original[:1]):
                    application['types'] = changed
                    with self.subTest(stage=crate_name, types=changed), self.assertRaises(ValueError):
                        bind()
                application['types'] = original
            for crate in (self.final, self.before):
                crate['type_decls'] = [
                    {'def_id': 5, 'item_meta': meta('zerocopy::Cell')},
                    {'def_id': 6, 'item_meta': meta('zerocopy::UnsafeCell')}]
                nominal_bound = clause()
                nominal_bound['trait_']['skip_binder']['generics'] = args([
                    {'Adt': {'id': 5, 'builtin': None,
                             'generics': args([{'TypeVar': {'Free': 0}}])}},
                    *[{'TypeVar': {'Free': i}} for i in (0, 2, 3)]])
                crate['trait_impls'][0]['generics']['trait_clauses'] = [nominal_bound]
            self.assertEqual(bind()[1][0]['dictionary_count'], 1)
            bound = implementation['generics']['trait_clauses'][0]
            subject = bound['trait_']['skip_binder']['generics']['types'][0]
            subject['Adt']['id'] = 6
            with self.assertRaisesRegex(ValueError, 'changed its required dictionaries'):
                bind()
            subject['Adt']['id'] = 5
            implementation['generics']['trait_clauses'] = []
            with self.assertRaisesRegex(ValueError, 'changed its required dictionaries'):
                bind()
            self.before['trait_impls'][0]['generics']['trait_clauses'] = []
            # Comparing both stages is insufficient if both have discarded a
            # required formal argument. Native declaration arity also matters.
            for crate in (self.final, self.before):
                crate['trait_impls'][0]['impl_trait']['generics']['types'].pop()
            with self.assertRaisesRegex(ValueError, 'declared type arity'):
                bind()

    def test_parameterized_bound_keeps_nominal_argument_identity(self):
        check = self.parameterized_function()
        for crate in (self.final, self.before):
            crate['type_decls'] = [{'def_id': 5, 'item_meta': meta('zerocopy::Cell')},
                                   {'def_id': 6, 'item_meta': meta('zerocopy::UnsafeCell')}]
            app = crate['fun_decls'][0]['generics']['trait_clauses'][0]['trait_']['skip_binder']
            app['generics']['types'][1] = {'Adt': {'id': 5, 'builtin': None,
                'generics': args([app['generics']['types'][1]])}}
        self.assertEqual(check()[0]['arguments'][1],
                         ['nominal', 'zerocopy::Cell', [['parameter', 0]]])
        app = self.function['generics']['trait_clauses'][0]['trait_']['skip_binder']
        app['generics']['types'][1]['Adt']['id'] = 6
        with self.assertRaisesRegex(ValueError, 'lost or changed a required source bound'):
            check()

    def test_parameterized_bound_rejects_native_equalities_and_lifetimes(self):
        for field in ('regions', 'trait_type_constraints'):
            check = self.parameterized_function()
            for crate in (self.final, self.before):
                crate['trait_decls'][0]['generics'][field] = [{}]
            with self.subTest(owner='trait', field=field), self.assertRaises(ValueError):
                check()
        for crate_name in ('final', 'before'):
            check = self.parameterized_function()
            crate = getattr(self, crate_name)
            crate['fun_decls'][0]['generics']['trait_type_constraints'] = [{}]
            with self.subTest(owner=crate_name), self.assertRaisesRegex(ValueError, 'constraints'):
                check()
        for binder in (True, False):
            check = self.parameterized_function()
            clause_ref = self.function['generics']['trait_clauses'][0]['trait_']
            if binder:
                clause_ref['regions'] = [{}]
            else:
                clause_ref['skip_binder']['generics']['regions'] = ['Static']
            with self.subTest(binder=binder), self.assertRaises(ValueError):
                check()

    def test_supertrait_graph_keeps_native_parent_identities(self):
        parent = {'def_id': 3, 'item_meta': meta('zerocopy::Parent'),
                  'generics': generics(names=('Self',)), 'types': []}
        self.final['trait_decls'].append(parent)
        self.before['trait_decls'].append(copy.deepcopy(parent))
        child_bound = clause(0); child_bound['trait_']['skip_binder']['id'] = 3
        self.trait['implied_clauses'] = [child_bound]
        self.assertEqual(traits.predicate(child_bound, self.final)['rust'], 'zerocopy::Parent')
        self.assertEqual(traits.predicate(child_bound, self.final)['clause_id'], 0)


if __name__ == '__main__':
    unittest.main()
