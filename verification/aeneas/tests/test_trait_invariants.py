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
            annotations.trait_proofs = [{'file': 'zerocopy/src/elsewhere.rs', 'syntax': '__impl',
                'theorem': 'other_proof', 'open_line': 1, 'end_line': 4, 'end_col': 1}]
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
