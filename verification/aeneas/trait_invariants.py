# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Bind trait laws to compiler identities and native Aeneas dictionaries.

The original AST checks coverage; only final LLBC clauses identify emitted
arguments. Clause ordinals and associated-type proof paths are not joined
across simplification. Unsupported carrier erasure and lifting fail closed.
"""

from collections import Counter
import json
import re

IDENTIFIER = r'[A-Za-z_][A-Za-z_0-9]*'
LEAN_NAME = re.compile(IDENTIFIER + r'(?:\.' + IDENTIFIER + r')*')
MARKERS = {
    'core::marker::Sized', 'core::marker::MetaSized',
    'core::marker::PointeeSized', 'core::marker::Destruct',
    'core::ptr::metadata::Pointee', 'core::ptr::metadata::Thin',
    'core::marker::Send', 'core::marker::Sync', 'core::marker::Unpin',
    'core::marker::Tuple', 'core::clone::TrivialClone', 'core::alloc::Allocator',
}


def unwrap(value):
    while isinstance(value, dict) and len(value) == 1:
        if 'Untagged' in value:
            value = value['Untagged']
        elif 'Value' in value:
            value = value['Value'][1]
        else:
            break
    if isinstance(value, dict) and 'Deduplicated' in value:
        raise ValueError('Trait laws require the admitted non-deduplicated AST')
    return value


def name(meta):
    elements = meta['name']
    if not all(set(e) == {'Ident'} and e['Ident'][1] == 0 for e in elements):
        raise ValueError('Unsupported trait-law Rust identity')
    return '::'.join(e['Ident'][0] for e in elements)


def declarations(crate, group):
    result = {}
    for declaration in crate.get(group, []):
        if not declaration:
            continue
        ident = declaration['def_id']
        if not isinstance(ident, int) or ident < 0 or ident in result:
            raise ValueError('Duplicate or invalid compiler declaration identity')
        result[ident] = declaration
    return result


def simple_type(value, crate, bound_depth=0):
    """Retain Rust origins; Box/reference/tuple carriers must not alias laws."""
    value = unwrap(value)
    if not isinstance(value, dict) or len(value) != 1:
        raise ValueError('Unsupported trait-law Rust type')
    tag, body = next(iter(value.items()))
    if tag == 'TypeVar':
        if set(body) == {'Free'}:
            return ['parameter', body['Free']]
        if set(body) == {'Bound'} and body['Bound'][0] == bound_depth:
            return ['parameter', body['Bound'][1]]
    elif tag == 'Scalar':
        return ['scalar', body]
    elif tag == 'Adt' and body.get('builtin') is None:
        args = body['generics']
        if not any(args.get(k) for k in ('regions', 'const_generics', 'trait_refs')):
            declaration = declarations(crate, 'type_decls').get(body['id'])
            if declaration is not None:
                return ['nominal', name(declaration['item_meta']),
                        [simple_type(t, crate, bound_depth) for t in args['types']]]
    raise ValueError('Trait-law carrier erasure or associated types are unsupported')


def predicate(clause, crate):
    bound = clause.get('trait_', clause.get('trait'))
    if not isinstance(bound, dict) or bound.get('regions'):
        raise ValueError('Higher-ranked trait laws are unsupported')
    reference = bound.get('skip_binder', bound.get('binder_value'))
    trait = declarations(crate, 'trait_decls').get(reference['id'])
    if trait is None:
        raise ValueError('Trait clause lacks its compiler declaration')
    args = reference['generics']
    if any(args.get(k) for k in ('regions', 'const_generics', 'trait_refs')):
        raise ValueError('Unsupported dependent trait-law arguments')
    return {'rust': name(trait['item_meta']),
            # The original AST has an item binder outside the (empty)
            # RegionBinder. unbind_item_vars makes these Free in final LLBC.
            'arguments': [simple_type(t, crate, 1) for t in args['types']],
            'clause_id': clause['clause_id']}


def key(predicate):
    return json.dumps([predicate['rust'], predicate['arguments']], sort_keys=True)


def retained_clauses(function, crate, annotated_traits):
    result = []
    for clause in function['generics'].get('trait_clauses', []):
        p = predicate(clause, crate)
        if p['rust'] in MARKERS:
            if p['rust'] in annotated_traits:
                raise ValueError('An annotated trait bound is erased by Aeneas')
            continue
        result.append(p)
    return result


def check_function_bounds(annotation, function, final, before, annotated_traits):
    """Compare semantic applications, never pre/post clause ordinals."""
    after = retained_clauses(function, final, annotated_traits)
    if not after and not annotation.get('trait_bounds'):
        return []
    if before is None:
        raise ValueError('Generic trait roots require the original admission AST')
    originals = [f for f in before.get('fun_decls', []) if f
                 and f['item_meta']['name'] == function['item_meta']['name']]
    if len(originals) != 1:
        raise ValueError('Generic trait root lacks an unambiguous original compiler owner')
    original = originals[0]
    if original['item_meta']['span'] != function['item_meta']['span']:
        raise ValueError('Generic trait root changed its original compiler source owner')
    original_names = [p['name'] for p in original['generics']['types']]
    final_names = [p['name'] for p in function['generics']['types']]
    if original_names != final_names or final_names != annotation['generics']:
        raise ValueError('Associated-type lifting changed the source generic prefix')
    original_predicates = [predicate(c, before)
                           for c in original['generics'].get('trait_clauses', [])]
    expected = [p for p in original_predicates if p['rust'] not in MARKERS]
    erased_laws = [p for p in original_predicates
                   if p['rust'] in MARKERS and p['rust'] in annotated_traits]
    if erased_laws or Counter(map(key, expected)) != Counter(map(key, after)):
        raise ValueError('Trait normalization lost or changed a required source bound')
    # Source syntax is only a proposed location/name. The resolved pre-AST
    # applications must explain every written bound on an original type variable.
    for bound in annotation.get('trait_bounds', []):
        index = annotation['generics'].index(bound['subject'])
        candidates = [p for p in original_predicates
                      if p['arguments'] == [['parameter', index]]
                      and (p['rust'] == bound['trait']
                           or p['rust'].endswith('::' + bound['trait']))]
        if len(candidates) != 1:
            raise ValueError('Source trait bound lacks an exact resolved compiler application')
    return after


def read_translation(work, final):
    path = work / 'Zerocopy/translation.json'
    if not path.is_file():
        raise ValueError('Trait invariants require Aeneas -emit-json bindings')
    result = json.loads(path.read_text())
    if (result.get('crate') != 'zerocopy' or result.get('charon_version') != '0.1.276'
            or result.get('aeneas_version') != 'nightly-2026.10.01-ca282ec+nominal-tuple-structs.1'):
        raise ValueError('Unsupported native trait binding manifest')
    for group, native in [('trait_decls', 'trait_decls'), ('trait_impls', 'trait_impls')]:
        ids = declarations(final, group)
        seen, names = set(), set()
        for entry in result.get(native, []):
            ident = entry.get('def_id')
            if (ident in seen or ident not in ids or entry.get('lean_name') in names
                    or not LEAN_NAME.fullmatch(entry.get('lean_name', ''))):
                raise ValueError('Invalid or duplicate native trait dictionary identity')
            seen.add(ident)
            names.add(entry['lean_name'])
            declaration = ids[ident]
            if entry.get('is_local') != declaration['item_meta'].get('is_local'):
                raise ValueError('Native trait dictionary disagrees with compiler ownership')
            if group == 'trait_decls' and entry.get('rust_name') != name(declaration['item_meta']):
                raise ValueError('Native trait declaration has the wrong Rust identity')
            if group == 'trait_impls' and entry.get('impl_trait_def_id') != declaration['impl_trait']['id']:
                raise ValueError('Native dictionary implements a different Rust trait')
            if group == 'trait_impls':
                trait = declarations(final, 'trait_decls')[declaration['impl_trait']['id']]
                if entry.get('impl_trait_rust_name') != name(trait['item_meta']):
                    raise ValueError('Native implementation has the wrong resolved Rust trait name')
            span = unwrap(declaration['item_meta']['span'])['data']
            file = next(f for f in final['files'] if f and f['id'] == span['file_id'])
            if (file.get('name', {}).get('Local') != entry.get('source', {}).get('file')
                    or span['beg']['line'] != entry.get('source', {}).get('begin_line')
                    or span['end']['line'] != entry.get('source', {}).get('end_line')):
                raise ValueError('Native trait binding has the wrong compiler source location')
    return result


def bind_laws(annotations, work, final, before):
    """Select every extracted local implementation, including derives/macros."""
    trait_annotations = {rust: a for rust, a in annotations.items() if a.get('kind') == 'trait'}
    if not trait_annotations:
        if getattr(annotations, 'trait_proofs', []):
            raise ValueError('Implementation proof has no annotated trait invariant')
        if not any(getattr(annotations, 'function_dictionaries', {}).values()):
            return [], [], []
    native = read_translation(work, final)
    native_traits = {e['def_id']: e for e in native['trait_decls']}
    native_impls = {e['def_id']: e for e in native['trait_impls']}
    traits = declarations(final, 'trait_decls')
    laws, implementations, dictionaries = [], [], []
    for ident, entry in native_traits.items():
        dictionaries.append({'def_id': ident, 'rust': name(traits[ident]['item_meta']),
                             'raw': entry['lean_name']})
    for ident, trait in traits.items():
        rust = name(trait['item_meta'])
        if rust not in trait_annotations:
            continue
        annotation = trait_annotations[rust]
        if ident not in native_traits:
            raise ValueError(f'Annotated trait lacks a native dictionary: {rust}')
        if [p['name'] for p in trait['generics']['types']] != annotation['generics']:
            raise ValueError('Trait invariant associated-type lifting is unsupported')
        original = declarations(before, 'trait_decls').get(ident) if before else None
        if (original is None or original['item_meta']['name'] != trait['item_meta']['name']
                or original.get('types') or original['generics'].get('trait_type_constraints')):
            raise ValueError('Trait invariant requires an original trait without associated types')
        original_parents = [predicate(c, before) for c in original.get('implied_clauses', [])]
        final_parents = [predicate(c, final) for c in trait.get('implied_clauses', [])]
        if (any(p['rust'] in MARKERS and p['rust'] in trait_annotations for p in original_parents)
                or Counter(key(p) for p in original_parents if p['rust'] not in MARKERS)
                != Counter(key(p) for p in final_parents if p['rust'] not in MARKERS)):
            raise ValueError('Trait supertrait normalization lost a required dictionary law')
        laws.append({**annotation, 'def_id': ident, 'raw': native_traits[ident]['lean_name'],
                     'law': 'Zerocopy.TraitLaws.' + annotation['theorem'],
                     'generic_count': len(annotation['generics'])})
    if {l['rust'] for l in laws} != set(trait_annotations):
        raise ValueError('Compiler bindings omit an annotated trait')
    by_id = {law['def_id']: law for law in laws}
    used_proofs = set()
    for ident, implementation in declarations(final, 'trait_impls').items():
        law = by_id.get(implementation['impl_trait']['id'])
        if law is None or implementation['item_meta'].get('is_local') is not True:
            continue
        entry = native_impls.get(ident)
        if entry is None:
            raise ValueError('An annotated trait implementation lacks its native dictionary')
        generics = implementation['generics']
        if generics.get('const_generics') or generics.get('regions') or generics.get('trait_type_constraints'):
            raise ValueError('Unsupported generic trait-law implementation')
        original = declarations(before, 'trait_impls').get(ident) if before else None
        if original is None or original['item_meta']['span'] != implementation['item_meta']['span']:
            raise ValueError('Trait implementation lacks its original compiler owner')
        if ([p['name'] for p in original['generics']['types']]
                != [p['name'] for p in generics['types']]
                or Counter(map(key, retained_clauses(original, before, trait_annotations)))
                != Counter(map(key, retained_clauses(implementation, final, trait_annotations)))):
            raise ValueError('Trait implementation normalization changed its required dictionaries')
        types = [simple_type(t, final) for t in implementation['impl_trait']['generics']['types']]
        original_types = [simple_type(t, before) for t in original['impl_trait']['generics']['types']]
        if types != original_types:
            raise ValueError('Trait implementation lost its original Rust type application')
        span = unwrap(implementation['item_meta']['span'])
        file = next(f for f in final['files'] if f and f['id'] == span['data']['file_id'])
        matching = [p for p in getattr(annotations, 'trait_proofs', [])
                    if file['name'] == {'Local': p['file'].removeprefix('zerocopy/')}
                    and span['data']['beg']['line'] <= p['open_line'] <= span['data']['end']['line']
                    and span['data']['end'] == {'line': p['end_line'], 'col': p['end_col']}]
        if len(matching) > 1:
            raise ValueError('Ambiguous source implementation proof binding')
        proof = matching[0]['theorem'] if matching else entry['lean_name'].removeprefix('Zerocopy.') + '_law'
        if matching:
            used_proofs.add((matching[0]['file'], matching[0]['syntax']))
        implementations.append({'def_id': ident, 'trait_def_id': law['def_id'],
            'dictionary': entry['lean_name'], 'law': law['law'],
            'proof': 'Zerocopy.Proofs.' + proof, 'rust_type': types,
            'generic_count': len(generics['types']),
            'dictionary_count': len(retained_clauses(implementation, final, trait_annotations))})
    if used_proofs != {(p['file'], p['syntax']) for p in getattr(annotations, 'trait_proofs', [])}:
        raise ValueError('An annotated implementation proof was not bound and checked')
    return laws, implementations, dictionaries
