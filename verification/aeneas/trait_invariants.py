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
across simplification. Arrays retain their original element and usize const
identities. Unsupported carrier erasure and lifting fail closed.
"""

from collections import Counter
import json
import re

from native_types import lift_original_type

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


USIZE = {'Scalar': {'Integer': {'Unsigned': 'Usize'}}}


def simple_const(value, bound_depth=0):
    """Preserve the compiler's usize const identity and literal value."""
    value = unwrap(value)
    if not isinstance(value, list) or len(value) != 2 or unwrap(value[1]) != USIZE:
        raise ValueError('Trait-law array length must be an audited usize const')
    value = value[0]
    if isinstance(value, dict) and set(value) == {'Var'}:
        variable = value['Var']
        if set(variable) == {'Free'}:
            return ['const_parameter', variable['Free']]
        if set(variable) == {'Bound'} and variable['Bound'][0] == bound_depth:
            return ['const_parameter', variable['Bound'][1]]
    if isinstance(value, dict) and set(value) == {'Integer'}:
        literal = value['Integer'].get('Unsigned')
        if (isinstance(literal, list) and len(literal) == 2
                and literal[0] == 'Usize' and isinstance(literal[1], str)
                and re.fullmatch(r'0|[1-9][0-9]*', literal[1])):
            return ['const_usize', literal[1]]
    raise ValueError('Unsupported trait-law array const expression')


def usize_const_parameters(generics):
    parameters = generics.get('const_generics', [])
    result = []
    for index, parameter in enumerate(parameters):
        if (parameter.get('index') != index or unwrap(parameter.get('ty')) != USIZE
                or not re.fullmatch(IDENTIFIER, parameter.get('name', ''))):
            raise ValueError('Trait implementations support only original usize const parameters')
        result.append({'index': index, 'name': parameter['name'], 'type': 'usize'})
    return result


def check_application_parameters(types, type_count, const_count):
    def visit(value):
        if not isinstance(value, list):
            return
        if len(value) == 2 and value[0] in ('parameter', 'const_parameter'):
            limit = type_count if value[0] == 'parameter' else const_count
            if not isinstance(value[1], int) or not 0 <= value[1] < limit:
                raise ValueError('Trait application refers to an omitted original parameter')
        for child in value:
            visit(child)
    for value in types:
        visit(value)


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
    elif tag == 'Array' and isinstance(body, list) and len(body) == 3 and body[2] is None:
        return ['array', simple_type(body[0], crate, bound_depth),
                simple_const(body[1], bound_depth)]
    elif tag == 'Adt' and body.get('builtin') == 'Tuple':
        if body.get('generics') == {'regions': [], 'types': [],
                                   'const_generics': [], 'trait_refs': []}:
            return ['unit']
    elif tag == 'Adt' and body.get('builtin') is None:
        args = body['generics']
        if not any(args.get(k) for k in ('regions', 'const_generics', 'trait_refs')):
            declaration = declarations(crate, 'type_decls').get(body['id'])
            if declaration is not None:
                return ['nominal', name(declaration['item_meta']),
                        [simple_type(t, crate, bound_depth) for t in args['types']]]
    raise ValueError('Trait-law carrier erasure or associated types are unsupported')


def type_only_trait_arguments(arguments, arity):
    """Reject discarded argument kinds before comparing compiler applications."""
    if (not isinstance(arguments, dict)
            or set(arguments) != {'regions', 'types', 'const_generics', 'trait_refs'}
            or not isinstance(arguments['types'], list)
            or any(arguments[k] for k in ('regions', 'const_generics', 'trait_refs'))):
        raise ValueError('Unsupported dependent trait-law arguments')
    if len(arguments['types']) != arity:
        raise ValueError('Trait-law application changed its declared type arity')
    return arguments['types']


def predicate(clause, crate):
    bound = clause.get('trait_', clause.get('trait'))
    if not isinstance(bound, dict) or bound.get('regions'):
        raise ValueError('Higher-ranked trait laws are unsupported')
    reference = bound.get('skip_binder', bound.get('binder_value'))
    trait = declarations(crate, 'trait_decls').get(reference['id'])
    if trait is None:
        raise ValueError('Trait clause lacks its compiler declaration')
    if (trait['generics'].get('regions')
            or trait['generics'].get('const_generics')
            or trait['generics'].get('trait_type_constraints')):
        raise ValueError('Unsupported dependent trait-law arguments')
    types = type_only_trait_arguments(reference['generics'], len(trait['generics']['types']))
    return {'rust': name(trait['item_meta']),
            # The original AST has an item binder outside the (empty)
            # RegionBinder. unbind_item_vars makes these Free in final LLBC.
            'arguments': [simple_type(t, crate, 1) for t in types],
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


def default_type_arguments(arguments, crate, bound_depth):
    """Read the restricted type application without discarding other arguments."""
    if (not isinstance(arguments, dict)
            or set(arguments) != {'regions', 'types', 'const_generics', 'trait_refs'}
            or arguments['regions'] or arguments['const_generics']):
        raise ValueError('Unsupported default-method type application')
    return [simple_type(t, crate, bound_depth) for t in arguments['types']]


def default_trait_application(reference, crate, bound_depth):
    if (not isinstance(reference, dict) or set(reference) != {'regions', 'skip_binder'}
            or reference['regions']):
        raise ValueError('Unsupported default-method dictionary binder')
    reference = reference['skip_binder']
    if not isinstance(reference, dict) or set(reference) != {'id', 'generics'}:
        raise ValueError('Missing default-method dictionary application')
    arguments = reference['generics']
    if arguments['trait_refs']:
        raise ValueError('Unsupported default-method nested dictionary')
    return {'id': reference['id'],
            'arguments': default_type_arguments(arguments, crate, bound_depth)}


def default_method_owner(annotation, function, final, before):
    """Recover only the enclosing trait's compiler-identified default bound.

    Charon can remove an unused Self dictionary from a provided method. The
    body then remains independent of the dictionary's operations, but its
    specification still needs the trait's promise. Preserve that promise as a
    specification parameter; never add it to the extracted Rust input prefix.
    """
    source = function.get('src')
    source = source.get('TraitDefault') if isinstance(source, dict) else None
    proposed = annotation.get('default_trait')
    if source is None:
        if proposed:
            raise ValueError('Source default method lacks its compiler trait owner')
        return None
    if not proposed or before is None:
        raise ValueError('Default method requires source and original compiler ownership')
    if (not isinstance(source, dict) or set(source) != {'trait_ref', 'item_id'}
            or not isinstance(source['trait_ref'], dict)
            or set(source['trait_ref']) != {'id', 'generics'}):
        raise ValueError('Default method lacks its compiler trait application')
    originals = declarations(before, 'fun_decls')
    original = originals.get(function['def_id'])
    old_source = original.get('src') if original else None
    old_source = old_source.get('TraitDefault') if isinstance(old_source, dict) else None
    trait = declarations(final, 'trait_decls').get(source['trait_ref']['id'])
    old_trait = declarations(before, 'trait_decls').get(source['trait_ref']['id'])
    if (not isinstance(old_source, dict) or set(old_source) != {'trait_ref', 'item_id'}
            or not isinstance(old_source['trait_ref'], dict)
            or set(old_source['trait_ref']) != {'id', 'generics'}
            or trait is None or old_trait is None
            or original['item_meta']['name'] != function['item_meta']['name']
            or old_source['item_id'] != source['item_id']
            or old_source['trait_ref']['id'] != source['trait_ref']['id']
            or name(trait['item_meta']) != 'zerocopy::' + proposed
            or old_trait['item_meta']['name'] != trait['item_meta']['name']):
        raise ValueError('Default method changed its enclosing Rust trait')
    source_args = source['trait_ref']['generics']
    old_args = old_source['trait_ref']['generics']
    arguments = default_type_arguments(source_args, final, 0)
    old_arguments = default_type_arguments(old_args, before, 0)
    if (source_args['trait_refs'] or old_args['trait_refs']
            or arguments != old_arguments
            or arguments != [['parameter', i] for i in range(len(trait['generics']['types']))]):
        raise ValueError('Unsupported default-method trait instantiation')
    for owner, crate_function, crate in ((trait, function, final), (old_trait, original, before)):
        index = source['item_id']
        methods = owner['methods']
        if not isinstance(index, int) or not 0 <= index < len(methods) or methods[index] is None:
            raise ValueError('Default method lacks its original trait method slot')
        method = methods[index]
        declared = method['skip_binder'].get('default')
        if (method['kind'] != {'TraitMethod': [owner['def_id'], index]}
                or declared is None or declared.get('id') != crate_function['def_id']
                or method['skip_binder']['item_meta']['name'] != crate_function['item_meta']['name']):
            raise ValueError('Default method does not implement its declared trait slot')
        application = declared['generics']
        if default_type_arguments(application, crate, 1) != arguments:
            raise ValueError('Default method slot changed its original type application')
        self_clauses = [c for c in crate_function['generics']['trait_clauses']
                        if c.get('origin') == 'TraitSelf']
        references = application['trait_refs']
        if self_clauses:
            reference = unwrap(references[0]) if len(references) == 1 else {}
            if (reference.get('kind') != 'SelfId'
                    or default_trait_application(reference['trait_decl_ref'], crate, 2)
                       != {'id': owner['def_id'], 'arguments': arguments}):
                raise ValueError('Default method slot lost its original Self dictionary')
        elif references:
            raise ValueError('Default method slot gained a Self dictionary')
    return {'rust': name(trait['item_meta']), 'arguments': arguments,
            'trait_def_id': trait['def_id'], 'method_id': source['item_id']}


def check_function_bounds(annotation, function, final, before, annotated_traits):
    """Compare semantic applications, never pre/post clause ordinals."""
    if function['generics'].get('trait_type_constraints'):
        raise ValueError('Associated-type constraints in trait roots are unsupported')
    after = retained_clauses(function, final, annotated_traits)
    owner = default_method_owner(annotation, function, final, before)
    if not after and not annotation.get('trait_bounds') and owner is None:
        return []
    if before is None:
        raise ValueError('Generic trait roots require the original admission AST')
    originals = [f for f in before.get('fun_decls', []) if f
                 and f['item_meta']['name'] == function['item_meta']['name']]
    if len(originals) != 1:
        raise ValueError('Generic trait root lacks an unambiguous original compiler owner')
    original = originals[0]
    if original['generics'].get('trait_type_constraints'):
        raise ValueError('Associated-type constraints in original trait roots are unsupported')
    if original['item_meta']['span'] != function['item_meta']['span']:
        raise ValueError('Generic trait root changed its original compiler source owner')
    original_names = [p['name'] for p in original['generics']['types']]
    final_names = [p['name'] for p in function['generics']['types']]
    if original_names != final_names or final_names != annotation['generics']:
        raise ValueError('Associated-type lifting changed the source generic prefix')
    original_predicates = [predicate(c, before)
                           for c in original['generics'].get('trait_clauses', [])]
    expected = [p for p in original_predicates if p['rust'] not in MARKERS]
    if owner:
        self_clauses = [predicate(c, before) for c in original['generics']['trait_clauses']
                        if c.get('origin') == 'TraitSelf']
        if len(self_clauses) != 1 or key(self_clauses[0]) != key(owner):
            raise ValueError('Default method lacks its original enclosing Self bound')
        # Only this exact, unused Self clause may disappear. All other bounds
        # must survive the normal semantic-application comparison below.
        if not any(key(p) == key(owner) for p in after):
            expected.remove(self_clauses[0])
            annotation['erased_self_bound'] = owner
    erased_laws = [p for p in original_predicates
                   if p['rust'] in MARKERS and p['rust'] in annotated_traits]
    if erased_laws or Counter(map(key, expected)) != Counter(map(key, after)):
        raise ValueError('Trait normalization lost or changed a required source bound')
    check_source_bounds(annotation, original_predicates)
    return after


def check_source_bounds(annotation, original_predicates):
    """Resolve source bound subjects and arities through original native clauses."""
    # Source syntax is only a proposed location/name. The resolved pre-AST
    # applications must explain every written bound on an original type variable.
    for bound in annotation.get('trait_bounds', []):
        if bound['subject'] not in annotation['generics']:
            raise ValueError('Source trait bound requires an original type-variable subject')
        index = annotation['generics'].index(bound['subject'])
        argument_count = bound.get('argument_count', 0)
        if type(argument_count) is not int or argument_count < 0:
            raise ValueError('Source trait bound has an invalid type argument count')
        candidates = [p for p in original_predicates
                      if len(p['arguments']) == argument_count + 1
                      and p['arguments'][0] == ['parameter', index]
                      and (p['rust'] == bound['trait']
                           or p['rust'].endswith('::' + bound['trait']))]
        if (not candidates and argument_count == 0
                and bound['trait'] in {'Sized', 'core::marker::Sized'}):
            # The admitted compiler preset hides this builtin marker. Any
            # same-spelled user trait still has a resolved dictionary above.
            continue
        if len(candidates) != 1:
            raise ValueError('Source trait bound lacks an exact resolved compiler application')


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
        if (trait['generics'].get('regions') or trait['generics'].get('const_generics')
                or trait['generics'].get('trait_type_constraints') or trait.get('types')
                or [p['name'] for p in trait['generics']['types']] != annotation['generics']):
            raise ValueError('Trait invariant requires original type-only parameters without associated types')
        original = declarations(before, 'trait_decls').get(ident) if before else None
        if (original is None or original['item_meta']['name'] != trait['item_meta']['name']
                or original.get('types') or original['generics'].get('trait_type_constraints')
                or original['generics'].get('regions') or original['generics'].get('const_generics')
                or [p['name'] for p in original['generics']['types']] != annotation['generics']):
            raise ValueError('Trait invariant requires an original trait without associated types')
        original_bounds = retained_clauses(original, before, trait_annotations)
        final_bounds = retained_clauses(trait, final, trait_annotations)
        if Counter(map(key, original_bounds)) != Counter(map(key, final_bounds)):
            raise ValueError('Trait generic normalization lost or changed a required dictionary law')
        original_parents = [predicate(c, before) for c in original.get('implied_clauses', [])]
        final_parents = [predicate(c, final) for c in trait.get('implied_clauses', [])]
        check_source_bounds(annotation, [predicate(c, before)
            for c in original['generics'].get('trait_clauses', [])] + original_parents)
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
    used_proofs, marked_owners = set(), set()
    for ident, implementation in declarations(final, 'trait_impls').items():
        law = by_id.get(implementation['impl_trait']['id'])
        if law is None or implementation['item_meta'].get('is_local') is not True:
            continue
        entry = native_impls.get(ident)
        if entry is None:
            raise ValueError('An annotated trait implementation lacks its native dictionary')
        generics = implementation['generics']
        if generics.get('regions') or generics.get('trait_type_constraints'):
            raise ValueError('Unsupported generic trait-law implementation')
        original = declarations(before, 'trait_impls').get(ident) if before else None
        if (original is None or original['item_meta']['span'] != implementation['item_meta']['span']
                or original['item_meta']['name'] != implementation['item_meta']['name']
                or original['item_meta'].get('is_local') is not True
                or original['impl_trait']['id'] != implementation['impl_trait']['id']
                or name(declarations(before, 'trait_decls')[original['impl_trait']['id']]['item_meta'])
                   != law['rust']):
            raise ValueError('Trait implementation lacks its original compiler owner')
        if original['generics'].get('regions') or original['generics'].get('trait_type_constraints'):
            raise ValueError('Unsupported original generic trait-law implementation')
        const_parameters = usize_const_parameters(generics)
        if const_parameters != usize_const_parameters(original['generics']):
            raise ValueError('Trait implementation normalization changed its original const parameters')
        if ([p['name'] for p in original['generics']['types']]
                != [p['name'] for p in generics['types']]
                or Counter(map(key, retained_clauses(original, before, trait_annotations)))
                != Counter(map(key, retained_clauses(implementation, final, trait_annotations)))):
            raise ValueError('Trait implementation normalization changed its required dictionaries')
        arguments = type_only_trait_arguments(
            implementation['impl_trait']['generics'], law['generic_count'])
        original_arguments = type_only_trait_arguments(
            original['impl_trait']['generics'], law['generic_count'])
        types = [simple_type(t, final) for t in arguments]
        original_types = [simple_type(lift_original_type(t, before, final), before)
                          for t in original_arguments]
        check_application_parameters(types, len(generics['types']), len(const_parameters))
        check_application_parameters(original_types, len(original['generics']['types']), len(const_parameters))
        if types != original_types:
            raise ValueError('Trait implementation lost its original Rust type application')
        span = unwrap(implementation['item_meta']['span'])
        file = next(f for f in final['files'] if f and f['id'] == span['data']['file_id'])
        matching = [p for p in getattr(annotations, 'trait_proofs', [])
                    if ((p.get('macro_input') and p.get('native_trait_impl_id') == ident)
                    or (not p.get('macro_input')
                    and file['name'] == {'Local': p['file'].removeprefix('zerocopy/')}
                    and span['data']['beg'] == {'line': p['open_line'], 'col': p['open_col']}
                    and span['data']['end'] == {'line': p['end_line'], 'col': p['end_col']}))]
        if len(matching) > 1:
            raise ValueError('Ambiguous source implementation proof binding')
        # Names come from the actual extracted dictionary, never an authored
        # marker. The marker only requests this exact owner's obligation.
        proof = entry['lean_name'].removeprefix('Zerocopy.') + '_law'
        if matching:
            marker = matching[0]
            if (not marker.get('macro_input')
                    and (marker['generics'] != [p['name'] for p in generics['types']]
                    or marker['const_generics'] != [p['name'] for p in const_parameters])):
                raise ValueError('Implementation marker disagrees with its resolved Rust owner')
            if (original['item_meta'].get('started_from') is not True
                    or implementation['item_meta'].get('started_from') is not True):
                raise ValueError('Implementation marker did not independently request extraction')
            used_proofs.add((matching[0]['file'], matching[0]['syntax']))
            marked_owners.add(ident)
        implementations.append({'def_id': ident, 'trait_def_id': law['def_id'],
            'dictionary': entry['lean_name'], 'law': law['law'],
            'proof': 'Zerocopy.Proofs.' + proof, 'rust_type': types,
            'generic_count': len(generics['types']),
            'const_parameters': const_parameters, 'const_count': len(const_parameters),
            'dictionary_count': len(retained_clauses(implementation, final, trait_annotations))})
    if used_proofs != {(p['file'], p['syntax']) for p in getattr(annotations, 'trait_proofs', [])}:
        raise ValueError('An annotated implementation proof was not bound and checked')
    # Source roots and dependency dictionaries have different coverage rules.
    # A function-root prefix can also select a nested implementation of an
    # unannotated trait (for example a static assertion's private trait). Such
    # dependencies are not invariant-proof markers. Restrict the root bijection
    # to annotated traits; every local dictionary of those traits, including
    # unmarked dependencies, still receives its proof obligation above.
    for crate in (before, final):
        rooted = {ident for ident, impl in declarations(crate, 'trait_impls').items()
                  if impl['item_meta'].get('started_from') is True
                  and impl['impl_trait']['id'] in by_id}
        if rooted != marked_owners:
            raise ValueError('Compiler implementation roots disagree with bound markers')
    return laws, implementations, dictionaries
