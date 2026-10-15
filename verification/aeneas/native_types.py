# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Preserve concrete NonZero associated types across native Charon lifting.

The original resolved ZeroablePrimitive dictionary supplies NonZeroInner. Keep
that nominal type as an explicit argument; do not identify it with its primitive
Self type. Generic dictionaries and other associated-type carriers fail closed.
"""

from copy import deepcopy

NONZERO = 'core::num::nonzero::NonZero'
ZEROABLE = 'core::num::nonzero::ZeroablePrimitive'
ARG_FIELDS = ('regions', 'types', 'const_generics', 'trait_refs')
PARAM_FIELDS = ('regions', 'types', 'const_generics', 'trait_clauses',
                'regions_outlive', 'types_outlive', 'trait_type_constraints')
PRIMITIVES = {'Unsigned': {'U8', 'U16', 'U32', 'U64', 'U128', 'Usize'},
              'Signed': {'I8', 'I16', 'I32', 'I64', 'I128', 'Isize'}}


def _require(condition, reason):
    if not condition:
        raise ValueError('Native associated-type preservation: ' + reason)


def _plain(value):
    if isinstance(value, dict):
        if set(value) == {'Untagged'}:
            return _plain(value['Untagged'])
        if set(value) == {'Value'}:
            return _plain(value['Value'][1])
        _require('Deduplicated' not in value, 'deduplicated AST is unsupported')
        return {key: _plain(child) for key, child in value.items()}
    if isinstance(value, list):
        return [_plain(child) for child in value]
    return value


def _name(declaration):
    parts = declaration['item_meta']['name']
    _require(all(set(part) == {'Ident'} and part['Ident'][1] == 0 for part in parts),
             'unsupported nominal identity')
    return '::'.join(part['Ident'][0] for part in parts)


def _index(crate, group):
    result = {}
    for declaration in crate.get(group, []):
        if declaration is not None:
            ident = declaration['def_id']
            _require(type(ident) is int and ident >= 0 and ident not in result,
                     'duplicate or invalid declaration id')
            result[ident] = declaration
    return result


def _empty(value, fields):
    return isinstance(value, dict) and set(value) == set(fields) and all(
        value[field] == [] for field in fields)


def _args(types):
    return {'regions': [], 'types': types, 'const_generics': [], 'trait_refs': []}


def lift_original_type(value, before, final):
    """Return the source type with its exact native associated argument appended.

    This mirrors expand_associated_types.rs lookup_path_on_trait_ref/update_generics
    for the supported concrete, binder-free dictionary: substitution is empty.
    The caller still compares the complete lifted original application with final
    LLBC and checks the generated dictionary's law in Lean.
    """
    types = _index(before, 'type_decls')
    final_types = _index(final, 'type_decls')
    traits = _index(before, 'trait_decls')
    final_traits = _index(final, 'trait_decls')
    impls = _index(before, 'trait_impls')
    final_impls = _index(final, 'trait_impls')

    def lift(current):
        current = _plain(current)
        if not isinstance(current, dict) or len(current) != 1:
            return current
        if 'Array' in current or 'Slice' in current:
            kind = 'Array' if 'Array' in current else 'Slice'
            sequence = deepcopy(current[kind])
            sequence[0] = lift(sequence[0])
            return {kind: sequence}
        if 'Adt' not in current:
            return current
        body = deepcopy(current['Adt'])
        args = body['generics']
        args['types'] = [lift(child) for child in args['types']]
        declaration = types.get(body['id']) if body.get('builtin') is None else None
        if declaration is None or _name(declaration) != NONZERO:
            return {'Adt': body}  # Existing source-type checks reject other trait refs.
        _require(sum(d['item_meta']['name'] == declaration['item_meta']['name']
                     for d in types.values()) == 1,
                 'ambiguous NonZero identity')
        original_params = declaration['generics']
        _require(len(original_params['types']) == 1
                 and original_params['types'][0]['index'] == 0
                 and original_params['types'][0]['name'] == 'T'
                 and all(original_params[key] == [] for key in PARAM_FIELDS
                         if key not in ('types', 'trait_clauses'))
                 and len(original_params['trait_clauses']) == 1,
                 'unsupported NonZero declaration arity or bounds')
        clause = original_params['trait_clauses'][0]
        predicate = _plain(clause['trait_'])
        _require(clause['clause_id'] == 0 and predicate['regions'] == [],
                 'unsupported NonZero clause binder')
        trait_id = predicate['skip_binder']['id']
        trait = traits.get(trait_id)
        _require(trait is not None and _name(trait) == ZEROABLE
                 and sum(d['item_meta']['name'] == trait['item_meta']['name']
                         for d in traits.values()) == 1,
                 'NonZero bound is not the native ZeroablePrimitive trait')
        _require(predicate['skip_binder']['generics'] == _args([{'TypeVar': {'Bound': [1, 0]}}]),
                 'NonZero bound changed its original Self parameter')
        _require(len(trait['generics']['types']) == 1
                 and trait['generics']['types'][0]['index'] == 0
                 and trait['generics']['types'][0]['name'] == 'Self'
                 and all(trait['generics'][key] == [] for key in PARAM_FIELDS if key != 'types'),
                 'unsupported native trait arity or bounds')
        _require(len(trait['types']) == 1 and trait['types'][0] is not None,
                 'unknown or ambiguous associated-type slot')
        slot = trait['types'][0]
        _require(slot['kind'] == {'TraitType': [trait_id, 0]}
                 and _empty(slot['params'], PARAM_FIELDS)
                 and slot['skip_binder']['name'] == 'NonZeroInner'
                 and slot['skip_binder'].get('default') is None,
                 'unsupported associated-type identity or binder')
        _require(set(args) == set(ARG_FIELDS) and not args['regions']
                 and not args['const_generics'] and len(args['types']) == 1
                 and len(args['trait_refs']) == 1,
                 'unsupported NonZero application arity')
        self_type = args['types'][0]
        scalar = self_type.get('Scalar', {}).get('Integer', {})
        _require(len(scalar) == 1 and next(iter(scalar)) in PRIMITIVES
                 and next(iter(scalar.values())) in PRIMITIVES[next(iter(scalar))],
                 'NonZero Self is not a supported concrete integer')
        reference = _plain(args['trait_refs'][0])
        _require(set(reference['kind']) == {'TraitImpl'}, 'unresolved NonZero dictionary')
        instance = reference['kind']['TraitImpl']
        _require(_empty(instance['generics'], ARG_FIELDS), 'generic dictionary substitution is unsupported')
        _require(reference['trait_decl_ref'] == {'regions': [], 'skip_binder': {
            'id': trait_id, 'generics': _args([self_type])}}, 'dictionary reference changed trait or Self')
        dictionary = impls.get(instance['id'])
        _require(dictionary is not None and not dictionary['is_negative']
                 and _empty(dictionary['generics'], PARAM_FIELDS)
                 and _plain(dictionary['impl_trait']) == {'id': trait_id, 'generics': _args([self_type])},
                 'resolved dictionary changed trait, Self, polarity or arity')
        _require(len(dictionary['types']) == 1 and dictionary['types'][0] is not None,
                 'resolved dictionary lacks its unique associated type')
        resolved = dictionary['types'][0]
        _require(resolved['kind'] == {'TraitType': [trait_id, 0]}
                 and _empty(resolved['params'], PARAM_FIELDS), 'associated dictionary slot or binder changed')
        inner = _plain(resolved['skip_binder']['value'])
        inner_adt = inner.get('Adt', {})
        inner_decl = types.get(inner_adt.get('id'))
        _require(inner_adt.get('builtin') is None and _empty(inner_adt.get('generics'), ARG_FIELDS)
                 and inner_decl is not None and _empty(inner_decl['generics'], PARAM_FIELDS)
                 and _name(inner_decl) in {f'core::num::niche_types::NonZero{primitive}Inner'
                                          for primitives in PRIMITIVES.values()
                                          for primitive in primitives},
                 'associated type is unknown, recursive or outside native niche types')
        # Preserve exact compiler identities, including the original dictionary;
        # final arguments may extend its prefix only by this resolved nominal type.
        final_dict = final_impls.get(instance['id'])
        final_nominal = final_types.get(body['id'])
        final_trait = final_traits.get(trait_id)
        _require(final_dict is not None and final_nominal is not None and final_trait is not None,
                 'final extraction omitted an original native declaration')
        for original, changed in [(dictionary, final_dict), (declaration, final_nominal),
                                  (trait, final_trait), (inner_decl, final_types.get(inner_decl['def_id']))]:
            _require(changed is not None
                     and original['item_meta']['name'] == changed['item_meta']['name']
                     and original['item_meta']['span'] == changed['item_meta']['span'],
                     'final extraction changed an original native owner')
        _require(final_dict['generics'] == dictionary['generics']
                 and final_dict['is_negative'] == dictionary['is_negative']
                 and final_dict['types'] == [None]
                 and _plain(final_dict['impl_trait']) == {
                     'id': trait_id, 'generics': _args([self_type, inner])},
                 'final dictionary changed its original Self or associated type')
        _require(final_trait['types'] == [None]
                 and len(final_trait['generics']['types']) == 2
                 and final_trait['generics']['types'][0] == trait['generics']['types'][0]
                 and final_trait['generics']['types'][1]['index'] == 1
                 and final_trait['generics']['types'][1]['name'] == 'Self_NonZeroInner'
                 and all(final_trait['generics'][key] == [] for key in PARAM_FIELDS if key != 'types')
                 and len(final_nominal['generics']['types']) == 2
                 and final_nominal['generics']['types'][0] == original_params['types'][0]
                 and final_nominal['generics']['types'][1]['index'] == 1
                 and final_nominal['generics']['types'][1]['name'] == 'Clause0_NonZeroInner'
                 and all(final_nominal['generics'][key] == [] for key in PARAM_FIELDS if key != 'types'),
                 'unexpected native associated-type lifting shape')
        args['types'].append(inner)
        args['trait_refs'] = []
        return {'Adt': body}

    return lift(value)
