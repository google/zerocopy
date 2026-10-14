# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Validate the pinned native storage shapes before requesting Lean decoders.

Layout and byte validity are separate facts. These checks establish the native
wrapper-to-payload layout bridge; Lean maps the child's physical decoder without
using the optional mathematical admission decoder to restrict its domain.
"""
import copy


_BYTE_WIDTHS = {'U16': 2, 'U32': 4, 'U64': 8, 'U128': 16, 'Usize': 8,
                'I16': 2, 'I32': 4, 'I64': 8, 'I128': 16, 'Isize': 8,
                'F32': 4, 'F64': 8}
_SINGLE = {'zerocopy::wrappers::Unalign': ('_0', False),
           'zerocopy::wrappers::read_only_def::ReadOnly': ('inner', True),
           'core::num::wrapping::Wrapping': ('_0', True)}
_PHANTOM = 'core::marker::PhantomData'


def _name(declaration):
    parts = declaration['item_meta']['name']
    if any(set(part) != {'Ident'} or part['Ident'][1] != 0 for part in parts):
        return None
    return '::'.join(part['Ident'][0] for part in parts)


def _constant(number):
    return {'Untagged': {'Constant': {'Untagged': [
        {'Integer': {'Unsigned': ['Usize', str(number)]}},
        {'Untagged': {'Scalar': {'Integer': {'Unsigned': 'Usize'}}}}]}}}


def _typevar():
    return {'Untagged': {'TypeVar': {'Free': 0}}}


def _require(condition, owner, detail):
    if not condition:
        raise ValueError(f'Physical wrapper shape changed for {owner}: {detail}')


def _ownership(declaration, owner):
    metadata = declaration['item_meta']
    local = owner.startswith('zerocopy::')
    _require(metadata.get('is_local') is local
             and metadata.get('opacity') == ('Transparent' if local else 'Foreign')
             and metadata.get('has_errors') is False,
             owner, 'native local/foreign carrier ownership')


def _generics(declaration, owner):
    generics = declaration['generics']
    _require(len(generics['types']) == 1 and generics['types'][0]['index'] == 0,
             owner, 'one original type parameter required')
    _require(all(not generics[key] for key in ('regions', 'const_generics',
        'trait_clauses', 'regions_outlive', 'types_outlive', 'trait_type_constraints')),
        owner, 'unsupported generic constraints')


def _repr(declaration, owner, transparent):
    expected = {'repr_algo': 'Rust' if transparent else 'C',
                'align_modif': None if transparent else {'Pack': 1},
                'transparent': transparent, 'explicit_discr_type': None}
    layouts = declaration.get('layout', [])
    _require(bool(layouts), owner, 'native layout unavailable')
    _require(all(row['value'].get('repr') == expected for row in layouts),
             owner, 'native repr must be transparent or C packed(1) as supported')


def _phantom(declaration):
    _require(declaration is not None, _PHANTOM, 'missing carrier')
    _ownership(declaration, _PHANTOM)
    _generics(declaration, _PHANTOM)
    _require(declaration['kind'] == {'Struct': []}, _PHANTOM, 'stored fields')
    layouts = declaration.get('layout', [])
    _require(bool(layouts), _PHANTOM, 'native layout unavailable')
    for row in layouts:
        layout = row['value']
        _require(layout['size']['chosen'] == _constant(0)
                 and layout['align']['chosen'] == _constant(1),
                 _PHANTOM, 'must be size zero, alignment one')


def _identity(declaration):
    # Full native generic, field, repr and layout evidence must survive lowering.
    return {key: copy.deepcopy(declaration[key]) for key in
            ('def_id', 'item_meta', 'generics', 'kind', 'layout')}


def _lowering_identity(declaration):
    # Charon frees the outer binder and adds derived layout guarantees. Compare
    # original native observations; derived guarantees do not supply the bridge.
    def normalize(value):
        if isinstance(value, list):
            return [normalize(x) for x in value]
        if not isinstance(value, dict):
            return value
        if set(value) == {'And'} and len(value['And']) == 1:
            return normalize(value['And'][0])['Untagged']
        if value == {'TypeVar': {'Bound': [0, 0]}}:
            return {'TypeVar': {'Free': 0}}
        return {key: normalize(child) for key, child in value.items()
                if key != 'guarantee'}
    return normalize(_identity(declaration))


def validate_physical_wrapper_plans(final, before=None):
    """Return supported native plans keyed by Rust owner; reject changed shapes.

    Inputs are the translated LLBC/ULLBC objects, not the outer JSON document.
    Only documented owners are eligible: other transparent or zero-size types
    do not acquire byte semantics by structural resemblance.
    """
    declarations = {name: declaration for declaration in final['type_decls']
                    if declaration is not None and (name := _name(declaration))}
    old = ({_name(d): d for d in before['type_decls'] if d is not None}
           if before is not None else None)
    plans = {}
    for owner, declaration in declarations.items():
        leaf = owner.removeprefix('zerocopy::byteorder::')
        byteorder = owner.startswith('zerocopy::byteorder::') and leaf in _BYTE_WIDTHS
        if owner not in _SINGLE and not byteorder:
            continue
        _ownership(declaration, owner)
        _generics(declaration, owner)
        fields = declaration['kind'].get('Struct') if isinstance(declaration['kind'], dict) else None
        _require(fields is not None, owner, 'structure required')
        _require(len(fields) == (2 if byteorder else 1), owner, 'field count')
        if byteorder:
            _repr(declaration, owner, True)
            phantom = declarations.get(_PHANTOM)
            _phantom(phantom)
            width = _BYTE_WIDTHS[leaf]
            expected_payload = {'Untagged': {'Array': [
                {'Untagged': {'Scalar': {'Integer': {'Unsigned': 'U8'}}}},
                _constant(width)['Untagged']['Constant'], None]}}
            expected_phantom = {'Untagged': {'Adt': {'id': phantom['def_id'],
                'generics': {'regions': [], 'types': [_typevar()],
                             'const_generics': [], 'trait_refs': []}, 'builtin': None}}}
            _require([(f['name'], f['is_positional'], f['ty']) for f in fields] ==
                     [('_0', True, expected_payload), ('_1', True, expected_phantom)],
                     owner, 'byte array and PhantomData fields')
        else:
            field_name, transparent = _SINGLE[owner]
            _repr(declaration, owner, transparent)
            _require(fields[0]['name'] == field_name and fields[0]['ty'] == _typevar()
                     and fields[0]['is_positional'] == (field_name == '_0'),
                     owner, 'original generic payload field')
        if old is not None:
            _require(owner in old and _lowering_identity(old[owner]) == _lowering_identity(declaration),
                     owner, 'whole/final native evidence differs')
            if byteorder:
                _require(_PHANTOM in old and _lowering_identity(old[_PHANTOM]) == _lowering_identity(phantom),
                         owner, 'whole/final PhantomData evidence differs')
        plans[owner] = {'kind': 'payload-wrapper', 'payload': 0,
                        'field': fields[0]['name'],
                        'phantom_fields': [1] if byteorder else [],
                        'native': _identity(declaration)}
    return plans


def physical_model_suffix(plan):
    if plan is None:
        return ''
    if plan.get('kind') != 'payload-wrapper' or plan.get('payload') != 0:
        raise ValueError('Unsupported physical model plan')
    return ' with_physical 0'
