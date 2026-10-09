#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Reject unreviewed execution before Aeneas can erase its effects.

This checker admits the pinned value-and-borrow fragment, not arbitrary memory
operations. Its correspondence premises are documented in LOWERING_AUDIT.md. In
particular, valid incoming references and the reviewed borrow translation are
premises; neither is inferred from a list of bytes. Storage-producing operations
are exact registered leaves with guards, rather than unchecked carrier casts.

The traversal starts at every bound specification. Annotation status never
exempts a callee. Unknown constructors, indirect calls, drops, and raw storage
observations fail closed. The report identifies the inspected LLBC and selected
interpretations; it is evidence of this inspection, not a proof of rustc.
"""

import argparse
import hashlib
import json
import os
import re
from pathlib import Path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def untag(value):
    # Disable serialization sharing in the extraction command. Different AST
    # domains reuse deduplication indices; guessing their domain is unsafe.
    if isinstance(value, dict) and set(value) == {'Untagged'}:
        return value['Untagged']
    return value


def variant(value):
    value = untag(value)
    if isinstance(value, str):
        return value, None
    if isinstance(value, dict) and len(value) == 1:
        return next(iter(value.items()))
    raise ValueError(f'Invalid LLBC variant: {value!r}')


def fields(value, expected):
    if not isinstance(value, dict) or set(value) != set(expected.split()):
        raise ValueError(f'Unreviewed LLBC fields: expected {expected}, got {value!r}')


class Admission:
    def __init__(self, data, registry):
        if data.get('has_errors') is not False or data.get('charon_version') != '0.1.276':
            raise ValueError('Admission requires successful LLBC from the reviewed Charon schema')
        self.crate = data['translated']
        self.functions = {f['def_id']: f for f in self.crate['fun_decls'] if f}
        self.types = {t['def_id']: t for t in self.crate['type_decls'] if t}
        self.registry = registry
        self.visited = {}
        self.calls = []
        self.globals = set()
        self.current = None
        self.locals = {}
        self.checked_types = set()
        options = self.crate['options']
        targets = self.crate['target_information']
        if (len(targets) != 1 or targets[0]['value']['target_pointer_size'] != 8 or
                targets[0]['value']['is_little_endian'] is not True):
            raise ValueError('Admission currently requires a little-endian 64-bit target')
        # Review the whole option profile. A new Charon flag must not silently
        # enable an erasure just because the old subset of flags still matches.
        required = dict.fromkeys("""ullbc precise_drops monomorphize
            start_from_pub extract_opaque_bodies translate_all_methods
            eager_vtables duplicate_defaulted_methods no_doc_comments
            remove_unused_clauses desugar_drops resugar_drops detect_drop_flags
            raw_consts unsized_strings print_original_ullbc print_ullbc
            print_built_llbc print_llbc print_layouts no_serialize skip_borrowck
            erase_body_lifetimes no_typecheck no_normalize no_reorder_decls
            no_compute_layout_guarantees""".split(), False)
        required.update(dict.fromkeys("""hide_marker_traits hide_allocator
            remove_unused_self_clauses remove_adt_clauses ops_to_function_calls
            index_to_function_calls treat_box_as_builtin no_gen_tuple_structs
            reconstruct_fallible_operations reconstruct_asserts
            reconstruct_matches deallocate_all_locals unbind_item_vars
            no_dedup_serialized_ast abort_on_error error_on_warnings""".split(), True))
        required.update(dict.fromkeys("""rustc_args targets start_from_if_exists
            start_from_attribute include exclude""".split(), []))
        required.update(dict.fromkeys('monomorphize_mut consts dest_dir format'.split(), None))
        required.update(preset='Aeneas', mir='Promoted', sysroot='default',
                        lift_associated_types=['*'])
        if set(options) != set(required) | {'start_from', 'opaque', 'dest_file'}:
            raise ValueError('Unreviewed extraction option fields')
        for key, expected in required.items():
            if options[key] != expected:
                raise ValueError(f'Unreviewed extraction option {key}: {options[key]!r}')
        stages = {variant(f['body'])[0] for f in self.functions.values()
                  if f['body'] != 'Opaque'}
        if len(stages) != 1 or not stages <= {'Unstructured', 'Structured'}:
            raise ValueError('Missing or mixed admission body stages')
        self.before = stages == {'Unstructured'}
        # Opaque selection comes only from the registry, never from arbitrary
        # command-line flags which could hide an unsafe local body.
        expected = sorted(row['rust'] for row in registry if row.get('opaque'))
        if sorted(options['opaque']) != expected:
            raise ValueError('Opaque selections disagree with the external interpretation registry')

    def name(self, name):
        parts = []
        for element in name:
            tag, body = variant(element)
            if tag == 'Ident' and body[1] == 0:
                parts.append(body[0])
            elif tag == 'Impl':
                if 'Ty' in body:
                    parts.append('{' + self.ty_name(body['Ty']['skip_binder']) + '}')
                elif 'Trait' in body:
                    # Preserve the exact trait implementation identity in the
                    # signature fingerprint below; display is only a lookup key.
                    impl = self.crate['trait_impls'][body['Trait']]['impl_trait']
                    trait = self.crate['trait_decls'][impl['id']]
                    args = impl['generics']['types']
                    parts.append('{' + self.name(trait['item_meta']['name']) +
                                 '<' + ','.join(self.ty_name(t) for t in args) + '>}')
                else:
                    raise ValueError('Unknown implementation identity')
            elif tag == 'Builtin' and isinstance(body[0], dict) and set(body[0]) == {'Tuple'}:
                parts.append('tuple' + str(body[0]['Tuple']))
            elif tag == 'Builtin' and body == ['Str', 0]:
                parts.append('str')
            else:
                raise ValueError(f'Unknown Rust identity component: {element}')
        return '::'.join(parts)

    def ty_name(self, ty):
        tag, body = variant(ty)
        if tag == 'Never':
            return '!'
        if tag == 'Scalar':
            if body == 'Bool':
                return 'bool'
            if isinstance(body, dict) and set(body) == {'Integer'}:
                signedness, width = variant(body['Integer'])
                if signedness not in {'Signed', 'Unsigned'} or width not in {
                        'I8', 'I16', 'I32', 'I64', 'I128', 'Isize',
                        'U8', 'U16', 'U32', 'U64', 'U128', 'Usize'}:
                    raise ValueError(f'Unreviewed integer {body}')
                return width.lower()
            raise ValueError(f'Unsupported scalar {body}')
        if tag == 'TypeVar':
            kind, index = variant(body)
            if kind == 'Free': return 'T' + str(index)
            if kind == 'Bound' and index[0] == 0: return 'T' + str(index[1])
            raise ValueError(f'Unreviewed type variable {body}')
        if tag == 'Adt':
            base = self.name(self.types[body['id']]['item_meta']['name'])
            args = body['generics']['types']
            if body['generics']['const_generics']:
                raise ValueError('Nominal const-generic value carriers are unsupported')
            self.check_type(body['id'])
            return base + ('<' + ','.join(self.ty_name(x) for x in args) + '>' if args else '')
        if tag in {'Slice', 'Array'}:
            suffix = '' if tag == 'Slice' else ';' + self.const_name(body[1])
            return '[' + self.ty_name(body[0]) + suffix + ']'
        if tag == 'Ref':
            if body[2] not in {'Shared', 'Mut'}:
                raise ValueError('Unreviewed reference mutability')
            return ('&mut ' if body[2] == 'Mut' else '&') + self.ty_name(body[1])
        raise ValueError(f'Unreviewed type {tag}; raw pointers and storage are not logical values')

    def const_name(self, value):
        value, _ = untag(value)
        tag, body = variant(value)
        if tag == 'Var':
            kind, index = variant(body)
            if kind == 'Free': return 'N' + str(index)
            if kind == 'Bound' and index[0] == 0: return 'N' + str(index[1])
            raise ValueError(f'Unreviewed const variable {body}')
        if tag == 'Integer':
            return next(iter(body.values()))[1]
        raise ValueError(f'Unreviewed const-generic expression {tag}')

    def check_type(self, index):
        if index in self.checked_types:
            return
        self.checked_types.add(index)
        declaration = self.types[index]
        kind, body = variant(declaration['kind'])
        name = self.name(declaration['item_meta']['name'])
        if kind == 'Opaque':
            if name not in {'tuple0', 'str', 'core::fmt::Arguments',
                            'core::fmt::Formatter', 'core::marker::PhantomData',
                            'core::num::nonzero::NonZero',
                            'core::num::niche_types::NonZeroUsizeInner'}:
                raise ValueError(f'Unreviewed opaque value carrier {name}')
            return
        if kind == 'Struct':
            children = body
        elif kind == 'Enum':
            children = [field for case in body for field in case['fields']]
        else:
            raise ValueError(f'Unreviewed value carrier {kind}: {name}')
        for field in children:
            self.ty_name(field['ty'])

    def prototype(self, function):
        sig = function['signature']
        fields(sig, 'is_unsafe abi is_variadic inputs output')
        if sig['abi'] != 'Rust' or sig['is_variadic']:
            raise ValueError('Unsupported ABI or variadic function')
        return {'unsafe': sig['is_unsafe'],
                'inputs': [self.ty_name(x) for x in sig['inputs']],
                'output': self.ty_name(sig['output']),
                'types': len(function['generics']['types']),
                'consts': len(function['generics']['const_generics'])}

    def visit(self, index):
        if index in self.visited:
            return
        function = self.functions.get(index)
        if function is None:
            raise ValueError(f'Missing executable dependency {index}')
        meta = function['item_meta']
        name = self.name(meta['name'])
        prototype = self.prototype(function)
        if meta['has_errors'] or meta['is_extern']:
            raise ValueError(f'Untranslated or foreign-ABI dependency {name}')
        for attribute in meta['attr_info']['attributes']:
            kind, detail = variant(attribute)
            if kind == 'DocComment':
                continue
            if kind == 'Builtin':
                tag, _ = variant(detail)
                if tag in {'Inline', 'TrackCaller'}:
                    continue
            elif kind == 'Unknown':
                fields(detail, 'path args')
                if detail['path'] in {'allow', 'warn', 'deny', 'forbid',
                        'must_use', 'cold', 'deprecated', 'doc', 'cfg', 'cfg_attr'}:
                    continue
            raise ValueError(f'Unreviewed function attribute {kind} on {name}')
        matches = []
        for row in self.registry:
            selected = row.get('before', row) if self.before else row
            if selected['rust'] == name and selected['signature'] == prototype:
                matches.append(row)
        if matches:
            if len(matches) != 1:
                raise ValueError(f'External interpretation signature changed: {name}')
            # A builtin may replace a visible Rust body. Always select the
            # interpretation first, rather than approving the unused body.
            self.visited[index] = {'rust': name, 'origin': 'interpretation',
                                   'lean': matches[0]['lean']}
            return
        if function['body'] == 'Opaque' or meta['is_local'] is not True:
            raise ValueError(f'No reviewed interpretation for {name}')
        stage, body = variant(function['body'])
        if stage not in {'Structured', 'Unstructured'}:
            raise ValueError(f'Unknown body stage {stage}')
        fields(body, 'span bound_body_regions locals body comments')
        if self.contains_reference(function['signature']['output']):
            raise ValueError(f'Escaping borrow is unsupported: {name}')
        self.visited[index] = {'rust': name, 'origin': 'body'}
        previous = self.current, self.locals
        self.current = name
        self.locals = {local['index']: local for local in body['locals']['locals']}
        for local in self.locals.values():
            self.ty_name(local['ty'])
            if local['drop_flag_for'] is not None:
                raise ValueError(f'Conditional drop flag in {name}')
        try:
            if stage == 'Structured':
                self.block(body['body'])
            else:
                self.cfg(body['body'])
        except ValueError as error:
            raise ValueError(f'{name}: {error}') from error
        finally:
            self.current, self.locals = previous

    def contains_reference(self, value, seen=None):
        seen = set() if seen is None else seen
        tag, body = variant(value)
        if tag == 'Ref':
            return True
        if tag in {'Slice', 'Array'}:
            return self.contains_reference(body[0], seen)
        if tag == 'Adt':
            if any(self.contains_reference(t, seen) for t in body['generics']['types']):
                return True
            index = body['id']
            if index in seen:
                return False
            seen.add(index)
            kind, children = variant(self.types[index]['kind'])
            if kind == 'Enum':
                children = [field for case in children for field in case['fields']]
            if kind in {'Struct', 'Enum'}:
                return any(self.contains_reference(field['ty'], seen) for field in children)
        return False

    def assertion(self, assertion):
        fields(assertion, 'cond expected check_kind')
        if type(assertion['expected']) is not bool:
            raise ValueError('Unreviewed assertion polarity')
        self.operand(assertion['cond'])
        check = assertion['check_kind']
        if check is None:
            return
        tag, detail = variant(check)
        if tag == 'BoundsCheck':
            fields(detail, 'len index')
            operands = list(detail.values())
        elif tag == 'Overflow':
            # Charon uses this only for diagnostics; the preceding Boolean
            # computation contains the actual arithmetic check.
            self.rvalue({'BinaryOp': detail})
            return
        elif tag in {'OverflowNeg', 'DivisionByZero', 'RemainderByZero'}:
            operands = [detail]
        else:
            raise ValueError(f'Unreviewed assertion kind {tag}')
        for operand in operands:
            self.operand(operand)

    def abort(self, abort):
        tag, _ = variant(abort)
        # The pinned interpreter collapses source UB aborts into panic. Both
        # remain rejected by every admitted contract. No recovery or failure
        # handler is admitted; adding one requires preserving this distinction.
        if tag not in {'Panic', 'UndefinedBehavior'}:
            raise ValueError(f'Unreviewed abort {tag}')

    def place(self, place, indexed=False):
        fields(place, 'kind ty')
        self.ty_name(place['ty'])
        tag, body = variant(place['kind'])
        if tag == 'Local':
            if body not in self.locals:
                raise ValueError('Unknown local place')
        elif tag == 'Global':
            self.global_value(body['id'])
        elif tag == 'Projection':
            self.place(body[0], indexed)
            projection, detail = variant(body[1])
            if projection == 'Deref':
                if variant(body[0]['ty'])[0] != 'Ref':
                    raise ValueError('Dereference without a modeled reference')
            elif projection == 'PtrMetadata':
                if variant(body[0]['ty'])[0] != 'Ref':
                    raise ValueError('Metadata without a modeled reference')
            elif projection == 'Index' and indexed and self.before:
                fields(detail, 'offset from_end')
                if detail['from_end'] is not False or variant(body[0]['ty'])[0] not in {'Slice', 'Array'}:
                    raise ValueError('Unreviewed indexing base or direction')
                self.operand(detail['offset'])
            elif projection != 'Field':
                # Indexing must use a reviewed, guarded builtin. In particular,
                # PlaceMention cannot bypass its bounds check by being erased.
                raise ValueError(f'Unreviewed place projection {projection}')
        else:
            raise ValueError(f'Unsupported place {tag}')

    def global_value(self, index):
        if index in self.globals:
            return
        self.globals.add(index)
        global_ = self.crate['global_decls'][index]
        if global_['global_kind'] != 'NamedConst' or global_['item_meta']['has_errors']:
            raise ValueError('Unreviewed static or global origin')
        self.constant(global_['value'])

    def operand(self, operand):
        tag, body = variant(operand)
        if tag in {'Copy', 'Move'}:
            self.place(body, indexed=True)
        elif tag == 'Const':
            self.constant(body)
        else:
            raise ValueError(f'Unsupported operand {tag}')

    def constant(self, constant):
        value, ty = untag(constant)
        self.ty_name(ty)
        tag, body = variant(value)
        if tag == 'Opaque' and body == 'Missing metadata' and self.ty_name(ty) == 'tuple0':
            # Original Charon uses this exact unit token for absent thin-pointer
            # metadata. It is not a raw value or an unevaluated Rust constant.
            return
        if tag in {'Bool', 'Integer', 'Str', 'Discriminant'}:
            return
        if tag == 'Adt':
            for field in body[1]:
                self.constant(field)
            return
        if tag == 'Global':
            self.global_value(body['id'])
            return
        if tag == 'Call':
            function, args = body
            if variant(function['kind'])[0] != 'Fun':
                raise ValueError('Unresolved constant producer')
            for arg in args:
                self.constant(arg)
            self.visit(function['kind']['Fun'])
            return
        if tag == 'TraitConst':
            # Resolved dictionaries are traversed below; unresolved constants
            # cannot be treated as harmless data because their producer may run.
            self.dictionary(body[0])
            return
        raise ValueError(f'Unsupported constant {tag}; no raw-memory or CTFE placeholder')

    def dictionary(self, reference):
        # The pinned dictionaries explicitly name their implementations. A
        # type-variable clause is acceptable only for marker traits with no
        # executable methods; never for a callback chosen by a caller.
        reference = untag(reference)
        kind = reference['kind']
        tag, body = variant(kind)
        if tag == 'TraitImpl':
            index = body['id']
            impl = self.crate['trait_impls'][index]
            for method in impl['methods']:
                if method is not None:
                    self.visit(method['skip_binder']['id'])
        elif tag in {'BuiltinOrAuto', 'Clause'}:
            trait = self.crate['trait_decls'][reference['trait_decl_ref']['skip_binder']['id']]
            if trait['methods']:
                raise ValueError(f'Unresolved dictionary with executable methods {tag}')
            # Method-free dictionaries supply typed, evaluated constant data.
            # Compiler CTFE validity remains an explicit normalization premise.
            return
        else:
            raise ValueError(f'Unresolved executable dictionary {tag}')

    def rvalue(self, rvalue):
        tag, body = variant(rvalue)
        if tag == 'Use':
            self.operand(body[0])
            if body[1] not in {'Yes', 'No'}:
                raise ValueError('Unknown retag mode')
        elif tag == 'BinaryOp':
            op, mode = variant(body[0])
            if op not in {'BitXor', 'BitAnd', 'BitOr', 'Eq', 'Lt', 'Le', 'Ne', 'Ge', 'Gt',
                          'Add', 'Sub', 'Mul', 'Div', 'Rem', 'Shl', 'Shr',
                          'AddChecked', 'SubChecked', 'MulChecked'}:
                raise ValueError(f'Unreviewed binary operation {op}')
            if mode == 'UB' and op in {'Add', 'Mul'}:
                # Charon resugars these into the exact registered Usize leaves.
                # Require both operands to have that carrier; no generic or
                # signed unchecked arithmetic inherits this registration.
                for operand in body[1:]:
                    kind, value = variant(operand)
                    ty = value['ty'] if kind in {'Copy', 'Move'} else untag(value)[1]
                    if self.ty_name(ty) != 'usize':
                        raise ValueError('Unsupported unchecked arithmetic carrier')
                leaf = 'core::num::{usize}::unchecked_' + op.lower()
                if not any(row['rust'] == leaf for row in self.registry):
                    raise ValueError(f'No reviewed interpretation for {leaf}')
                self.calls.append({'caller': self.current, 'callee': leaf,
                                   'implicit': True})
            elif mode == 'UB' and op in {'Div', 'Rem'}:
                # Rust's preceding assertions guard these MIR operations. The
                # pinned backend additionally performs the divisor/overflow
                # checks; final LLBC must retain checked division/remainder.
                for operand in body[1:]:
                    kind, value = variant(operand)
                    ty = value['ty'] if kind in {'Copy', 'Move'} else untag(value)[1]
                    if not re.fullmatch(r'(u|i)(8|16|32|64|128|size)', self.ty_name(ty)):
                        raise ValueError('Unsupported division/remainder carrier')
            elif mode not in {None, 'Panic', 'Wrap'}:
                raise ValueError(f'Unreviewed arithmetic mode {mode}; use a guarded primitive')
            for operand in body[1:]:
                self.operand(operand)
        elif tag == 'UnaryOp':
            op, detail = variant(body[0])
            if op == 'Cast':
                cast, types = variant(detail)
                if cast == 'Unsize':
                    source, target, metadata = [untag(t) for t in types]
                    if set(source) != {'Ref'} or set(target) != {'Ref'}:
                        raise ValueError('Only array-reference to slice-reference unsizing is supported')
                    source, target = source['Ref'], target['Ref']
                    if source[2] != target[2] or source[2] not in {'Shared', 'Mut'}:
                        raise ValueError('Unreviewed unsizing mutability')
                    source, target = untag(source[1]), untag(target[1])
                    if (set(source) != {'Array'} or set(target) != {'Slice'} or
                            self.ty_name(source['Array'][0]) != self.ty_name(target['Slice'][0])):
                        raise ValueError('Unreviewed unsizing element or carrier')
                    if (not isinstance(metadata, dict) or set(metadata) != {'Length'} or
                            self.const_name(metadata['Length']) != self.const_name(source['Array'][1])):
                        raise ValueError('Unreviewed unsizing metadata')
                elif cast == 'Scalar':
                    for endpoint in types:
                        if not (endpoint == 'Bool' or isinstance(endpoint, dict)
                                and set(endpoint) == {'Integer'}):
                            raise ValueError(f'Unreviewed scalar cast endpoint {endpoint}')
                else:
                    raise ValueError(f'Unreviewed cast {cast}')
            elif op != 'Not' and not (op == 'Neg' and detail in {'Panic', 'Wrap'}):
                raise ValueError(f'Unreviewed unary operation {op}')
            self.operand(body[1])
        elif tag == 'Aggregate':
            kind, _ = variant(body[0])
            if kind not in {'Adt', 'Array'}:
                raise ValueError(f'Unreviewed aggregate {kind}')
            for operand in body[1]:
                self.operand(operand)
        elif tag == 'Discriminant':
            self.place(body)
        elif tag == 'Ref':
            fields(body, 'place kind ptr_metadata')
            if body['kind'] not in {'Shared', 'Mut', 'TwoPhaseMut', 'Shallow'}:
                raise ValueError('Unsupported reference kind')
            self.place(body['place'], indexed=True)
            if body['ptr_metadata'] is not None:
                self.operand(body['ptr_metadata'])
        else:
            raise ValueError(f'Unreviewed rvalue {tag}')

    def block(self, block, unwind=False):
        fields(block, 'span id statements')
        for statement in block['statements']:
            fields(statement, 'span id kind comments_before')
            tag, body = variant(statement['kind'])
            if unwind and tag not in {'StorageDead', 'UnwindResume', 'Abort', 'Nop'}:
                raise ValueError(f'Unclassified unwind effect {tag}')
            if tag in {'StorageLive', 'StorageDead', 'Nop', 'Return', 'Break', 'Continue'}:
                continue
            if tag == 'UnwindResume':
                if not unwind:
                    raise ValueError('UnwindResume on a normal path')
            elif tag == 'Assign':
                self.place(body[0]); self.rvalue(body[1])
            elif tag == 'PlaceMention':
                self.place(body)
            elif tag == 'Borrowck':
                kind, place = variant(body)
                if kind != 'FakeRead':
                    raise ValueError(f'Unreviewed borrow-checking statement {kind}')
                self.place(place)
            elif tag == 'Call':
                fields(body, 'call on_unwind')
                call = body['call']; fields(call, 'func args dest')
                category, fn = variant(call['func'])
                if category != 'Regular' or variant(fn['kind'])[0] != 'Fun':
                    raise ValueError('Unresolved trait, callback, or indirect call')
                fields(fn, 'kind generics')
                callee = fn['kind']['Fun']
                for operand in call['args']:
                    self.operand(operand)
                self.place(call['dest'])
                for ty in fn['generics']['types']:
                    self.ty_name(ty)
                for ref in fn['generics']['trait_refs']:
                    self.dictionary(ref)
                target = self.functions[callee]
                name = self.name(target['item_meta']['name'])
                if name == 'zerocopy::util::transmute_unchecked':
                    actual = [self.ty_name(ty) for ty in fn['generics']['types']]
                    if actual != ['u8', 'bool']:
                        raise ValueError(f'Unsupported transmute instantiation {actual}')
                self.calls.append({'caller': self.current, 'callee': name})
                self.visit(callee)
                self.block(body['on_unwind'], True)
            elif tag == 'Assert':
                fields(body, 'assert on_failure on_unwind')
                self.assertion(body['assert'])
                self.abort(body['on_failure'])
                self.block(body['on_unwind'], True)
            elif tag == 'Abort':
                self.abort(body)
            elif tag == 'Switch':
                fields(body, 'data branches')
                data = body['data']
                fields(data, 'scrutinee branches fallback')
                kind, scrutinee = variant(data['scrutinee'])
                if kind == 'Value':
                    self.operand(scrutinee)
                elif kind == 'Discriminant':
                    self.place(scrutinee)
                else:
                    raise ValueError(f'Unreviewed branch scrutinee {kind}')
                for value, index in data['branches']:
                    self.constant(value)
                    if not 0 <= index < len(body['branches']):
                        raise ValueError('Invalid branch target')
                if data['fallback'] is not None and not 0 <= data['fallback'] < len(body['branches']):
                    raise ValueError('Invalid fallback branch')
                for branch in body['branches']:
                    self.block(branch, unwind)
            elif tag == 'Loop':
                self.block(body, unwind)
            else:
                raise ValueError(f'Unreviewed statement {tag}; drops, assembly and padding observations are excluded')

    def cfg(self, blocks):
        """Inspect every original block, including dead and unwind blocks.

        Charon may later remove a dead block. Inspecting it is conservative and
        avoids relying on that pass to distinguish unreachable UB from a lost
        effect. Terminators are converted to the same operation checks used for
        LLBC; only control-flow edges and bookkeeping get separate treatment.
        """
        for block in blocks:
            fields(block, 'statements terminator')
            for stmt in block['statements']:
                fields(stmt, 'span kind comments_before')
                self.block({'span': stmt['span'], 'id': 0,
                            'statements': [dict(stmt, id=0)]})
            term = block['terminator']
            fields(term, 'span kind comments_before')
            tag, body = variant(term['kind'])
            if tag in {'Goto', 'Return', 'UnwindResume'}:
                continue
            if tag == 'Call':
                fields(body, 'call target on_unwind')
                body = {'call': body['call'], 'on_unwind':
                        {'span': term['span'], 'id': 0, 'statements': []}}
            elif tag == 'Assert':
                fields(body, 'assert target on_unwind')
                self.assertion(body['assert'])
                continue
            elif tag == 'Switch':
                fields(body, 'data branches')
                body = {'data': body['data'], 'branches': [
                    {'span': term['span'], 'id': 0, 'statements': []}
                    for _ in body['branches']]}
            elif tag != 'Abort':
                raise ValueError(f'Unreviewed original terminator {tag}; '
                                 'implicit drops and assembly must remain visible')
            self.block({'span': term['span'], 'id': 0, 'statements': [
                dict(term, id=0, kind={tag: body})]})

    def audit(self, roots):
        names = {}
        for index, function in self.functions.items():
            meta = function['item_meta']
            if not (meta['is_local'] and meta['started_from']):
                continue
            parts = meta['name']
            if len(parts) > 1 and 'Impl' in parts[-2]:
                impl = parts[-2]['Impl']
                if 'Ty' not in impl:
                    continue
                ty, adt = variant(impl['Ty']['skip_binder'])
                if ty != 'Adt':
                    continue
                name = self.name(self.types[adt['id']]['item_meta']['name']) + '::' + parts[-1]['Ident'][0]
            else:
                name = self.name(parts)
            names.setdefault(name, []).append(index)
        for root in roots:
            matches = names.get(root, [])
            if len(matches) != 1:
                raise ValueError(f'Missing or ambiguous specification root {root}')
            self.visit(matches[0])
        return {'roots': sorted(roots), 'executions': list(self.visited.values()),
                'calls': self.calls}


def input_identity(root):
    """Bind inspection to source, build configuration, and the patched runtime.

    Compiler overrides could invalidate the preserved-MIR premise even though
    Charon's serialized options stay unchanged. Reject them before compiling.
    Cargo credential files are never inspected or included in the report.
    """
    for name, value in os.environ.items():
        if value and (name in {'RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS',
                'CARGO_BUILD_RUSTFLAGS', 'RUSTC', 'RUSTC_WRAPPER',
                'RUSTC_WORKSPACE_WRAPPER', 'CHARON_ARGS'} or
                re.fullmatch(r'CARGO_TARGET_.*_RUSTFLAGS', name)):
            raise ValueError(f'Unreviewed compiler override {name}')
    configs = []
    for base in [root / 'zerocopy', root, *root.parents,
                 Path(os.environ.get('CARGO_HOME', Path.home() / '.cargo'))]:
        for suffix in ('.cargo/config', '.cargo/config.toml', 'Charon.toml'):
            path = base / suffix
            if path.is_file() and path not in configs:
                configs.append(path)
    cargo_home = Path(os.environ.get('CARGO_HOME', Path.home() / '.cargo'))
    configs.extend(p for p in [cargo_home / 'config', cargo_home / 'config.toml']
                   if p.is_file() and p not in configs)
    for path in configs:
        if path.name == 'Charon.toml':
            raise ValueError(f'Extraction configuration must be in run.sh, not {path}')
        # Conservative lexical check avoids implementing Cargo's precedence
        # rules. Even a dormant override is rejected, rather than guessed safe.
        text = '\n'.join(line.split('#', 1)[0] for line in path.read_text().splitlines())
        if re.search(r'\b(rustflags|rustc|rustc-wrapper|rustc-workspace-wrapper)\b', text):
            raise ValueError(f'Unreviewed Cargo compiler configuration: {path}')
    paths = set()
    for directory in ['zerocopy/src', 'verification/aeneas', 'tools/aeneas-inline/src']:
        paths.update(p for p in (root / directory).rglob('*')
                     if p.is_file() and '__pycache__' not in p.parts and '.lake' not in p.parts
                     and 'golden' not in p.parts)
    paths.update(p for p in [root / 'Cargo.lock', root / 'Cargo.toml',
        root / 'zerocopy/Cargo.toml', root / 'zerocopy/build.rs',
        root / 'tools/Cargo.lock', root / 'tools/Cargo.toml', root / 'anneal/flake.lock']
        if p.is_file())
    combined = hashlib.sha256()
    for path in sorted(paths):
        combined.update(str(path.relative_to(root)).encode())
        combined.update(path.read_bytes())
    tools = Path(os.environ['AENEAS_TOOLCHAIN_DIR'])
    return {'project': combined.hexdigest(),
            'configs': [digest(path) for path in configs],
            'runtime': digest(tools / 'aeneas-build.json')}


def inspect(root, work, roots, sources, body_digests=None):
    registry_path = root / 'verification/aeneas/external.json'
    registry = json.loads(registry_path.read_text())
    reports = {}
    for stage, filename in [('before', 'zerocopy.before.ullbc'), ('llbc', 'zerocopy.llbc')]:
        path = work / filename
        if not path.is_file():
            raise ValueError(f'Missing mandatory {stage} admission snapshot: {path}')
        checked = Admission(json.loads(path.read_text()), registry)
        if checked.before != (stage == 'before'):
            raise ValueError(f'Wrong AST stage for mandatory {stage} snapshot')
        reports[stage] = checked.audit(roots)
        reports[stage]['sha256'] = digest(path)
    for entry in registry:
        if entry.get('opaque') and any(row['rust'] == entry['rust']
                for row in reports['llbc']['executions']):
            observed = (body_digests or {}).get(entry['rust'])
            if observed != [entry.get('source_body_sha256')]:
                raise ValueError(f'Trusted Rust helper body changed; review its interpretation: {entry["rust"]}')
    # Compare the unsafe call boundaries that must survive normalization.
    # This is a conservative shape check, not a formal simulation theorem.
    from collections import Counter
    guarded = {row['rust'] for row in registry
               if row.get('opaque') or row['signature']['unsafe']}
    def guarded_calls(stage):
        return Counter((call['caller'], call['callee']) for call in stage['calls']
                       if call['callee'] in guarded)
    missing = guarded_calls(reports['before']) - guarded_calls(reports['llbc'])
    if missing:
        raise ValueError(f'Normalization lost a guarded call boundary: {list(missing)}')
    # Capture this identity before compilation, then require it unchanged when
    # binding the model. Otherwise an editor could change Rust while Charon was
    # running and accidentally associate the old model with the new source.
    identity_path = work / 'extraction-inputs.json'
    if not identity_path.is_file():
        raise ValueError('Missing pre-compilation input identity')
    identity = json.loads(identity_path.read_text())
    if identity != input_identity(root):
        raise ValueError('Extraction inputs changed during compilation; regenerate')
    # No extra selection roster: every function binding supplies one root.
    return {'version': 1, 'stages': reports,
            'registry': digest(registry_path), 'sources': sources,
            'inputs': identity}


def check_translation(work, evidence):
    text = (work / 'Zerocopy/FunsExternal_Template.lean').read_text()
    signatures = {
        'util.transmute_unchecked':
            'axiom util.transmute_unchecked {Src : Type} (Dst : Type) : Src → Result Dst',
        'util.copy_unchecked':
            'axiom util.copy_unchecked : Slice Std.U8 → Slice Std.U8 → Result (Slice Std.U8)',
        'util.copy_unchecked_at':
            'axiom util.copy_unchecked_at : Slice Std.U8 → Slice Std.U8 → Std.Usize → Result (Slice Std.U8)',
        'util.validity.read_byte':
            'axiom util.validity.read_byte : Slice Std.U8 → Std.Usize → Result Std.U8',
        'core.num.Usize.unchecked_add':
            'axiom core.num.Usize.unchecked_add : Std.Usize → Std.Usize → Result Std.Usize',
        'core.num.Usize.unchecked_mul':
            'axiom core.num.Usize.unchecked_mul : Std.Usize → Std.Usize → Result Std.Usize',
    }
    normalized = ' '.join(text.split())
    for selected in evidence['stages']['llbc']['executions']:
        expected = signatures.get(selected.get('lean'))
        if expected and expected not in normalized:
            raise ValueError(f'Guarded boundary changed its generated failure-capable signature: {selected["rust"]}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['inputs', 'opaque'])
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    args = parser.parse_args()
    if args.command == 'inputs':
        print(json.dumps(input_identity(args.root), sort_keys=True))
    else:
        registry = json.loads((args.root / 'verification/aeneas/external.json').read_text())
        print('\n'.join(row['rust'] for row in registry if row.get('opaque')))


if __name__ == '__main__':
    main()
