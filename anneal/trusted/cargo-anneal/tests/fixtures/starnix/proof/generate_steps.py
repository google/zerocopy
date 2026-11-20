# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Produce candidate execution witnesses; Lean checks every source transition."""

import argparse
import copy
import json
from pathlib import Path

HEADER = '-- Copyright 2026 The Fuchsia Authors\n--\n-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n-- This file may not be copied, modified, or distributed except according to\n-- those terms.\n\n'


def is_u64_ty(ty):
    return ty['kind'] == 'int' and ty['width'] == 'i64' and not ty['signed']


def is_isize_ty(ty):
    return ty['kind'] == 'int' and ty['width'] == 'isize' and ty['signed']


def uninit_slot(ty):
    if ty['kind'] == 'unit':
        return ('value', ('.unit', None, 0))
    return ('uninit', None)


def render_slot(slot):
    kind, payload = slot
    if kind == 'dead':
        return '.dead'
    if kind == 'uninit':
        return '.live none'
    assert kind == 'value'
    val_term = payload[0]
    if ' ' in val_term:
        return f'.live (some ({val_term}))'
    return f'.live (some {val_term})'


# Enumerate concrete control choices while retaining the u64 input as a
# symbolic parameter. The generated theorem must cover every value, not a
# finite sample; Lean checks the emitted transitions against sourceBody.
def produce(body, flag, width):
    local_tys = body['local_tys']
    markers = set()
    for block in body['blocks']:
        for stmt in block['statements']:
            if stmt['kind'] in ('storage_live', 'storage_dead'):
                markers.add(stmt['local'])
    locals_ = [('dead', None) if i in markers else uninit_slot(local_tys[i])
               for i in range(len(local_tys))]
    flag_bool = 'true' if flag else 'false'
    locals_[1:4] = [('value', (f'.bool {flag_bool}', None, flag)),
                    ('value', (f'dataWidthVal {width}', None, width)),
                    ('value', ('u64Val value', 'value', None))]
    block = position = 0
    states = []
    step_proofs = []

    # Concrete values choose branches; symbolic expressions only describe
    # candidate states. These assertions restrict this producer, while its
    # generated step obligations still establish the actual source behavior.
    def operand(op):
        kind = op['kind']
        if kind == 'constant':
            ty = op['ty']
            lit = op['lit']
            if lit['kind'] == 'zero_sized':
                assert ty['kind'] == 'unit'
                return '.unit', None, 0
            bits = lit['bits']
            if ty['kind'] == 'bool':
                b = 'true' if bits else 'false'
                return f'.bool {b}', None, bits
            if is_u64_ty(ty):
                return f'u64Val {bits}', str(bits), bits
            if is_isize_ty(ty):
                return f'isizeVal {bits}', None, bits
            assert ty['kind'] == 'int'
            w = ty['width']
            s = 'true' if ty['signed'] else 'false'
            return f'.scalar ⟨.{w}, {s}, BitVec.ofNat 128 {bits}⟩', None, bits
        index = op['local']
        assert locals_[index][0] == 'value', (index, locals_[index])
        value = locals_[index][1]
        if kind == 'move':
            locals_[index] = uninit_slot(local_tys[index])
        else:
            assert kind == 'copy'
        return value

    def eval_assign(dst, rv):
        dst_ty = local_tys[dst]
        kind = rv['kind']
        if kind == 'unit':
            return ('.unit', None, 0), '(by rfl)'
        if kind == 'use':
            val_term, word_expr, known = operand(rv['operand'])
            if is_u64_ty(dst_ty) and known is None:
                assert word_expr is not None
                proof = f'(step_u64Use {word_expr} (by rfl) (by rfl))'
            else:
                proof = '(by rfl)'
            return (val_term, word_expr, known), proof
        if kind == 'discriminant':
            index = rv['local']
            assert locals_[index][0] == 'value'
            variant = locals_[index][1][2]
            table = local_tys[index]['discriminants']
            disc = table[variant]
            return (f'isizeVal {disc}', None, disc), '(by rfl)'
        assert kind == 'binary' and is_u64_ty(dst_ty)
        _, left_w, _ = operand(rv['left'])
        _, right_w, right_known = operand(rv['right'])
        op = rv['op']
        if op == 'bit_and':
            assert left_w is not None and right_w is not None
            expr = f'({left_w} &&& {right_w})'
            return (f'u64Val {expr}', expr, None), f'(step_u64And {left_w} {right_w} (by rfl) (by rfl))'
        if op == 'bit_or':
            assert left_w is not None and right_w is not None
            expr = f'({left_w} ||| {right_w})'
            return (f'u64Val {expr}', expr, None), f'(step_u64Or {left_w} {right_w} (by rfl) (by rfl))'
        assert op in ('shl', 'shr') and left_w is not None and right_known is not None
        amount = right_known % 64
        operator = '<<<' if op == 'shl' else '>>>'
        lemma = 'step_u64Shl' if op == 'shl' else 'step_u64Shr'
        expr = f'({left_w} {operator} ({amount} : Nat))'
        return (f'u64Val {expr}', expr, None), f'({lemma} {left_w} {amount} (by rfl) (by rfl))'

    while True:
        states.append((block, position, copy.deepcopy(locals_)))
        current = body['blocks'][block]
        if position < len(current['statements']):
            stmt = current['statements'][position]
            kind = stmt['kind']
            if kind == 'assign':
                result, proof = eval_assign(stmt['local'], stmt['value'])
                locals_[stmt['local']] = ('value', result)
                step_proofs.append(proof)
            elif kind == 'storage_live':
                locals_[stmt['local']] = uninit_slot(local_tys[stmt['local']])
                step_proofs.append('(by rfl)')
            elif kind == 'storage_dead':
                locals_[stmt['local']] = ('dead', None)
                step_proofs.append('(by rfl)')
            else:
                assert kind == 'nop'
                step_proofs.append('(by rfl)')
            position += 1
            continue
        term = current['terminator']
        if term['kind'] == 'ret':
            break
        if term['kind'] == 'goto':
            block = term['block']
        else:
            assert term['kind'] == 'switch_int'
            _, _, key = operand(term['operand'])
            assert key is not None
            block = dict(term['targets']).get(key, term['otherwise'])
        step_proofs.append('(by rfl)')
        position = 0

    # This witness records the source's actual result, including after a
    # mutation. ProductionEndpoints separately applies the fixed expected value;
    # keeping those duties apart lets CI positively check each generated path.
    label = ('be' if flag else 'le') + str(8 << width)
    # Witness the source's actual result. Fixed byte-reversal endpoints live
    # in a separate module, so checking these transitions does not assume the
    # property that a mutation is intended to violate.
    assert locals_[0][0] == 'value' and locals_[0][1][1] is not None
    output_val = locals_[0][1][0]
    source = ''
    for i, (b, p, slots) in enumerate(states):
        source += f'private def {label}_state{i} (value : Word) : State :=\n  mkState {b} {p} [\n'
        terms = [render_slot(x) for x in slots]
        for j in range(0, len(terms), 5):
            source += '    ' + ', '.join(terms[j:j + 5])
            if j + 5 < len(terms):
                source += ','
            source += '\n'
        source += '  ]\n\n'
    last = len(states) - 1
    assert len(step_proofs) == last
    # Keep every intermediate state checked while composing a short entry
    # segment with the returning suffix. Short source mutations can return
    # before two transitions, so the checkpoint must stay on their actual path.
    checkpoint = min(2, last)
    segment = '.refl'
    for k in range(checkpoint):
        segment = f'.next ({segment}) {step_proofs[k]}'
    source += f'''private theorem {label}_suffix{last} (value : Word) :
    Executes sourceBody ({label}_state{last} value) ({output_val}) :=
  .ret (by rfl)

'''
    for i in range(last - 1, checkpoint - 1, -1):
        source += f'''private theorem {label}_suffix{i} (value : Word) :
    Executes sourceBody ({label}_state{i} value) ({output_val}) :=
  .next {step_proofs[i]} ({label}_suffix{i + 1} value)

'''
    source += f'''theorem {label}_actual (value : Word) :
    Safe sourceBody (endianArgs {flag_bool} {width} value) ∧
      Returns sourceBody (endianArgs {flag_bool} {width} value) ({output_val}) := by
  have start : mkState 0 0
      (initLocalsLoop sourceBody (endianArgs {flag_bool} {width} value) 0
        sourceBody.locals) =
      {label}_state0 value := by rfl
  have segment : Reach sourceBody ({label}_state0 value)
      ({label}_state{checkpoint} value) :=
    {segment}
  have execution : Executes sourceBody
      (mkState 0 0
        (initLocalsLoop sourceBody (endianArgs {flag_bool} {width} value) 0
          sourceBody.locals)) ({output_val}) := by
    rw [start]
    exact executes_prepend segment ({label}_suffix{checkpoint} value)
  exact ⟨executes_safe execution, executes_returns execution⟩

'''
    return source, len(states)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capture', type=Path, help='Typed capture.json input')
    parser.add_argument('output', type=Path, help='Candidate Lean proof module')
    args = parser.parse_args()
    with args.capture.open() as source:
        captured = json.load(source)
    if captured.get('schema_version') != 3:
        raise ValueError(
            f"Unsupported capture schema_version: {captured.get('schema_version')}"
        )
    bodies = captured['program']['bodies']
    if len(bodies) != 1:
        raise ValueError('The fixture requires one selected production body')
    parts = []
    count = 0
    for flag in (0, 1):
        for width in range(4):
            part, length = produce(bodies[0], flag, width)
            parts.append(part)
            count += length
    args.output.write_text(HEADER + """prelude
import InitialCache

namespace ProductionSteps

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Endianness ProductionReduction

""" + ''.join(parts) + 'end ProductionSteps\n')
    print(f'Wrote {count} candidate state witnesses to {args.output}')


if __name__ == '__main__':
    main()
