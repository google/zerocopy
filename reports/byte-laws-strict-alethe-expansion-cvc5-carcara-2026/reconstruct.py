"""Untrusted, bounded Alethe producer for the four fixed byte-law roots.

This does not verify cvc5 or change Carcara. Every emitted assumption must be an
assertion in the separately supplied SMT root; every inference is checked by the
unchanged native Carcara. The consumer must bind the independent root hash.
"""
import argparse
from pathlib import Path


def application(op, *args):
    return '(' + op + ' ' + ' '.join(args) + ')'


def produce(case, source):
    statements = []
    for line in source.splitlines():
        if line.startswith('(assert ') and line.endswith(')'):
            statements.append(line[len('(assert '):-1])
    if not statements:
        raise ValueError('no single-line assertion roots')
    lines = ['(']
    premises = {}
    for i, term in enumerate(statements):
        name = f'a{i}'
        premises[term] = name
        lines.append(f'(assume {name} {term})')
    counter = 0

    def step(terms, rule, refs=()):
        nonlocal counter
        name = f't{counter}'
        counter += 1
        clause = '(cl' + ((' ' + ' '.join(terms)) if terms else '') + ')'
        suffix = ' :premises (' + ' '.join(refs) + ')' if refs else ''
        lines.append(f'(step {name} {clause} :rule {rule}{suffix})')
        return name

    def get(term):
        try:
            return premises[term]
        except KeyError:
            raise ValueError('required premise is not in this root: ' + term) from None

    def select(array, index):
        return application('select', array, index)

    def transfer_validity(index, narrow=False):
        source_byte = select('source', index)
        current_byte = select('current', index)
        source_cmp = application('>=', source_byte, '2')
        current_cmp = application('>=', current_byte, '2')
        source_valid = application('not', source_cmp)
        current_valid = application('not', current_cmp)
        if narrow:
            # Two ordinary comparison normalizations, then congruence of not.
            lt = application('<', source_byte, '2')
            le = application('<=', '2', source_byte)
            not_le = application('not', le)
            h_lt = step([application('=', lt, not_le)], 'comp_simplify')
            h_ge = step([application('=', source_cmp, le)], 'comp_simplify')
            h_not = step([application('=', source_valid, not_le)], 'cong', [h_ge])
            h_reverse = step([application('=', not_le, source_valid)], 'symm', [h_not])
            h_trans = step([application('=', lt, source_valid)], 'trans', [h_lt, h_reverse])
            source_ref = step([source_valid], 'eq_mp', [get(lt), h_trans])
        else:
            source_ref = get(source_valid)
        byte_eq = get(application('=', source_byte, current_byte))
        cmp_eq = step([application('=', source_cmp, current_cmp)], 'cong', [byte_eq])
        valid_eq = step([application('=', source_valid, current_valid)], 'cong', [cmp_eq])
        return current_valid, step([current_valid], 'eq_mp', [source_ref, valid_eq])

    if case == 'into_bytes':
        terms = [select('source_' + metadata, index)
                 for index in ['0', '1'] for metadata in ['init', 'read']]
        refs = [get(term) for term in terms]
    elif case == 'byte_write':
        value_store = application('store', 'source', 'changed', 'replacement')
        init_store = application('store', 'source_init', 'changed', 'true')
        terms = [application('=', select(value_store, 'changed'), 'replacement'),
                 select(init_store, 'changed'),
                 application('=', select(value_store, 'framed'), select('source', 'framed')),
                 application('=', select(init_store, 'framed'), select('source_init', 'framed'))]
        byte_at_write = step([terms[0]], 'arrays_idx')
        init_at_write_eq = step([application('=', terms[1], 'true')], 'arrays_idx')
        init_reversed = step([application('=', 'true', terms[1])], 'symm', [init_at_write_eq])
        truth = step(['true'], 'true')
        init_at_write = step([terms[1]], 'eq_mp', [truth, init_reversed])
        separated = get('(not (= changed framed))')
        outside_byte = step([terms[2]], 'arrays_row', [separated])
        outside_init = step([terms[3]], 'arrays_row', [separated])
        refs = [byte_at_write, init_at_write, outside_byte, outside_init]
    elif case in ['bool_validate', 'array_validate', 'wrong_narrow_domain']:
        indices = ['0', '1'] if case == 'array_validate' else ['0']
        terms = [select('current_' + metadata, index)
                 for index in indices for metadata in ['init', 'read']]
        refs = [get(term) for term in terms]
        for index in indices:
            term, ref = transfer_validity(index, case == 'wrong_narrow_domain')
            terms.append(term)
            refs.append(ref)
    else:
        raise ValueError('case outside bounded producer')

    goal = application('and', *terms)
    negated = application('not', goal)
    goal_ref = step([goal], 'and_intro', refs)
    step([], 'resolution', [goal_ref, get(negated)])
    lines.append(')')
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', required=True)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    with args.output.open('x') as output:
        output.write(produce(args.case, args.root.read_text()))


if __name__ == '__main__':
    main()
