"""Untrusted exact local expansion of five cvc5 rare_rewrite names.

Conclusions, assertion roots and all other proof steps remain unchanged.
Carcara checks the translated steps; this program is not in acceptance TCB.
The arithmetic expansion avoids assuming that not(>= a b) is a native normal
form for comp_simplify: it proves both sides equal to not(<= b a).
"""
import argparse
import re
from pathlib import Path


def parse_terms(text):
    tokens = re.findall(r'\(|\)|"[^"\\]*(?:\\.[^"\\]*)*"|[^\s()]+', text)
    position = 0

    def term():
        nonlocal position
        if position >= len(tokens):
            raise ValueError('truncated rare_rewrite arguments')
        head = tokens[position]
        position += 1
        if head == ')':
            raise ValueError('unexpected close parenthesis')
        if head != '(':
            return head
        children = []
        while position < len(tokens) and tokens[position] != ')':
            children.append(term())
        if position >= len(tokens):
            raise ValueError('unclosed rare_rewrite arguments')
        position += 1
        return children

    result = []
    while position < len(tokens):
        result.append(term())
    return result


def render(term):
    return '(' + ' '.join(map(render, term)) + ')' if isinstance(term, list) else term


def translate(proof):
    direct = {'array-read-over-write': 'arrays_idx',
              'eq-refl': 'eq_simplify',
              'eq-symm': 'eq_symmetric',
              'bool-double-not-elim': 'not_simplify'}
    lines = []
    counts = {}
    for line in proof.splitlines():
        if ':rule rare_rewrite' not in line:
            lines.append(line)
            continue
        match = re.fullmatch(r'(\(step (\S+) .*?) :rule rare_rewrite :args \((.*)\)\)', line)
        if match is None:
            raise ValueError('outside bounded one-line rare_rewrite syntax')
        prefix, name, args_text = match.groups()
        args = parse_terms(args_text)
        if not args or not isinstance(args[0], str) or not args[0].startswith('"'):
            raise ValueError('expected literal rewrite name')
        rule = args[0][1:-1]
        counts[rule] = counts.get(rule, 0) + 1
        if rule in direct:
            expected = {'array-read-over-write': 4, 'eq-refl': 2,
                        'eq-symm': 3, 'bool-double-not-elim': 2}[rule]
            if len(args) != expected:
                raise ValueError('wrong argument count for ' + rule)
            lines.append(prefix + ' :rule ' + direct[rule] + ')')
        elif rule == 'arith-elim-lt' and len(args) == 3:
            a, b = map(render, args[1:])
            ids = [name + '.normalized_' + str(i) for i in range(4)]
            # These helper names are fresh in these bounded cvc5 artifacts.
            if any(re.search(r'\(step ' + re.escape(i) + r'\s', proof) for i in ids):
                raise ValueError('helper step identifier collision')
            le = f'(<= {b} {a})'
            ge = f'(>= {a} {b})'
            lines += [
                f'(step {ids[0]} (cl (= (< {a} {b}) (not {le}))) :rule comp_simplify)',
                f'(step {ids[1]} (cl (= {ge} {le})) :rule comp_simplify)',
                f'(step {ids[2]} (cl (= (not {ge}) (not {le}))) :rule cong :premises ({ids[1]}))',
                f'(step {ids[3]} (cl (= (not {le}) (not {ge}))) :rule symm :premises ({ids[2]}))',
                prefix + f' :rule trans :premises ({ids[0]} {ids[3]}))',
            ]
        else:
            raise ValueError('unexamined rewrite name/arity: ' + rule)
    return '\n'.join(lines) + '\n', counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    translated, counts = translate(args.input.read_text())
    with args.output.open('x') as output:
        output.write(translated)
    print(counts)


if __name__ == '__main__':
    main()
