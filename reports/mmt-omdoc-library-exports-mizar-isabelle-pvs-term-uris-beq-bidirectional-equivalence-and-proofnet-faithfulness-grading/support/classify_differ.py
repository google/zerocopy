#!/usr/bin/env python3
"""Heuristic classification of the first differing subterm pair recorded by
ReelabProbe.lean (column `detail`, token `DIFF[a ~~ b]`, where `a` comes from the
re-elaborated term and `b` from the stored theorem type).

Usage: python3 classify_differ.py out_default.tsv
The classes are a reading aid, not a semantic proof: the probe records only the
first differing pair found by a left-to-right structural walk.
"""
import collections, re, sys

NUM = {'Nat', 'Int', 'UInt8', 'UInt16', 'UInt32', 'UInt64', 'USize', 'Int8', 'Int16',
       'Int32', 'Int64', 'ISize', 'Dyadic', 'Rat', 'Float', 'Float32', 'Char'}

def cls(detail):
    m = re.search(r'DIFF\[(.*?) ~~ (.*?)\]', detail)
    if not m:
        return 'none'
    a, b = m.group(1).strip(), m.group(2).strip()
    if a in NUM and (b in NUM or b.startswith('Fin ') or b.startswith('BitVec')):
        return 'numeral/literal type defaulting'
    if (a.startswith('Fin ') or a.startswith('BitVec')) and b in NUM:
        return 'numeral/literal type defaulting'
    if re.match(r'^#\d+$', a) and re.match(r'^#\d+$', b):
        return 'bound-variable (instance/hypothesis) identity'
    if '.{' in a and '.{' in b and a.split('.{')[0] == b.split('.{')[0]:
        return 'universe instantiation (e.g. element type defaulted)'
    if re.match(r'^#\d+$', b) or re.match(r'^#\d+$', a):
        return 'binder-type/argument dependency'
    if 'match_' in a or 'match_' in b:
        return 'auxiliary matcher identity'
    return 'other'

def main(path):
    rows = [l.rstrip('\n').split('\t') for l in open(path, encoding='utf-8')
            if not l.startswith('#') and not l.startswith('name\t')]
    for st in ('differ', 'defeq'):
        for tx in ('same', 'changed'):
            c = collections.Counter(cls(r[9]) for r in rows if len(r) >= 10 and r[2] == st and r[3] == tx)
            print(st, tx, sum(c.values()), dict(c.most_common()))

if __name__ == '__main__':
    main(sys.argv[1])
