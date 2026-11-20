#!/usr/bin/env python3
"""Classify non-blank, non-comment lines of Abella .thm files.

A line is 'proof' if it lies after a `Theorem` statement's terminating '.'
and before the next top-level command (Theorem/Define/CoDefine/Kind/Type/
Import/Split/Close/Specification/Set/Query). Everything else is 'spec'
(definitions, signatures, theorem statements). '%' starts a line comment;
'/* ... */' block comments are stripped.
"""
import re, sys, pathlib
TOP = re.compile(r'^\s*(Theorem|Define|CoDefine|Kind|Type|Import|Split|Close|Specification|Set|Query)\b')
def strip_comments(s):
    s = re.sub(r'/\*.*?\*/', '', s, flags=re.S)
    return '\n'.join(l.split('%', 1)[0] for l in s.splitlines())
def classify(text):
    spec = proof = thms = skips = 0
    state = 'spec'; in_stmt = False
    for line in strip_comments(text).splitlines():
        if not line.strip():
            continue
        m = TOP.match(line)
        if m:
            state = 'spec'; in_stmt = (m.group(1) == 'Theorem')
            if in_stmt: thms += 1
        if re.search(r'\bskip\b', line): skips += 1
        if state == 'proof':
            proof += 1
        else:
            spec += 1
            if in_stmt and line.rstrip().endswith('.'):
                state = 'proof'; in_stmt = False
    return spec, proof, thms, skips
tot = [0, 0, 0, 0]
for p in sorted(sys.argv[1:]):
    r = classify(pathlib.Path(p).read_text())
    tot = [a + b for a, b in zip(tot, r)]
    print(f'{pathlib.Path(p).name:24s} spec={r[0]:5d} proof={r[1]:5d} theorems={r[2]:4d} skip={r[3]}')
print(f'{"TOTAL":24s} spec={tot[0]:5d} proof={tot[1]:5d} theorems={tot[2]:4d} skip={tot[3]}  proof/spec={tot[1]/tot[0]:.2f}')
