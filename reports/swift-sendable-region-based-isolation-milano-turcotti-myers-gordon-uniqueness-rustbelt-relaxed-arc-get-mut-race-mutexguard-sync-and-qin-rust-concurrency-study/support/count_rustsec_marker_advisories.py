#!/usr/bin/env python3
"""Count RustSec advisories about thread-safety marker (Send/Sync) implementations.

Usage: python3 count_rustsec_marker_advisories.py <advisory-db checkout>

Reads every crates/*/RUSTSEC-*.md file, parses the leading ```toml block, and
reports counts for three nested classes:
  A  categories contains "thread-safety"           (withdrawn advisories excluded)
  B  A and (title or description or keywords mention Send or Sync as a word)
  C  B and (categories contains "memory-corruption" or text mentions
     use-after-free / dangling / double free)
  D  B and text explicitly mentions use-after-free / dangling / double free
Also prints the B list (id, crate, date, title) for manual audit.
Standard library only (Python 3.11+ for tomllib).
"""
import pathlib, re, sys, tomllib, collections

root = pathlib.Path(sys.argv[1])
files = sorted(root.glob('crates/*/RUSTSEC-*.md'))
TOML = re.compile(r'```toml\n(.*?)\n```', re.S)
WORD = re.compile(r'\b(Send|Sync)\b')
UAF = re.compile(r'use[- ]after[- ]free|dangling|double[- ]free', re.I)

total = withdrawn = 0
A, B, C, D = [], [], [], []
for f in files:
    text = f.read_text(encoding='utf-8')
    m = TOML.search(text)
    if not m:
        continue
    meta = tomllib.loads(m.group(1)).get('advisory', {})
    total += 1
    if meta.get('withdrawn'):
        withdrawn += 1
        continue
    body = text[m.end():]
    title = body.strip().splitlines()[0].lstrip('# ').strip() if body.strip() else ''
    cats = meta.get('categories', [])
    kws = ' '.join(meta.get('keywords', []))
    if 'thread-safety' not in cats:
        continue
    rec = (meta.get('id'), meta.get('package'), str(meta.get('date')), title)
    A.append(rec)
    if WORD.search(title) or WORD.search(body) or re.search(r'\b(send|sync)\b', kws, re.I):
        B.append(rec)
        if 'memory-corruption' in cats or UAF.search(body):
            C.append(rec)
        if UAF.search(body):
            D.append(rec)

print(f'advisory files parsed: {total}; withdrawn excluded: {withdrawn}')
print(f'A thread-safety category: {len(A)}')
print(f'B ... mentioning Send/Sync: {len(B)}')
print(f'C ... and memory-corruption or use-after-free/dangling/double-free text: {len(C)}')
print(f'D B and explicit use-after-free/dangling/double-free text: {len(D)}')
print('A by year:', dict(sorted(collections.Counter(r[2][:4] for r in A).items())))
print('B by year:', dict(sorted(collections.Counter(r[2][:4] for r in B).items())))
print('--- B list (id, crate, date, title) ---')
for r in B:
    print(' | '.join(r), ('| C' if r in C else '') + (' D' if r in D else ''))
