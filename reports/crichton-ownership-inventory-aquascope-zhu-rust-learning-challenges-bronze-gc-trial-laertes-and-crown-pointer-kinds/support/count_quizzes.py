#!/usr/bin/env python3
"""Count quiz questions by file and type in a checkout of the book fork.

Usage: count_quizzes.py <rust-book-checkout>/quizzes
"""
import collections, pathlib, sys, tomllib
d = pathlib.Path(sys.argv[1])
total = 0; types = collections.Counter(); groups = collections.defaultdict(lambda: [0, 0, collections.Counter()])
def group(name):
    if name.startswith('ch04'): return 'chapter 4'
    if name.startswith('ch10-03'): return 'ch10-03 lifetimes'
    if name.endswith('-inventory.toml'): return 'ownership inventory files'
    return None
files = sorted(d.glob('*.toml'))
for f in files:
    qs = tomllib.loads(f.read_text()).get('questions', [])
    c = collections.Counter(q.get('type') for q in qs)
    total += len(qs); types.update(c)
    g = group(f.name)
    if g:
        groups[g][0] += 1; groups[g][1] += len(qs); groups[g][2].update(c)
        print(f"{f.name}\t{len(qs)}\t{dict(c)}")
print(f"ALL\tfiles={len(files)}\tquestions={total}\t{dict(types)}")
for g, (nf, nq, c) in sorted(groups.items()):
    print(f"GROUP {g}\tfiles={nf}\tquestions={nq}\t{dict(c)}")
