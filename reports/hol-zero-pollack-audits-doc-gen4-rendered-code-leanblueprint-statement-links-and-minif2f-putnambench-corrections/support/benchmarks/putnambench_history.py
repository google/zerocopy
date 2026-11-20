#!/usr/bin/env python3
"""Classify the commit history of trishullab/PutnamBench that touches lean4/src.

Fetches (read-only, GitHub REST API via the `gh` CLI) all commits reachable
from the pinned revision that touch lean4/src, drops merge commits, and
classifies first lines of commit messages with the regular expressions below.
This is a message-text heuristic, not a semantic review of each diff.

Usage: python3 putnambench_history.py [revision]
"""
import collections, json, re, subprocess, sys

REV = sys.argv[1] if len(sys.argv) > 1 else 'a635813f5edf297d928f9bd5ef8324a26bdde09c'
commits, page = [], 1
while True:
    out = subprocess.run(['gh', 'api', f'repos/trishullab/PutnamBench/commits?sha={REV}&path=lean4/src&per_page=100&page={page}'],
                         capture_output=True, text=True, check=True).stdout
    batch = json.loads(out)
    commits += batch
    if len(batch) < 100:
        break
    page += 1
print('commits touching lean4/src (incl. merges):', len(commits))
commits = [c for c in commits if len(c.get('parents', [])) <= 1]
print('non-merge commits:', len(commits))

INFRA = re.compile(r'build|style|deprecat|version|syntax highlighting|update to lean|bump|toolchain|compil|unknown identifier|elaboration issue|lint|spacing|split lean|readme|ci\b', re.I)
FIX = re.compile(r'\bfix|misformal|wrong|incorrect|correct', re.I)
PROB = re.compile(r'(?:putnam[ _])?((?:19|20)\d\d)[ _]?([ab]\d)\b', re.I)

def first(c):
    return c['commit']['message'].splitlines()[0]

sf = [c for c in commits if FIX.search(first(c)) and not INFRA.search(first(c))]
infra = [c for c in commits if INFRA.search(first(c))]
print('statement-fix (heuristic):', len(sf))
print('infrastructure (heuristic):', len(infra))
print('other (additions, edits):', len(commits) - len(sf) - len(infra))
probs = {(y, p.upper()) for c in sf for (y, p) in PROB.findall(c['commit']['message'])}
print('distinct problems named in statement-fix messages:', len(probs))
for label, rx in [('disprovable', r'disprovable'), ('counterexample', r'counterexample|counter-example'),
                  ('trivially provable / vacuous', r'trivially (true|provable)|vacuous'),
                  ('issue reference', r'\bfixes #\d+|issue'), ('optParam', r'optparam'),
                  ('Euclidean / sup-norm metric', r'euclidean|dist\b|sup norm'),
                  ('parentheses / precedence', r'parenthes|precedence'), ('off-by-one', r'off-by-one'),
                  ('informal statement', r'informal')]:
    print(f'  messages mentioning {label}: {sum(1 for c in sf if re.search(rx, c["commit"]["message"], re.I))}')
print('statement-fix commits with an explanatory body:', sum(1 for c in sf if len(c['commit']['message'].strip().splitlines()) > 1))
dates = sorted(c['commit']['author']['date'][:10] for c in sf)
print('author-date range of statement-fix commits:', dates[0], '..', dates[-1])
authors = collections.Counter(c['commit']['author']['name'] for c in sf)
print('distinct commit authors of statement-fix commits:', len(authors))
print('largest single-author share:', authors.most_common(1)[0][1])
