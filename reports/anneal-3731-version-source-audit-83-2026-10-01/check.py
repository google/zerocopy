#!/usr/bin/env python3
"""Offline integrity check for the frozen 83-row source audit."""
import csv
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REPO = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish')
CACHE = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/sources')
CLASSES = {'source_revision_recheck', 'prior_comparison'}

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def git_object(cache, rev, path):
    env = os.environ.copy(); env['GIT_NO_LAZY_FETCH'] = '1'
    p = subprocess.run(['git', 'ls-tree', rev, '--', path], cwd=CACHE / cache,
                       env=env, text=True, capture_output=True, timeout=30)
    if p.returncode: return {'status': 'revision_unavailable', 'error': p.stderr.strip()}
    lines = [x for x in p.stdout.splitlines() if x.endswith('\t' + path)]
    if len(lines) != 1: return {'status': 'path_absent'}
    _, kind, rest = lines[0].split(' ', 2)
    oid, _ = rest.split('\t', 1)
    return {'status': 'present', 'kind': kind, 'git_sha1': oid}

inventory = [r for r in csv.DictReader((HERE / 'evidence/version-inventory-ebcdcad-581.csv').open())
             if r['classification'] in CLASSES]
selector = list(csv.DictReader((HERE / 'evidence/selector-83.csv').open()))
status = list(csv.DictReader((HERE / 'status-83.csv').open()))
rows = json.loads((HERE / 'evidence/bundle-pairs-83.json').read_text())
review_map = json.loads((HERE / 'evidence/review-map-83.json').read_text())
ids = [r['inventory_id'] for r in inventory]
assert len(ids) == 83 and len(set(ids)) == 83
assert ids == [r['inventory_id'] for r in selector]
assert ids == [r['inventory_id'] for r in status]
assert ids == [r['inventory_id'] for r in rows]
assert ids == [r['inventory_id'] for r in review_map]
assert sum(r['classification'] == 'source_revision_recheck' for r in inventory) == 72
assert sum(r['classification'] == 'prior_comparison' for r in inventory) == 11

checked = 0
for row, status_row in zip(rows, status):
    assert row['inventory_id'] == status_row['inventory_id']
    assert sha(REPO / row['original_report']) == row['original_report_sha256']
    assert json.loads(next(x for x in inventory if x['inventory_id'] == row['inventory_id'])['exact_pinned_subject_identities_json']) == row['pinned_subjects']
    for review in row['existing_source_reviews']:
        assert sha(REPO / review['review_report']) == review['review_report_sha256']
        assert sha(REPO / review['review_matrix']) == review['review_matrix_sha256']
    assert status_row['target_runtime'] == 'unexecuted_in_this_audit'
    assert status_row['anneal_product'] == 'unassessed_in_this_audit'
    assert status_row['source_relation_at_mapped_scope'] in {'changed', 'unchanged', 'unavailable'}
    for group, cache in ((row['google_source_pairs'], 'zerocopy-reference'),
                         (row['bundle_source_pairs'], None)):
        for pair in group:
            actual_cache = cache or {'AeneasVerif/aeneas': 'aeneas',
                                     'AeneasVerif/charon': 'charon',
                                     'charon-lang/charon': 'charon',
                                     'leanprover/lean4': 'lean4'}[pair['repository']]
            old = git_object(actual_cache, pair['old_revision'], pair['path'])
            new_path = pair.get('current_path', pair['path'])
            new_rev = pair.get('current_revision', pair.get('target_revision'))
            new = git_object(actual_cache, new_rev, new_path)
            assert old == pair['old'], (row['inventory_id'], pair['path'], 'old')
            assert new == pair.get('current', pair.get('target')), (row['inventory_id'], pair['path'], 'new')
            relation = ('same_git_object' if old.get('status') == new.get('status') == 'present' and old['git_sha1'] == new['git_sha1']
                        else 'different_git_object' if old.get('status') == new.get('status') == 'present'
                        else 'unavailable_or_absent')
            assert relation == pair['relation']
            checked += 1

heads = json.loads((HERE / 'evidence/default-heads.json').read_text())
assert heads['repository_count'] == len(heads['refs']) == 63
for result in heads['refs'].values():
    if result['head'] is not None:
        assert len(result['head']) == 40 and all(c in '0123456789abcdef' for c in result['head'])
assert sum(bool(r['head']) for r in heads['refs'].values()) == 62
assert sha(HERE / 'evidence/version-inventory-ebcdcad-581.csv') == sha(
    REPO / 'reports/anneal-3730-3731-residual-38-source-audit-2026-09-30-v85/support/version-inventory-ebcdcad-581.csv')
status_before = sha(HERE / 'status-83.csv')
details_before = sha(HERE / 'evidence/review-details-83.json')
rebuild = subprocess.run(['python3', 'build_status.py'], cwd=HERE, text=True,
                         capture_output=True, timeout=30)
assert rebuild.returncode == 0, rebuild.stderr
assert sha(HERE / 'status-83.csv') == status_before
assert sha(HERE / 'evidence/review-details-83.json') == details_before
print(f'PASS: {len(ids)} frozen rows, {checked} exact Git object pairs, 62/63 observed default refs, review/report bytes verified')
