#!/usr/bin/env python3
"""Compare frozen claim-related Google source paths to verified current main."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish')
SOURCE = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/sources/zerocopy-reference')
CURRENT = 'cc135f46155b72e4b51188525c2974a3b84acf92'

def git(*args):
    env = os.environ.copy()
    env['GIT_NO_LAZY_FETCH'] = '1'
    return subprocess.run(['git', *args], cwd=SOURCE, env=env, text=True,
                          capture_output=True, timeout=30)

def object_at(rev, path):
    p = git('ls-tree', rev, '--', path)
    if p.returncode != 0:
        return {'status': 'revision_unavailable', 'error': p.stderr.strip()}
    lines = [line for line in p.stdout.splitlines() if line.endswith('\t' + path)]
    if len(lines) != 1:
        return {'status': 'path_absent'}
    mode, typ, rest = lines[0].split(' ', 2)
    oid, _ = rest.split('\t', 1)
    return {'status': 'present', 'kind': typ, 'git_sha1': oid}

def old_google_revs(subjects):
    out = []
    for s in subjects:
        i = s['identity']
        if i.get('repository') == 'google/zerocopy' and i.get('revision'):
            out.append(i['revision'])
        elif i.get('source_commit') and s['name'].startswith('Checked-in Anneal V2'):
            out.append(i['source_commit'])
    return out

def map_paths(row, old_revs):
    package = (REPO / row['original_report']).parent
    sm = package / 'source-map.json'
    paths = []
    if sm.exists():
        source_map = json.loads(sm.read_text())
        for source in source_map.get('sources', []):
            repo = source.get('repository')
            path = source.get('path')
            if repo in (None, 'google/zerocopy') and path and path.startswith(('anneal/', 'exocrate/', 'zerocopy/')) and not path.startswith('reports/'):
                paths.append((source.get('revision') or source_map.get('subject_revision') or (old_revs[0] if old_revs else ''), path, 'source-map'))
            if repo == 'google/zerocopy' and isinstance(source.get('files'), dict):
                for path in source['files']:
                    paths.append((source.get('revision') or (old_revs[0] if old_revs else ''), path, 'source-map-files'))
    if not paths:
        text = (package / 'REPORT.md').read_text()
        found = sorted(set(re.findall(r'(?<![A-Za-z0-9_/])(?:anneal|exocrate|zerocopy)/[A-Za-z0-9_./-]+\.(?:rs|lean|nix|toml|lock|md|py|json|yml)', text)))
        for path in found:
            paths.append(((old_revs[0] if old_revs else ''), path, 'report-text'))
    if not paths and old_revs:
        report = row['original_report']
        path = 'exocrate' if 'exocrate' in report else 'anneal/v1' if 'anneal-v1' in report else 'zerocopy/src' if 'zerocopy-ffi' in report else 'anneal'
        paths.append((old_revs[0], path, 'complete-claim-subtree-fallback'))
    for path in {
        'R324': ['anneal/v1/src/parse/attr.rs', 'anneal/v1/src/generate.rs'],
        'R335': ['anneal/v1/src/aeneas.rs', 'anneal/v1/src/setup.rs'],
    }.get(row['inventory_id'], []):
        paths.append((old_revs[0], path, 'curated-current-v1-path'))
    return list(dict.fromkeys(paths))

rows = json.loads((HERE / 'evidence/review-map-83.json').read_text())
assert len(rows) == 83
assert git('cat-file', '-t', CURRENT).stdout.strip() == 'commit'
for row in rows:
    old_revs = old_google_revs(row['pinned_subjects'])
    pairs = []
    for old_rev, path, provenance in map_paths(row, old_revs):
        if not old_rev:
            continue
        old = object_at(old_rev, path)
        new = object_at(CURRENT, path)
        relation = ('same_git_object' if old.get('status') == new.get('status') == 'present' and old['git_sha1'] == new['git_sha1']
                    else 'different_git_object' if old.get('status') == new.get('status') == 'present'
                    else 'unavailable_or_absent')
        pairs.append({'repository': 'google/zerocopy', 'old_revision': old_rev,
                      'current_revision': CURRENT, 'path': path, 'path_basis': provenance,
                      'old': old, 'current': new, 'relation': relation})
    if row['inventory_id'] == 'R331':
        old_path = 'anneal/tests/integration.rs'
        new_path = 'anneal/v1/tests/integration.rs'
        old_rev = 'd410c162d51977635ca5afac67d99a3b10327a94'
        old = object_at(old_rev, old_path)
        new = object_at(CURRENT, new_path)
        assert old['status'] == new['status'] == 'present'
        pairs.append({'repository': 'google/zerocopy', 'old_revision': old_rev,
                      'current_revision': CURRENT, 'path': old_path, 'current_path': new_path,
                      'path_basis': 'curated-v1-reorganization-relocation', 'old': old,
                      'current': new, 'relation': 'same_git_object' if old['git_sha1'] == new['git_sha1'] else 'different_git_object'})
    row['google_source_pairs'] = pairs
    if pairs:
        row['google_source_summary'] = {
            'same': sum(p['relation'] == 'same_git_object' for p in pairs),
            'different': sum(p['relation'] == 'different_git_object' for p in pairs),
            'unavailable_or_absent': sum(p['relation'] == 'unavailable_or_absent' for p in pairs),
        }
    else:
        row['google_source_summary'] = None

out = HERE / 'evidence/local-pairs-83.json'
out.write_text(json.dumps(rows, indent=2, sort_keys=True) + '\n')
print(json.dumps({'rows': len(rows), 'with_google_pairs': sum(bool(x['google_source_pairs']) for x in rows),
                  'pair_count': sum(len(x['google_source_pairs']) for x in rows),
                  'unavailable_pairs': sum(x['google_source_summary']['unavailable_or_absent'] for x in rows if x['google_source_summary']),
                  'different_pairs': sum(x['google_source_summary']['different'] for x in rows if x['google_source_summary'])}, sort_keys=True))
