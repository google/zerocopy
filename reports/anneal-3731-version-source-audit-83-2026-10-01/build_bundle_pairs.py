#!/usr/bin/env python3
"""Compare mapped Aeneas, Charon, and Lean source objects at named releases."""
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REF = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish')
SOURCE_ROOT = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/sources')
TARGET = {
    'AeneasVerif/aeneas': ('aeneas', '0855ce1b8ed3958512b6c19de6bf3035b7acb552', 'nightly-2026.09.30'),
    'AeneasVerif/charon': ('charon', 'e435e5f341863a49a7e85d2fee9988bc0c687c82', 'Aeneas-paired 2026-09-30'),
    'charon-lang/charon': ('charon', 'e435e5f341863a49a7e85d2fee9988bc0c687c82', 'Aeneas-paired 2026-09-30; distinct upstream namespace'),
    'leanprover/lean4': ('lean4', '5045d0056413266e57c625dcd7c365b10e377c52', 'v4.34.1'),
}

MANUAL = {
    'R138': [('AeneasVerif/aeneas', 'f95a80abaf554d4612cb60ef9ec8e849139bec44', 'src'),
             ('AeneasVerif/aeneas', 'ac9f1bc5262a5e4ff1e24ca78617121382202727', 'src'),
             ('AeneasVerif/charon', '42836b36b666a980cbc9d438a8aed340ad3b848b', 'charon/src'),
             ('AeneasVerif/charon', 'a535e914f74db4fd9e6be7048f4233270d8945c0', 'charon/src')],
    'R368': [('AeneasVerif/charon', '0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1', 'charon/src')],
    'R423': [('leanprover/lean4', '68218e876d2a38b1985b8590fff244a83c321783', x) for x in (
        'src/lake/Lake/Config/Package.lean', 'src/lake/Lake/Config/Workspace.lean',
        'src/lake/Lake/Load/Config.lean', 'src/lake/Lake/Load/Lean/Elab.lean',
        'src/lake/Lake/Load/Resolve.lean', 'src/lake/Lake/Load/Toml.lean')],
    'R506': [('leanprover/lean4', '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc', x) for x in (
        'src/Init/ShareCommon.lean', 'src/Lean/Data/PersistentArray.lean',
        'src/Lean/Data/PersistentHashMap.lean', 'src/Lean/Util/ShareCommon.lean')],
    'R533': [('AeneasVerif/aeneas', 'f95a80abaf554d4612cb60ef9ec8e849139bec44', 'src'),
             ('AeneasVerif/aeneas', 'ac9f1bc5262a5e4ff1e24ca78617121382202727', 'src'),
             ('AeneasVerif/charon', 'a535e914f74db4fd9e6be7048f4233270d8945c0', 'charon/src')],
}

def object_at(repo, rev, path):
    env = os.environ.copy(); env['GIT_NO_LAZY_FETCH'] = '1'
    p = subprocess.run(['git', 'ls-tree', rev, '--', path], cwd=SOURCE_ROOT / repo,
                       env=env, text=True, capture_output=True, timeout=30)
    if p.returncode: return {'status': 'revision_unavailable', 'error': p.stderr.strip()}
    lines = [line for line in p.stdout.splitlines() if line.endswith('\t' + path)]
    if len(lines) != 1: return {'status': 'path_absent'}
    mode, kind, rest = lines[0].split(' ', 2)
    oid, _ = rest.split('\t', 1)
    return {'status': 'present', 'kind': kind, 'git_sha1': oid}

rows = json.loads((HERE / 'evidence/local-pairs-83.json').read_text())
for row in rows:
    rid = row['inventory_id']
    package = (REF / row['original_report']).parent
    source_map_path = package / 'source-map.json'
    entries = []
    if source_map_path.exists():
        sm = json.loads(source_map_path.read_text())
        for s in sm.get('sources', []):
            repo = s.get('repository')
            if repo not in TARGET: continue
            rev = s.get('revision') or sm.get('subject_revision')
            if rev and s.get('path'):
                entries.append((repo, rev, s['path'], 'source-map'))
            if rev and isinstance(s.get('files'), dict):
                entries.extend((repo, rev, path, 'source-map-files') for path in s['files'])
    entries.extend((repo, rev, path, 'curated-report-path') for repo, rev, path in MANUAL.get(rid, []))
    pairs = []
    for repo, old_rev, path, basis in dict.fromkeys(entries):
        cache_name, target_rev, label = TARGET[repo]
        old = object_at(cache_name, old_rev, path)
        new = object_at(cache_name, target_rev, path)
        relation = ('same_git_object' if old.get('status') == new.get('status') == 'present' and old['git_sha1'] == new['git_sha1']
                    else 'different_git_object' if old.get('status') == new.get('status') == 'present'
                    else 'unavailable_or_absent')
        pairs.append({'repository': repo, 'old_revision': old_rev,
                      'target_revision': target_rev, 'target_label': label, 'path': path,
                      'path_basis': basis, 'old': old, 'target': new, 'relation': relation})
    row['bundle_source_pairs'] = pairs
    row['bundle_source_summary'] = {
        'same': sum(p['relation'] == 'same_git_object' for p in pairs),
        'different': sum(p['relation'] == 'different_git_object' for p in pairs),
        'unavailable_or_absent': sum(p['relation'] == 'unavailable_or_absent' for p in pairs),
    } if pairs else None

out = HERE / 'evidence/bundle-pairs-83.json'
out.write_text(json.dumps(rows, indent=2, sort_keys=True) + '\n')
print(json.dumps({'rows': len(rows), 'with_pairs': sum(bool(r['bundle_source_pairs']) for r in rows),
                  'pairs': sum(len(r['bundle_source_pairs']) for r in rows),
                  'same': sum(r['bundle_source_summary']['same'] for r in rows if r['bundle_source_summary']),
                  'different': sum(r['bundle_source_summary']['different'] for r in rows if r['bundle_source_summary']),
                  'unavailable': sum(r['bundle_source_summary']['unavailable_or_absent'] for r in rows if r['bundle_source_summary'])}, sort_keys=True))
