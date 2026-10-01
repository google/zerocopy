#!/usr/bin/env python3
"""Check the v86 addendum against immutable published Git objects; launch nothing."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
M = json.loads((HERE / 'delta.json').read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(root, *args):
    env = dict(os.environ, GIT_NO_LAZY_FETCH='1')
    return subprocess.check_output(['git', *args], cwd=root, env=env)


def committed(root, revision, path):
    return git(root, 'show', f'{revision}:{path}')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--reference-root', type=Path,
                        default=Path(os.environ['REFERENCE_ROOT']) if os.environ.get('REFERENCE_ROOT') else None)
    args = parser.parse_args()
    if args.reference_root is None:
        parser.error('pass --reference-root or set REFERENCE_ROOT')
    root = args.reference_root
    assert git(root, 'cat-file', '-t', M['reference_head']).strip() == b'commit'
    for package in ('v85', 'lean_delta'):
        p = M[package]
        assert subprocess.run(['git', 'merge-base', '--is-ancestor', p['publication_revision'],
                               M['reference_head']], cwd=root, capture_output=True).returncode == 0
        tree = git(root, 'rev-parse', f"{p['publication_revision']}:reports/{p['package']}").decode().strip()
        assert tree == p['tree']
        assert sha(committed(root, p['publication_revision'], f"reports/{p['package']}/REPORT.md")) == p['report_sha256']
    v = M['v85']
    old_manifest = json.loads(committed(root, v['publication_revision'],
        f"reports/{v['package']}/support/validation-v85.json"))
    assert sha(committed(root, v['publication_revision'],
        f"reports/{v['package']}/support/validation-v85.json")) == v['validation_sha256']
    assert {k:old_manifest['counts'][k] for k in M['inherited_counts']} == M['inherited_counts']
    assert M['inherited_counts'] == {'investigations':159,'suggestions':174,
        'suggestion_links':345,'challenge_rows':333,'version_inventory':581}
    live_path = HERE / 'issue-observation-2026-10-01.json'
    assert sha(live_path.read_bytes()) == M['issue_observation_sha256']
    live = json.loads(live_path.read_text())
    assert live['observed_at'] == M['observed_at'] == '2026-10-01'
    assert [(i['number'],i['status']) for i in live['issues']] == [(3731,'Open'),(3730,'Closed as not planned')]
    assert '159 investigations' in live['issues'][0]['visible_body_excerpt']
    assert 'I145–I159' in live['issues'][0]['visible_body_excerpt']
    assert '174-entry crosswalk' in live['issues'][0]['visible_body_excerpt']
    admission = M['admission']
    sample_path = HERE / 'runtime-admission.json'
    sample_bytes = sample_path.read_bytes()
    assert sha(sample_bytes) == admission['snapshot_sha256']
    sample = json.loads(sample_bytes)
    assert sample['status'] == admission['decision'] == 'admission_denied'
    assert round(sample['memory_fraction'] * 100, 4) == admission['estimated_reclaimable_percent'] == 25.7875
    assert sample['disk_free_bytes'] == admission['free_disk_bytes'] == 12654592000
    assert sample['server_launched'] is admission['lean_server_launched'] is False
    assert sum(sample['memory_pages'].values()) * sample['page_bytes'] / sample['total_bytes'] == sample['memory_fraction']
    assert admission['estimated_reclaimable_percent'] < admission['minimum_reclaimable_percent_exclusive'] == 30.0
    assert admission['free_disk_bytes'] >= admission['minimum_free_disk_bytes'] == 10 * 1024**3
    assert admission['decision'] == 'admission_denied' and admission['lean_server_launched'] is False
    print('PASS: published v85 and Lean source delta bound; 159/174/345/333/581 retained; runtime admission denied')


if __name__ == '__main__':
    main()
