#!/usr/bin/env python3
"""Read-only offline integrity and exact-claim check for the R350 source review."""
from __future__ import annotations
import csv
import difflib
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
M = json.loads((HERE / 'claim-matrix.json').read_text())
O = json.loads((HERE / 'source-observation.json').read_text())

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def frozen(path: str) -> bytes:
    return subprocess.check_output(['git', 'show', M['frozen_reference_commit'] + ':' + path], cwd=ROOT)

def check(test: bool, label: str) -> None:
    if not test:
        raise AssertionError(label)

def main() -> None:
    check(subprocess.run(
        ['git', 'merge-base', '--is-ancestor', M['reference_parent_for_this_review'], 'HEAD'],
        cwd=ROOT, capture_output=True,
    ).returncode == 0, 'frozen parent is an ancestor of HEAD')
    md = frozen(M['predecessor_report_md'])
    rj = frozen(M['predecessor_report_json'])
    check(sha(md) == M['predecessor_report_md_sha256'], 'predecessor markdown')
    check(sha(rj) == M['predecessor_report_json_sha256'], 'predecessor metadata')
    check(json.loads(rj)['subjects'] == M['predecessor_subjects'], 'predecessor subjects')
    source = md.decode()
    summary = source.split('## Summary\n',1)[1].split('\n## ',1)[0].strip()
    findings = source.split('## Findings\n',1)[1].split('\n## Boundaries',1)[0]
    check(summary == M['full_summary_exact'], 'exact summary')
    for row in M['selected_findings']:
        exact = findings.split('### '+row['heading']+'\n',1)[1].split('\n### ',1)[0].strip()
        check(exact == row['exact_passage'], row['heading'])
    check(M['inventory_id'] == 'R350', 'inventory ID')
    check(sha((HERE/'source-observation.json').read_bytes()) == M['source_observation_sha256'], 'manifest hash')
    check(len(O['files']) == 10 and len({r['path'] for r in O['files']}) == 10, 'ten unique files')
    check(O['old_cargo_commit'] == M['old_cargo_commit'] == json.loads((HERE/'rust-old-cargo-gitlink.json').read_text())['sha'], 'old pin')
    check(O['new_cargo_commit'] == M['new_cargo_commit'] == json.loads((HERE/'rust-1981-cargo-gitlink.json').read_text())['sha'], 'new pin')
    check((HERE/'rust-tag-refs.txt').read_text().splitlines()[1].startswith('48a229ceaefd4985c50990b14116b6d856af0985\t'), 'release tag peel')
    changed = 0
    for row in O['files']:
        path = row['path']
        files = {}
        for side in ('old','new'):
            item=row[side]
            data=(HERE/item['snapshot']).read_bytes()
            files[side]=data
            check(item['commit'] == O['old_cargo_commit' if side=='old' else 'new_cargo_commit'], 'commit '+path)
            check(item['url'] == f"https://raw.githubusercontent.com/rust-lang/cargo/{item['commit']}/{path}", 'URL '+path)
            check((len(data),sha(data),blob(data)) == (item['size'],item['sha256'],item['git_blob_sha1']), 'snapshot '+path)
        check(row['same_blob'] == (files['old'] == files['new']), 'blob equality '+path)
        if not row['same_blob']:
            changed+=1
            diff=''.join(difflib.unified_diff(files['old'].decode().splitlines(keepends=True),files['new'].decode().splitlines(keepends=True),fromfile='old/'+path,tofile='new/'+path,n=3)).encode()
            check((HERE/row['diff_path']).read_bytes()==diff and sha(diff)==row['diff_sha256'], 'diff '+path)
    check(changed==4, 'four changed/six identical')
    check(M['runtime_status']=='unexecuted_in_this_review' and M['charon_aeneas_anneal_status']=='unassessed_in_this_review','limits')
    print('PASS: exact R350 frozen passages; ten Cargo source pairs (six identical, four changed); official gitlink snapshots; no target execution')

if __name__=='__main__':
    main()
