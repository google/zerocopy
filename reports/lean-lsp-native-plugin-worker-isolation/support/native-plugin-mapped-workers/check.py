#!/usr/bin/env python3
"""Offline checks for retained native-plugin process mapping evidence."""
import gzip
import hashlib
import json
from pathlib import Path

S = Path(__file__).resolve().parent
ROOT = S.parent
PLUGIN = 'plugin__probe_Plugin.dylib'
EXPECTED = {
    'v1-first': {93511: 'v1', 93518: 'v1'},
    'v1-after-close': {93511: 'v1'},
    'v2-open': {93511: 'v1', 93706: 'v2'},
    'forced-restart-v1': {93910: 'v1', 93911: 'v1'},
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def mapping_lines(label, pid, tool):
    path = S/'mapping-logs'/f'{label}-{pid}-{tool}.txt.gz'
    assert path.is_file(), path
    with gzip.open(path,'rt',encoding='utf-8') as f:
        raw=f.read()
    lines=[line for line in raw.splitlines() if PLUGIN in line]
    assert lines, path
    return lines,raw

def main():
    meta=json.loads((ROOT/'REPORT.json').read_text())
    assert set(meta)=={'topics','subjects','observed_at'}
    assert meta['observed_at']=='2026-09-30'
    assert sha(S/'artifacts/plugin-v1.dylib')==meta['subjects'][1]['identity']['v1_sha256']
    assert sha(S/'artifacts/plugin-v2.dylib')==meta['subjects'][1]['identity']['v2_sha256']
    assert sha(S/'run/live/.lake/build/lib/lean/v1'/PLUGIN)==meta['subjects'][1]['identity']['v1_sha256']
    assert sha(S/'run/live/.lake/build/lib/lean/v2'/PLUGIN)==meta['subjects'][1]['identity']['v2_sha256']
    link=S/'run/live/.lake/build/lib/lean'/PLUGIN
    assert link.is_symlink() and link.readlink().as_posix()==f'v1/{PLUGIN}'
    abort=json.loads((S/'guard-abort.json').read_text())
    assert abort['reason']=='process-tree RSS cap exceeded'
    assert abort['cap_kib']==1536*1024 and abort['total_kib']>abort['cap_kib']
    assert abort['active_server_pid']==93511
    assert {(r['pid'],r['ppid']) for r in abort['tree']}=={(93511,93509),(93706,93511)}
    assert 'P1.lean' in next(r['command'] for r in abort['tree'] if r['pid']==93706)
    for label, expected in EXPECTED.items():
        actual={int(p.name.split('-')[-2]) for p in (S/'mapping-logs').glob(f'{label}-*-lsof.txt.gz')}
        assert actual==set(expected), (label,actual)
        for pid,version in expected.items():
            suffix=f'/{version}/{PLUGIN}'
            for tool in ('lsof','vmmap'):
                lines,_=mapping_lines(label,pid,tool)
                assert all(line.rstrip().endswith(suffix) for line in lines), (label,pid,tool,lines)
                if tool=='lsof':assert len(lines)==1
                else:assert len(lines)>=4
    restart=json.loads((S/'restart-transcript.json').read_text())
    subject=next(e for e in restart if e['kind']=='recovery_subject')
    assert subject['v1_sha256']==meta['subjects'][1]['identity']['v1_sha256']
    assert subject['v2_sha256']==meta['subjects'][1]['identity']['v2_sha256']
    assert subject['free_memory_percent']>=30
    replace=next(e for e in restart if e['kind']=='replace')
    assert replace['link_target']==f'v1/{PLUGIN}'
    phase=next(e for e in restart if e['kind']=='phase')
    assert phase['label']=='v1-after-forced-restart' and phase['marker']=='plugin-v1'
    assert 'error' not in phase['wait'] and 'error' not in phase['goal']
    assert phase['goal']['result']['goals']==[]
    snapshot=next(e for e in restart if e['kind']=='mapping')
    assert snapshot['label']=='forced-restart-v1'
    assert {p['process']['pid'] for p in snapshot['processes']}=={93910,93911}
    for process in snapshot['processes']:
        for tool,datum in process['tools'].items():
            assert datum['exit']==0
            path=S/'mapping-logs'/datum['archive']
            with gzip.open(path,'rt',encoding='utf-8') as f:raw=f.read()
            assert hashlib.sha256(raw.encode()).hexdigest()==datum['raw_sha256']
            assert datum['matching_lines']==[line for line in raw.splitlines() if PLUGIN in line]
    assert next(e for e in restart if e['kind']=='server_stop')['exit']==0
    assert next(e for e in restart if e['kind']=='after_shutdown')['remaining']==[]
    resource=next(e for e in restart if e['kind']=='resources')
    assert resource['samples']>=10 and resource['peak_process_tree_rss_kib']<resource['cap_kib']==1536*1024
    assert not (S/'restart-guard-abort.json').exists()
    print('PASS: v1/v2 actual lsof+vmmap worker mappings, close, abort, forced restart, metadata')

if __name__=='__main__':main()
