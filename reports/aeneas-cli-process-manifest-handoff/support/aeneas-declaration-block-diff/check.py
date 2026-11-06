#!/usr/bin/env python3
"""Read-only replay of lexical block intervals and mutation comparisons."""
import hashlib
import json
import re
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPORT=HERE.parent
CASES=('base','function_body','type_shape','trait_impl','recursive_group','helper_insert','delete_step')
def sha(raw):return hashlib.sha256(raw).hexdigest()
def file_sha(path):return sha(path.read_bytes())
def blocks(raw,entries):
    lines=raw.decode('utf-8').splitlines(keepends=True)
    out={}
    for entry in entries:
        start=entry['line']-1
        assert lines[start].strip()==entry['head']
        assert re.match(r'^\s*(?:def|abbrev|structure|inductive|opaque|theorem|instance|partial def)\s+',lines[start])
        end=start+1
        while end<len(lines):
            stripped=lines[end].strip()
            if stripped.startswith('/-- ') or stripped=='end' or stripped.startswith('end ') or re.match(r'^\s*(?:def|abbrev|structure|inductive|opaque|theorem|instance|partial def)\s+',lines[end]):break
            end+=1
        while end>start+1 and not lines[end-1].strip():end-=1
        raw_block=''.join(lines[start:end]).encode('utf-8')
        assert entry['name'] not in out and raw_block
        out[entry['name']]={'head':entry['head'],'line_start':start+1,'line_end':end,
            'byte_start':sum(len(x.encode('utf-8')) for x in lines[:start]),
            'byte_end':sum(len(x.encode('utf-8')) for x in lines[:end]),
            'bytes':len(raw_block),'sha256':sha(raw_block)}
    assert len(out)==len(entries)
    return out

meta=json.loads((REPORT/'REPORT.json').read_text())
record=json.loads((HERE/'comparison.json').read_text())
source=json.loads((HERE/'source-results.json').read_text())
manifest=json.loads((HERE/'source-handoff-manifest.json').read_text())
source_id=meta['subjects'][0]['identity'];compare_id=meta['subjects'][1]['identity']
assert source_id['reference_revision']=='1332bf21478d8418403d306a7884b653cd735eea'
for field,path in (('source_report_sha256','source-report.md'),('source_results_sha256','source-results.json'),('source_handoff_manifest_sha256','source-handoff-manifest.json'),('source_probe_sha256','source-probe.py')):
    assert source_id[field]==file_sha(HERE/path)
assert json.loads((HERE/'source-report.json').read_text())['subjects'][2]['identity']['sha256']==file_sha(HERE/'source-probe.py')
assert compare_id['compare_sha256']==file_sha(HERE/'compare.py')
assert compare_id['comparison_sha256']==file_sha(HERE/'comparison.json')
assert compare_id['source_results_sha256']==record['source_results_sha256']==file_sha(HERE/'source-results.json')
assert record['source_manifest_sha256']==file_sha(HERE/'source-handoff-manifest.json')
assert record['status']=='completed'
assert record['limits']=={'max_rss_bytes':64*1024**2,'max_seconds':5.0,'min_reclaimable_percent':20.0}
assert record['elapsed_seconds']<=5 and record['peak_rss_bytes']<=64*1024**2
assert len(record['samples'])==16 and record['samples'][0]['label']=='preflight-before-input'
assert all(x['reclaimable_percent']>20 and x['max_rss_bytes']<=64*1024**2 and x['elapsed_seconds']<=5 for x in record['samples'])
assert set(record['cases'])==set(CASES) and set(record['comparisons'])==set(CASES)-{'base'}
replayed={}
for case in CASES:
    x=record['cases'][case];e=source['extractions'][case];t=source['translations'][case]
    assert t['exit']==0
    for suffix,field in (('rs','source_sha256'),('llbc','llbc_sha256')):
        actual=file_sha(HERE/'inputs'/f'{case}.{suffix}')
        assert actual==x['inputs'][suffix]==e[field]
    assert x['inputs']['llbc']==t['input_sha256']
    assert set(x['files'])==set(t['declaration_manifest'])=={'Current.lean','Funs.lean','Types.lean'}
    flat={}
    for filename,ref in t['declaration_manifest'].items():
        raw=(HERE/'outputs'/case/filename).read_bytes()
        item=x['files'][filename]
        assert sha(raw)==item['sha256']==ref['sha256']==manifest['generations'][case]['generated_files'][filename]['sha256']
        assert len(raw)==item['bytes']==ref['bytes']
        actual=blocks(raw,ref['declarations'])
        assert actual==item['blocks']
        for name,block in actual.items():
            key=f'{filename}::{name}'
            assert key not in flat
            flat[key]=block
    assert x['declaration_count']==len(flat)
    replayed[case]=flat
base=replayed['base']
for case in CASES[1:]:
    now=replayed[case];shared=set(base)&set(now)
    expected={'added':sorted(set(now)-set(base)),'removed':sorted(set(base)-set(now)),
              'changed':sorted(k for k in shared if now[k]['sha256']!=base[k]['sha256']),
              'unchanged':sorted(k for k in shared if now[k]['sha256']==base[k]['sha256']),
              'line_moved':sorted(k for k in shared if now[k]['line_start']!=base[k]['line_start'])}
    assert expected==record['comparisons'][case],case
assert record['comparisons']['function_body']['changed']==['Funs.lean::identity_probe.step']
assert record['comparisons']['type_shape']['changed']==['Funs.lean::identity_probe.Wrap.Insts.Identity_probeBump.bump','Types.lean::identity_probe.Wrap']
assert record['comparisons']['trait_impl']['changed']==['Funs.lean::identity_probe.Wrap.Insts.Identity_probeBump.bump']
assert record['comparisons']['recursive_group']['changed']==['Funs.lean::identity_probe.even']
assert record['comparisons']['helper_insert']['added']==['Funs.lean::identity_probe.helper']
assert record['comparisons']['delete_step']['removed']==['Funs.lean::identity_probe.step','Funs.lean::identity_probe.use_step']
assert sum(x['declaration_count'] for x in record['cases'].values())==83
print('PASS: seven exact source/LLBC inputs, 21 generated files, 83 lexical blocks, six comparisons, controls and resource limits')
