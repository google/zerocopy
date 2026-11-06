#!/usr/bin/env python3
"""Guarded ASCII-only local Charon span/source-text check on retained LLBCs."""
import hashlib
import json
import re
import resource
import signal
import subprocess
import time
from pathlib import Path

HERE=Path(__file__).resolve().parent
MAX_RSS=64*1024**2
MAX_SECONDS=5.0
MIN_RECLAIMABLE=20.0
started=time.monotonic()
samples=[]
class Refusal(Exception):pass

def alarm(*_):raise Refusal('five-second wall-time cap')
signal.signal(signal.SIGALRM,alarm)
signal.setitimer(signal.ITIMER_REAL,MAX_SECONDS)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def guard(label):
    elapsed=time.monotonic()-started
    rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    if rss>MAX_RSS:raise Refusal(f'RSS {rss} > {MAX_RSS} at {label}')
    if elapsed>MAX_SECONDS:raise Refusal(f'elapsed {elapsed} > {MAX_SECONDS} at {label}')
    vm=subprocess.run(['/usr/bin/vm_stat'],capture_output=True,text=True,timeout=1,check=True).stdout
    page=int(re.search(r'page size of (\d+) bytes',vm).group(1))
    counts=[int(re.search(rf'Pages {name}:\s+(\d+)\.',vm).group(1)) for name in ('free','inactive','speculative')]
    physical=int(subprocess.run(['/usr/sbin/sysctl','-n','hw.memsize'],capture_output=True,text=True,timeout=1,check=True).stdout.strip())
    pct=100*page*sum(counts)/physical
    samples.append({'label':label,'reclaimable_percent':pct,'max_rss_bytes':rss,'elapsed_seconds':elapsed,'physical_bytes':physical})
    if pct<=MIN_RECLAIMABLE:raise Refusal(f'reclaimable {pct:.4f}% <= {MIN_RECLAIMABLE}% at {label}')

def name(meta):
    return '::'.join(part['Ident'][0] for part in meta['name'] if 'Ident' in part)
def source_slice(raw,span):
    b,e=span['beg'],span['end']
    assert b['line']==e['line'] and b['line']>=1 and 0<=b['col']<e['col']
    lines=raw.splitlines(keepends=True)
    line=lines[b['line']-1]
    assert e['col']<=len(line)
    return line[b['col']:e['col']]

def main():
    guard('preflight-before-input')
    results_raw=(HERE/'source-results.json').read_bytes()
    assert sha(results_raw)=='e1f8ac94a2bda6f93ca21d11c8fae4c6030bd2f9a9ac5491d2e4b36f981e1d4a'
    results=json.loads(results_raw)
    base=(HERE/'source-states/baseline.rs').read_bytes()
    edited=(HERE/'source-states/edited.rs').read_bytes()
    assert base.isascii() and edited.isascii()
    assert base.count(b'x.wrapping_add(1)')==1 and edited==base.replace(b'x.wrapping_add(1)',b'x.wrapping_add(2)')
    states={'bbe231375dfe3d5ae46a420067496a466ee223e8e2acb2aa54d0c931691d041e':base,
            'd264e3214d6b82cc98a3dc13d3fb4d839d1ed54ccdf705225c17210195e61bae':edited}
    assert all(sha(raw)==digest for digest,raw in states.items())
    expected={}
    for cell in results['cells']:
        assert cell['incremental'] in (0,1) and cell['baseline_sha256'] in states and cell['edited_sha256'] in states
        for state,run in cell['oracle'].items():
            assert state in ('baseline','edited')
            expected[run['label']]=run
        for phase in cell['phases']:
            for root,run in phase['runs'].items():
                assert root in ('A','B') and run['source_sha256']==phase['source_hashes'][root]
                expected[run['label']]=run
    assert len(expected)==16
    out={'status':'completed','source_results_sha256':sha(results_raw),
         'source_state_sha256':{'baseline':sha(base),'edited':sha(edited)},
         'span_interpretation':{'line_numbering':'one-based for the tested local ASCII lines',
             'column_origin':'zero-based for the tested local ASCII lines',
             'end':'exclusive for the tested local ASCII lines',
             'column_unit':'underdetermined: bytes, Unicode scalars and UTF-16 units coincide in this ASCII fixture'},
         'limits':{'max_rss_bytes':MAX_RSS,'max_seconds':MAX_SECONDS,'min_reclaimable_percent':MIN_RECLAIMABLE},
         'artifacts':{},'samples':samples}
    for label in sorted(expected):
        guard(f'before-{label}')
        run=expected[label];raw=(HERE/'artifacts'/f'{label}.llbc').read_bytes()
        assert sha(raw)==run['output']['sha256'] and len(raw)==run['output']['bytes']
        doc=json.loads(raw)
        assert doc['translated']['crate_name']=='warm_probe' and doc['has_errors'] is False
        source=states[run['source_sha256']]
        files={f['id']:f for f in doc['translated']['files']}
        assert files[0]['name']=={'Local':'app/src/lib.rs'}
        assert files[0]['contents'].encode('utf-8')==source
        items=[];excluded=[]
        for category in ('type_decls','fun_decls','global_decls','trait_decls','trait_impls'):
            for decl in doc['translated'][category]:
                meta=decl.get('item_meta') or {}
                span=(meta.get('span') or {}).get('data')
                if not meta.get('is_local') or span is None:continue
                key=name(meta)
                if span['file_id']!=0:
                    excluded.append({'category':category,'name':key,'file_id':span['file_id'],'reason':'no independent retained generated Rust state for this file'})
                    continue
                assert category=='fun_decls'
                text=(meta['source_text'] or '').encode('utf-8')
                assert text and text.isascii()
                selected=source_slice(source,span)
                assert selected==text,(label,key,span,selected,text)
                items.append({'category':category,'name':key,'def_id':decl['def_id'],
                    'span':span,'source_text_sha256':sha(text),'source_text':meta['source_text'],
                    'source_state_sha256':run['source_sha256']})
        assert len(items)==4 and {x['name'] for x in items}=={'warm_probe::step','warm_probe::use_step','warm_probe::payload_len','warm_probe::generated_value'}
        assert len(excluded)==2
        step=next(x for x in items if x['name']=='warm_probe::step')['source_text']
        assert ('wrapping_add(2)' in step)==(run['source_sha256']==sha(edited))
        out['artifacts'][label]={'llbc_sha256':sha(raw),'source_state_sha256':run['source_sha256'],
            'local_ascii_items':items,'excluded_generated_local_items':excluded}
        guard(f'after-{label}')
    # Deliberately wrong offsets must fail against the recorded source_text.
    witness=out['artifacts']['inc0-baseline-A']['local_ascii_items'][0]
    span=witness['span'];start=span['beg']['col'];end=span['end']['col']
    line=base.splitlines(keepends=True)[span['beg']['line']-1]
    assert line[start+1:end]!=witness['source_text'].encode()
    assert line[start:end+1]!=witness['source_text'].encode()
    out['negative_controls']={'shift_start_one_byte_detected':True,'inclusive_end_detected':True,
        'edited_A_step_differs_from_baseline':True,'unchanged_B_step_remains_baseline':True,
        'reverted_A_step_returns_to_baseline':True}
    for inc in (0,1):
        assert out['artifacts'][f'inc{inc}-edited-A']['source_state_sha256']==sha(edited)
        for phase in ('baseline','reverted'):
            assert out['artifacts'][f'inc{inc}-{phase}-A']['source_state_sha256']==sha(base)
        for phase in ('baseline','edited','reverted'):
            assert out['artifacts'][f'inc{inc}-{phase}-B']['source_state_sha256']==sha(base)
    guard('final-before-write')
    out['elapsed_seconds']=time.monotonic()-started
    out['peak_rss_bytes']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    (HERE/'comparison.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'completed','artifacts':len(out['artifacts']),
       'matched_local_ascii_items':sum(len(x['local_ascii_items']) for x in out['artifacts'].values()),
       'excluded_generated_local_items':sum(len(x['excluded_generated_local_items']) for x in out['artifacts'].values()),
       'min_reclaimable_percent':min(x['reclaimable_percent'] for x in samples),
       'peak_rss_bytes':out['peak_rss_bytes'],'elapsed_seconds':out['elapsed_seconds']},sort_keys=True))

if __name__=='__main__':
    try:main()
    except Exception as exc:
        refusal={'status':'refused','reason':str(exc),'samples':samples,
            'elapsed_seconds':time.monotonic()-started,
            'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
        (HERE/'refusal.json').write_text(json.dumps(refusal,indent=2,sort_keys=True)+'\n')
        print(json.dumps(refusal,sort_keys=True))
        raise
