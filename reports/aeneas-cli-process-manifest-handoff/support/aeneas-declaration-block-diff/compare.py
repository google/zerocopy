#!/usr/bin/env python3
"""Guarded lexical declaration-block comparison of copied, retained Aeneas outputs."""
import hashlib
import json
import re
import resource
import signal
import subprocess
import time
from pathlib import Path

HERE=Path(__file__).resolve().parent
CASES=('base','function_body','type_shape','trait_impl','recursive_group','helper_insert','delete_step')
MAX_RSS=64*1024**2
MAX_SECONDS=5.0
MIN_RECLAIMABLE=20.0
started=time.monotonic()
samples=[]
class Refusal(Exception): pass

def alarm(*_): raise Refusal('five-second wall-time cap')
signal.signal(signal.SIGALRM,alarm)
signal.setitimer(signal.ITIMER_REAL,MAX_SECONDS)

def sha(raw): return hashlib.sha256(raw).hexdigest()
def guard(label):
    elapsed=time.monotonic()-started
    rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    if rss>MAX_RSS: raise Refusal(f'RSS {rss} > {MAX_RSS} at {label}')
    if elapsed>MAX_SECONDS: raise Refusal(f'elapsed {elapsed} > {MAX_SECONDS} at {label}')
    vm=subprocess.run(['/usr/bin/vm_stat'],capture_output=True,text=True,timeout=1,check=True).stdout
    page=int(re.search(r'page size of (\d+) bytes',vm).group(1))
    counts=[int(re.search(rf'Pages {name}:\s+(\d+)\.',vm).group(1)) for name in ('free','inactive','speculative')]
    physical=int(subprocess.run(['/usr/sbin/sysctl','-n','hw.memsize'],capture_output=True,text=True,timeout=1,check=True).stdout.strip())
    pct=100*page*sum(counts)/physical
    samples.append({'label':label,'reclaimable_percent':pct,'max_rss_bytes':rss,'elapsed_seconds':elapsed,'physical_bytes':physical})
    if pct<=MIN_RECLAIMABLE: raise Refusal(f'reclaimable {pct:.4f}% <= {MIN_RECLAIMABLE}% at {label}')

def blocks(raw,manifest):
    text=raw.decode('utf-8')
    lines=text.splitlines(keepends=True)
    heads=manifest['declarations']
    found={}
    for idx,decl in enumerate(heads):
        n=decl['line']-1
        assert 0<=n<len(lines) and lines[n].strip()==decl['head']
        assert re.match(r'^\s*(?:def|abbrev|structure|inductive|opaque|theorem|instance|partial def)\s+([^\s(:]+)',lines[n])
        stop=len(lines)
        for j in range(n+1,len(lines)):
            s=lines[j].strip()
            if s.startswith('/-- ') or s=='end' or s.startswith('end ') or re.match(r'^\s*(?:def|abbrev|structure|inductive|opaque|theorem|instance|partial def)\s+',lines[j]):
                stop=j;break
        assert idx+1==len(heads) or stop<=heads[idx+1]['line']-1
        while stop>n+1 and not lines[stop-1].strip():stop-=1
        body=''.join(lines[n:stop]).encode('utf-8')
        key=decl['name']
        assert key not in found and body
        found[key]={'head':decl['head'],'line_start':n+1,'line_end':stop,
                    'byte_start':len(''.join(lines[:n]).encode('utf-8')),
                    'byte_end':len(''.join(lines[:stop]).encode('utf-8')),
                    'bytes':len(body),'sha256':sha(body)}
    return found

def main():
    guard('preflight-before-input')
    results_raw=(HERE/'source-results.json').read_bytes()
    manifest_raw=(HERE/'source-handoff-manifest.json').read_bytes()
    assert sha(results_raw)=='694c43532ac90504947bd5cfe9e34369cae68e2164683e8c3f772138022d45b4'
    assert sha(manifest_raw)=='e9870d6f9844eb5ebc192d297d642319333549aac483d9f9a3322c75ba3c8826'
    results=json.loads(results_raw);manifest=json.loads(manifest_raw)
    record={'status':'completed','limits':{'max_rss_bytes':MAX_RSS,'max_seconds':MAX_SECONDS,'min_reclaimable_percent':MIN_RECLAIMABLE},
            'source_results_sha256':sha(results_raw),'source_manifest_sha256':sha(manifest_raw),
            'cases':{},'comparisons':{},'samples':samples}
    for case in CASES:
        guard(f'before-{case}')
        extraction=results['extractions'][case];translation=results['translations'][case]
        assert translation['exit']==0
        inputs={}
        for suffix,key in (('rs','source_sha256'),('llbc','llbc_sha256')):
            raw=(HERE/'inputs'/f'{case}.{suffix}').read_bytes()
            assert sha(raw)==extraction[key]
            inputs[suffix]=sha(raw)
        assert inputs['llbc']==translation['input_sha256']
        file_records={};flat={}
        assert set(translation['declaration_manifest'])=={'Current.lean','Funs.lean','Types.lean'}
        for filename,reference in translation['declaration_manifest'].items():
            raw=(HERE/'outputs'/case/filename).read_bytes()
            assert sha(raw)==reference['sha256'] and len(raw)==reference['bytes']
            assert manifest['generations'][case]['generated_files'][filename]['sha256']==sha(raw)
            b=blocks(raw,reference)
            file_records[filename]={'sha256':sha(raw),'bytes':len(raw),'blocks':b}
            for name,item in b.items():
                key=f'{filename}::{name}'
                assert key not in flat
                flat[key]=item
        record['cases'][case]={'inputs':inputs,'files':file_records,'declaration_count':len(flat)}
        if case!='base':
            baseline={f'{f}::{n}':x for f,y in record['cases']['base']['files'].items() for n,x in y['blocks'].items()}
            added=sorted(set(flat)-set(baseline));removed=sorted(set(baseline)-set(flat))
            common=set(flat)&set(baseline)
            changed=sorted(k for k in common if flat[k]['sha256']!=baseline[k]['sha256'])
            unchanged=sorted(common-set(changed))
            moved=sorted(k for k in common if flat[k]['line_start']!=baseline[k]['line_start'])
            record['comparisons'][case]={'added':added,'removed':removed,'changed':changed,'unchanged':unchanged,'line_moved':moved}
        guard(f'after-{case}')
    checks={
      'function_body':'Funs.lean::identity_probe.step',
      'type_shape':'Types.lean::identity_probe.Wrap',
      'trait_impl':'Funs.lean::identity_probe.Wrap.Insts.Identity_probeBump.bump',
      'recursive_group':'Funs.lean::identity_probe.even'}
    for case,key in checks.items():
        assert key in record['comparisons'][case]['changed'],(case,key)
    assert 'Funs.lean::identity_probe.helper' in record['comparisons']['helper_insert']['added']
    assert {'Funs.lean::identity_probe.step','Funs.lean::identity_probe.use_step'}<=set(record['comparisons']['delete_step']['removed'])
    guard('final-before-write')
    record['elapsed_seconds']=time.monotonic()-started
    record['peak_rss_bytes']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    (HERE/'comparison.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'completed','cases':len(record['cases']),'comparisons':{k:{n:len(v[n]) for n in ('added','removed','changed','unchanged','line_moved')} for k,v in record['comparisons'].items()},'minimum_reclaimable_percent':min(s['reclaimable_percent'] for s in samples),'peak_rss_bytes':record['peak_rss_bytes'],'elapsed_seconds':record['elapsed_seconds']},sort_keys=True))

if __name__=='__main__':
    try:main()
    except Exception as e:
        refusal={'status':'refused','reason':str(e),'samples':samples,'elapsed_seconds':time.monotonic()-started,'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
        (HERE/'refusal.json').write_text(json.dumps(refusal,indent=2,sort_keys=True)+'\n')
        print(json.dumps(refusal,sort_keys=True))
        raise
