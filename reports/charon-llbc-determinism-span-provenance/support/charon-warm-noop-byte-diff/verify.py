#!/usr/bin/env python3
"""Validate retained same-path LLBC byte diff and source-order evidence."""
import hashlib,json
from pathlib import Path

HERE=Path(__file__).resolve().parent
x=json.loads((HERE/'results.json').read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert len(x['runs'])==5 and len(x['comparisons'])==4
assert {r['run'] for r in x['runs']}=={1,2,3,4,5}
assert all(r['exit']==0 and r['bytes']==x['runs'][0]['bytes'] and r['has_errors'] is False and r['crate_name']=='r37u0' for r in x['runs'])
assert len({r['sha256'] for r in x['runs']})>=2
assert [r['mtime_ns'] for r in x['runs']]==sorted(r['mtime_ns'] for r in x['runs'])
for name,h in x['artifact_sha256'].items():assert sha(HERE/'artifacts'/name)==h,name
for name,h in x['diff_sha256'].items():assert sha(HERE/'diffs'/name)==h,name
assert x['source_manifest_sha256']=={
 str(p.relative_to(HERE/'fixture')):sha(p) for p in sorted((HERE/'fixture').rglob('*')) if p.is_file()}
span=x['isolated_region'];base=(HERE/'artifacts/run-1.llbc').read_bytes()
start=base.index(b'"short_names":');end=base.index(b',"type_decls":',start)
assert (span['start_byte'],span['end_byte_exclusive'],span['length_bytes'])==(start,end,end-start)
assert span['length_bytes']==225
prefix=base[:start];suffix=base[end:]
assert hashlib.sha256(prefix).hexdigest()==span['common_prefix_sha256']
assert hashlib.sha256(suffix).hexdigest()==span['common_suffix_sha256']
orders=[]
for i in range(1,6):
 raw=(HERE/f'artifacts/run-{i}.llbc').read_bytes();d=json.loads(raw)
 assert raw[:start]==prefix and raw[end:]==suffix
 assert sha(HERE/f'artifacts/run-{i}.llbc')==x['runs'][i-1]['sha256']
 names=d['translated']['short_names'];order=[z['key']['Fun'] for z in names]
 assert sorted(order)==[0,1,2,3]
 orders.append(order)
 field=b'"short_names":'+json.dumps(sorted(names,key=lambda z:z['key']['Fun']),separators=(',',':')).encode()
 assert hashlib.sha256(prefix+field+suffix).hexdigest()==span['canonical_sha256']
assert orders==span['short_name_fun_id_order'] and len({tuple(o) for o in orders})>=2
assert sha(HERE/'artifacts/canonical-sorted-short-names.llbc')==span['canonical_sha256']
for i,c in enumerate(x['comparisons'],1):
 assert (c['from'],c['to'])==(i,i+1)
 a=(HERE/f'artifacts/run-{i}.llbc').read_bytes();b=(HERE/f'artifacts/run-{i+1}.llbc').read_bytes()
 assert c['same_bytes']==(a==b) and c['same_parsed_json']==(json.loads(a)==json.loads(b))
 if a==b:
  assert c['first_different_byte_offset'] is None and c['json_changed_leaf_count']==0
 else:
  assert start<=c['first_different_byte_offset']<end
  assert c['json_changed_leaf_count']>0
 assert all(z['path'].startswith('$.translated.short_names[') for z in c['json_changed_leaves'])
 assert c['diff_sha256']==sha(HERE/f'diffs/run-{i}-to-{i+1}.diff')
inspection=json.loads((HERE/'source-inspection.json').read_text())
assert len(inspection['source_commit'])==40
assert 'HashMap<String, FoundName>' in str(inspection['files']['compute_short_names']['excerpts'])
assert 'for (short, found) in short_names' in str(inspection['files']['compute_short_names']['excerpts'])
assert 'SeqHashMapToArray' in str(inspection['files']['translated_crate']['excerpts'])
assert 'serializer.collect_seq(map.into_iter()' in str(inspection['files']['sequence_serializer']['excerpts'])
print('PASS: five equal-length runs vary only short_names order; canonical bytes agree')
