#!/usr/bin/env python3
"""Offline retained-byte, map, context and Lean outcome checks for I028."""
from pathlib import Path
import hashlib,json
from probe import Input,construct

HERE=Path(__file__).resolve().parent
R=json.loads((HERE/'results.json').read_text())
assert R['schema']==1 and set(R['cases'])=={'valid','incomplete','import-edit','unicode-crlf'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def messages_batch(c):return [(d['severity'],d['data']) for d in c['batch_file']['diagnostics']]
def messages_live(c):return [({1:'error',3:'information'}[d['severity']],d['message']) for x in c['live']['diagnostics'] for d in x['diagnostics']]
module_hashes={}
for name,c in R['cases'].items():
    a=HERE/'artifacts'/name
    for file in ('annotation','import.lean','file.lean','stream.lean','map.json'):assert (a/file).is_file()
    annotation=(a/'annotation').read_bytes().decode();source=Input(name,c['input']['module'],annotation)
    plan=construct(source);full=plan.text().encode()
    assert (a/'file.lean').read_bytes()==(a/'stream.lean').read_bytes()==full
    assert c['file_sha256']==c['stream_sha256']==sha(a/'file.lean')==sha(a/'stream.lean')
    assert c['file_bytes']==len(full) and c['input']['annotation_sha256']==sha(a/'annotation')
    assert c['input']['annotation_bytes']==len(annotation.encode())
    assert c['segments']==[{'kind':x.kind,'sha256':hashlib.sha256(x.text.encode()).hexdigest(),'bytes':len(x.text.encode())} for x in plan.segments]
    assert c['import_source_sha256']==sha(a/'import.lean')
    assert c['source_map_sha256']==sha(a/'map.json')
    assert json.loads((a/'map.json').read_text())==plan.source_map()
    points=plan.source_map()['points'];assert len(points)==len(annotation)+1
    assert points[0]['generated_utf8']==len(plan.segments[0].text.encode())
    assert points[-1]['generated_utf8']==len((plan.segments[0].text+annotation).encode())
    assert all(q['generated_utf8']-q['source_utf8']==len(plan.segments[0].text.encode()) for q in points)
    assert all(points[i]['source_utf8']<points[i+1]['source_utf8'] and points[i]['generated_utf8']<points[i+1]['generated_utf8'] for i in range(len(points)-1))
    module_hashes.setdefault(source.module,set()).add(c['import_olean_sha256'])
    f,s=c['batch_file'],c['batch_stream']
    assert (f['rc'],f['stdout'],f['stderr'],f['diagnostics'])==(s['rc'],s['stdout'],s['stderr'],s['diagnostics'])
    assert c['live']['versions']==3 and c['live']['virtual_file_absent_at_final']
    assert c['live']['wait']['result']=={} and c['live']['process']['rc']==0
    assert messages_batch(c)==messages_live(c),(name,messages_batch(c),messages_live(c))
    changes=[m['message']['method'] for m in c['live']['messages'] if m['direction']=='client' and m['message'].get('method') in ('textDocument/didOpen','textDocument/didChange')]
    assert changes==['textDocument/didOpen','textDocument/didChange','textDocument/didChange']
    expected_rc=1 if name in ('incomplete','import-edit') else 0
    assert f['rc']==expected_rc
    data=[d['data'] for d in f['diagnostics']]
    assert 'Generated.checked : depValue = 7' in data
    assert any(('depends on axioms: [sorryAx]' if expected_rc else 'does not depend on any axioms') in x for x in data)
    if name=='incomplete':assert any('unsolved goals' in x for x in data)
    if name=='import-edit':assert any('is false' in x for x in data)
assert len(module_hashes['Base'])==len(module_hashes['Alt'])==1
assert module_hashes['Base']!=module_hashes['Alt']
uni=R['cases']['unicode-crlf'];ann=(HERE/'artifacts/unicode-crlf/annotation').read_bytes().decode()
assert '\r\n' in ann and 'λ😀' in ann
pts=json.loads((HERE/'artifacts/unicode-crlf/map.json').read_text())['points']
i=ann.index('😀');assert pts[i+1]['source_utf16']['character']-pts[i]['source_utf16']['character']==2
assert pts[i+1]['generated_utf16']['character']-pts[i]['generated_utf16']['character']==2
print('OK: four shared plans, byte-identical file/live sinks, exhaustive source maps, import context, batch/LSP messages and acceptance')
