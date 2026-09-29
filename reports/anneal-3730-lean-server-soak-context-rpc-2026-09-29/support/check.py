#!/usr/bin/env python3
"""Offline integrity/behavior checks for the retained bounded R11 transcript."""
import hashlib,json
from pathlib import Path

HERE=Path(__file__).resolve().parent;events=json.loads((HERE/'transcript.json').read_text());work=HERE/'work'
assert [e['seq'] for e in events]==list(range(len(events)))
assert not any(e['kind']=='fatal' for e in events)
assert events[-1]['kind']=='finish'
one=lambda kind,label:next(e for e in events if e['kind']==kind and e.get('label')==label)
subject=next(e for e in events if e['kind']=='subject')
assert subject['lean_version'].startswith('Lean (version 4.30.0-rc2,')
for name,value in [('A',11),('B',22)]:
    e=next(x for x in events if x['kind']=='compile' and x['root']==name)
    assert e['value']==value and e['rc']==0
    assert hashlib.sha256((work/name/'Dep.lean').read_bytes()).hexdigest()==e['source_sha256']
    assert hashlib.sha256((work/name/'Dep.olean').read_bytes()).hexdigest()==e['olean_sha256']
for label in ['A-first','B']:
    c=one('cycle',label);assert c['rounds']==12 and len(c['checks'])==12
    assert all(z['goal_ok'] for z in c['checks'])
    assert len([e for e in events if e['kind']=='reopen' and e['label']==label])==2
    for e in [e for e in events if e['kind']=='reopen' and e['label']==label]:
        assert e['stale']['error']['code']==-32900
    refs=[e for e in events if e['kind']=='rpc_reference' and e['label']==label]
    assert len(refs)==5 and refs[0]['info_ref'] is not None and 'result' in refs[0]['popup']
    releases=[e for e in events if e['kind']=='release_control' and e['label']==label]
    assert len(releases)==1 and releases[0]['response']['error']['code']==-32602
    assert 'not valid' in releases[0]['response']['error']['message']
    assert one('stop',label)['rc']==0 and one('stop',label)['after']['count']==0
restart=next(e for e in events if e['kind']=='restart')
assert restart['old']['error']['code']==-32900 and 'result' in restart['new']
assert one('stop','A-restart')['after']['count']==0
wrong=one('wrong_import','A-first')
assert any(d.get('message')=='11' for d in wrong['diagnostics']['diagnostics'])
assert any('not definitionally equal' in d.get('message','') for d in wrong['diagnostics']['diagnostics'])
deadline=next(e for e in events if e['kind']=='client_deadline')
timeout=next(e for e in events if e['kind']=='timeout_control')
assert deadline['elapsed_ms']>=100 and timeout['reply'].get('client_wait_error')
assert 'n = 22' in json.dumps(timeout['recovered']) and one('stop','timeout')['after']['count']==0
post=next(e for e in events if e['kind']=='post_timeout_restart')
assert 'n = 22' in json.dumps(post['goal']) and 'result' in post['rich']
assert one('stop','post-timeout-restart')['rc']==0 and one('stop','post-timeout-restart')['after']['count']==0
for e in [e for e in events if e['kind']=='guard']:
    assert not e['violations']
    assert e['tree']['rss_bytes']<=subject['limits']['rss']
    assert e['tree']['count']<=subject['limits']['processes']
    assert e['inventory']['blocks_bytes']<=subject['limits']['disk']
    assert e['free_percent']>=subject['limits']['free']
print(f"OK: {len(events)} events; 24 edits, 4 reopens, reference release, wrong import, clean timeout/restart and cleanup")
