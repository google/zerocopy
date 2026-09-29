#!/usr/bin/env python3
"""Check archived R16 evidence without starting Lean."""
import hashlib,json
from pathlib import Path

HERE=Path(__file__).resolve().parent;events=json.loads((HERE/'transcript.json').read_text())
pilot=json.loads((HERE/'pilot-id-collision.json').read_text())
assert pilot[-1]['kind']=='fatal' and 'workspace/inlayHint/refresh' in pilot[-1]['error']
assert any(e['kind']=='server' and e.get('message',{}).get('method')=='workspace/inlayHint/refresh'
           and e['message'].get('id')==23 for e in pilot)
assert all(e['after']['count']==0 for e in pilot if e['kind']=='stop')
assert [e['seq'] for e in events]==list(range(len(events)))
assert not any(e['kind'] in ('fatal','watchdog_abort') for e in events)
subject=next(e for e in events if e['kind']=='subject')
assert subject['lean_version'].startswith('Lean (version 4.30.0-rc2,')
limits=subject['limits']
for e in events:
    if e['kind']=='guard':
        assert not e['violations']
        assert e['tree']['rss_bytes']<=limits['rss']
        assert e['tree']['count']<=limits['processes']
        assert e['inventory']['blocks_bytes']<=limits['disk']
        assert e['free_percent']>=limits['free']
    if e['kind']=='stop':assert e['rc']==0 and e['after']['count']==0
assert events[-1]['kind']=='finish'
cells={e['label']:e for e in events if e['kind']=='cell'}
if events[-1]['status']=='all-skipped':
    assert {k:v['status'] for k,v in cells.items()}=={'A-1':'skipped','A-2':'skipped','A-4':'skipped'}
    print('OK: all three ramp cells explicitly skipped by host preflight')
    raise SystemExit
assert events[-1]['status']=='completed' and events[-1]['ms']>=120000
for root in ['A','B']:
    c=next(e for e in events if e['kind']=='compile' and e['root']==root)
    assert c['rc']==0
    for ext,key in [('lean','source_sha256'),('olean','olean_sha256')]:
        p=HERE/'work'/root/f'Dep.{ext}'
        assert hashlib.sha256(p.read_bytes()).hexdigest()==c[key]
assert cells['A-1']['status']==cells['A-2']['status']==cells['B-1']['status']=='completed'
assert cells['A-4']['status'] in ('completed','skipped')
admission=next(e for e in events if e['kind']=='four_admission')
assert admission['allowed']==(cells['A-4']['status']=='completed')
for label,workers,rounds,base in [('A-1',1,9,11),('A-2',2,9,11),('A-4',4,9,11),('B-1',1,6,22)]:
    cell=cells[label]
    if cell['status']=='skipped':
        assert label=='A-4' and cell['reason'];continue
    assert cell['workers']==workers and cell['rounds']==rounds
    assert len(cell['checks'])==workers*rounds
    assert all(z['ok'] and f'n = {base+z["file"]}' in json.dumps(z['goal']) for z in cell['checks'])
    assert any(e['kind']=='rpc_release' and e['label']==label and e['after']['error']['code']==-32602 for e in events)
    assert any(e['kind']=='reopen' and e['label']==label and e['stale']['error']['code']==-32900 for e in events)
    assert any(e['kind']=='stop' and e['label']==label and e['after']['count']==0 for e in events)
for label in ['A-2','A-4']:
    if cells[label]['status']=='completed':
        assert any(e['kind']=='prior_server_session' and e['label']==label and e['response']['error']['code']==-32900 for e in events)
cross=next(e for e in events if e['kind']=='cross_import')
messages=[d.get('message','') for d in cross['diagnostics']['diagnostics']]
assert cross['server_import']==22 and cross['expected_local']==11
assert '22' in messages and any('not definitionally equal' in m for m in messages)
assert events[-1]['ms']/1000<=limits['seconds']
print(f"OK: {len(events)} events; {sum(v['status']=='completed' for v in cells.values())} cells; multi-minute sentinel/RPC/resource/cleanup checks")
