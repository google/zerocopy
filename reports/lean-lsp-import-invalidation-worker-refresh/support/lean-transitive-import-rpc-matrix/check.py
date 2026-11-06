#!/usr/bin/env python3
"""Assert bounded Lean/Lake and RPC observations from the retained transcript."""
import hashlib,json
from pathlib import Path
H=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=json.loads((H/'transcript.json').read_text())
assert [x['seq'] for x in rows]==list(range(len(rows)))
by=lambda kind:{x['version']:x for x in rows if x['kind']==kind and 'version' in x}
subjects=by('subject');matrices=by('matrix');initial=by('rpc_initial');retained=by('rpc_retained_release');restarted=by('rpc_after_restart');delayed=by('causal_delay')
commands={x['label']:x for x in rows if x['kind']=='command'}
assert set(subjects)==set(matrices)==set(initial)==set(retained)==set(restarted)==set(delayed)=={'4.29.0','4.30.0-rc2'}
assert len(rows)==588
def messages(sample):return [x.get('message','') for x in (sample['diagnostics'] or {}).get('diagnostics',[])]
def nogoal(reply):return reply.get('result',{}).get('rendered')=='no goals'
def hasgoal(reply,target):return any(target in g for g in reply.get('result',{}).get('goals',[]))
summary={}
for version in subjects:
    m=matrices[version];old=m['old'];before=m['old_after_change'];new=m['new'];after=m['old_after_new'];fresh=m['reopened']
    assert m['setup_before']['options']=={'pp.universes':False}
    assert m['setup_after']['options']=={'pp.universes':True}
    assert set(m['setup_before']['importArts'])==set(m['setup_after']['importArts'])=={'Base','Mid'}
    for s in (old,before,after):
        assert '7' in messages(s) and 'OPTION=false' in messages(s)
        assert nogoal(s['goal_data']) and nogoal(s['goal_macro'])
    for s in (new,fresh):
        assert '9' in messages(s) and 'OPTION=true' in messages(s)
        assert hasgoal(s['goal_data'],'transitive 7') and hasgoal(s['goal_macro'],'True')
    assert old['marker']=='plugin-v1' and before['marker']=='plugin-v1'
    assert new['marker']==after['marker']==fresh['marker']=='plugin-v2'
    assert old['artifacts']['Base.olean']!=new['artifacts']['Base.olean']
    assert old['artifacts']['Mid.olean']!=new['artifacts']['Mid.olean']
    assert new['artifacts']==after['artifacts']==fresh['artifacts']
    assert m['batch_rc']==1
    i=initial[version];t=retained[version];r=restarted[version];d=delayed[version]
    assert i['info_ref'] and i['deref']['result']
    assert t['ref']==i['info_ref'] and t['retained']['result']
    assert t['after_release']['error']['code']==-32602
    assert 'not valid' in t['after_release']['error']['message']
    assert r['old_session']['error']['code']==-32900 and r['new_rich']['result']['goals']
    assert d['reused_request_id']==50 and d['fast']['id']==d['delayed']['id']==50
    assert hasgoal(d['fast'],'False') and hasgoal(d['delayed'],'True')
    assert commands['batch-after-'+version]['rc']==1
    for k in ('old','old_after_change','new','old_after_new','reopened'):
        assert m[k]['tree']['rss_bytes']<3*1024**3
    summary[version]=dict(lean_sha256=subjects[version]['lean_sha256'],lake_sha256=subjects[version]['lake_sha256'],
                          before_olean={k:old['artifacts'][k] for k in ('Base.olean','Mid.olean')},
                          after_olean={k:new['artifacts'][k] for k in ('Base.olean','Mid.olean')},
                          before_plugin=old['artifacts']['rpc__matrix_Plugin.dylib'],
                          after_plugin=new['artifacts']['rpc__matrix_Plugin.dylib'],
                          max_main_rss_bytes=max(m[k]['tree']['rss_bytes'] for k in ('old','old_after_change','new','old_after_new')),
                          gated_rss_bytes=d['tree']['rss_bytes'])
stops=[x for x in rows if x['kind']=='stop']
assert len(stops)==6 and all(x['rc']==0 for x in stops)
out=dict(status='bounded assertions passed',events=len(rows),probe_sha256=sha(H/'probe.py'),transcript_sha256=sha(H/'transcript.json'),versions=summary,max_sampled_rss_bytes=max(x['tree']['rss_bytes'] for x in rows if x['kind']=='sample'))
(H/'summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
