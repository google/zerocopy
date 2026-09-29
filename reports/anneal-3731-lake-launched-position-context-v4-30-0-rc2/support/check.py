#!/usr/bin/env python3
"""Read-only consistency check for the retained Lake-launched position transcript."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
D = json.loads((HERE/'results.json').read_text())
PROBE_SHA256 = '6b97a29086334dac5576288a5e66d73e39e00634d14564600fff97eccb3cb580'

def require(ok, message):
    if not ok:
        raise SystemExit('FAIL: '+message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def display(value):
    if isinstance(value,str): return value
    if isinstance(value,list): return ''.join(display(x) for x in value)
    require(isinstance(value,dict),'unexpected rich display node')
    return value.get('text','')+display(value.get('append',[]))+display(value.get('tag',[]))

require(sha((HERE/'probe.py').read_bytes())==PROBE_SHA256,'probe source digest')
expected_tools = {
    'lake_sha256':'9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb',
    'lean_sha256':'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'}
require(D['tools']==expected_tools,'pinned tool hashes')
require(D['preflight']['disk_free_bytes']>10*1024**3 and D['preflight']['memory_free_percent']>=20,'preflight')
for name in ('Dep.lean','Proof.lean'):
    contents=(HERE/'fixture'/name).read_bytes()
    require(sha(contents)==D['source']['sha256'][name],name+' digest')
    require(contents.decode()==D['source'][name],name+' exact source')
require(D['source']['Dep.lean']=='def depValue : Nat := 7\n','dependency definition')
require('theorem positioned' in D['source']['Proof.lean'] and 'import Dep\n' in D['source']['Proof.lean'],'proof and import')
require(all(D['artifacts'].values()),'compiled artifacts recorded')
require(D['artifacts']['Dep.olean']!=D['artifacts']['Proof.olean'],'distinct module artifacts')
for key in ('build','batch','setup'):
    require(D[key]['exit']==0,key+' exit')
require(['-v','build','Proof']==D['build']['args'],'build command')
require(['--no-cache','env','lean','--json','Proof.lean']==D['batch']['args'],'batch command')
require(['--no-cache','setup-file','Proof.lean']==D['setup']['args'],'setup command')
require('Built Dep' in D['build']['stdout'] and 'Built Proof' in D['build']['stdout'],'actual build actions')
require("'positioned' does not depend on any axioms" in D['build']['stdout'],'build axiom result')
batch_info=[json.loads(line)['data'] for line in D['batch']['stdout'].splitlines() if line.startswith('{')]
require(batch_info==["'positioned' does not depend on any axioms",'7'],'batch axiom and import value')
setup=json.loads(D['setup']['stdout'])
require(setup['name']=='Proof' and setup['package']=='position_probe','setup identity')
require(setup['importArts']=={'Dep':['$WORK/dep/.lake/build/lib/lean/Dep.olean']},'setup imported artifact')
require(D['wait'].get('result')=={},'diagnostic readiness response')
require(isinstance(D['connect'].get('result',{}).get('sessionId'),str),'rich RPC session')
require(D['stop']=={'exit':0,'stderr':''},'server shutdown')
expected_positions={'outer_have':[3,2],'inner_start':[4,4],'inner_inside':[4,8],
                    'inner_end':[4,17],'outer_exact':[5,2],'outer_exact_end':[5,10],
                    'eof':[8,0]}
require(D['positions']==expected_positions,'position grid')
expected={
 'outer_have':'n : Nat\nh : n = depValue\n⊢ n + 0 = depValue',
 'inner_start':'n : Nat\nh : n = depValue\n⊢ n + 0 = depValue',
 'inner_inside':'n : Nat\nh : n = depValue\n⊢ n = depValue',
 'inner_end':[],
 'outer_exact':'n : Nat\nh : n = depValue\nhz : n + 0 = depValue\n⊢ n + 0 = depValue',
 'outer_exact_end':[],
 'eof':None}
require(set(D['live'])==set(expected),'sample names')
for name,want in expected.items():
    case=D['live'][name]
    line,col=expected_positions[name]
    require(case['position']=={'line':line,'character':col},name+' request position')
    plain,rich=case['plain'].get('result'),case['rich'].get('result')
    if want is None:
        require(plain is None and rich is None,name+' null pair')
        continue
    require(isinstance(plain,dict) and isinstance(rich,dict),name+' goal response shape')
    if want==[]:
        require(plain['goals']==[] and rich['goals']==[],name+' empty pair')
        continue
    require(plain['goals']==[want],name+' plain goal/context')
    require(len(rich['goals'])==1,name+' rich goal count')
    g=rich['goals'][0]
    rich_text='\n'.join([f"{','.join(h['names'])} : {display(h['type'])}" for h in g['hyps']]+[g['goalPrefix']+display(g['type'])])
    require(rich_text==want,name+' rich goal/context')
# The wire transcript must contain one opened document and each paired query.
client=[x['message'] for x in D['events'] if x['direction']=='client']
server=[x['message'] for x in D['events'] if x['direction']=='server']
opened=[x for x in client if x.get('method')=='textDocument/didOpen']
connections=[x for x in client if x.get('method')=='$/lean/rpc/connect']
require(len(connections)==1,'one rich RPC connection')
doc={'uri':'$WORK_URI/project/Proof.lean','version':1}
require(len(opened)==1 and opened[0]['params']['textDocument']==
        {**doc,'languageId':'lean','text':D['source']['Proof.lean']},'opened exact source/URI/version')
require(not [x for x in client if x.get('method') in ('textDocument/didChange','textDocument/didClose')],
        'single unchanged open document')
waits=[x for x in client if x.get('method')=='textDocument/waitForDiagnostics']
require(len(waits)==1 and waits[0]['params']==doc,'versioned wait request')
require(connections[0]['params']=={'uri':doc['uri']},'rich connection URI')
for request,retained,label in ((waits[0],D['wait'],'wait'),(connections[0],D['connect'],'connect')):
    require(len([m for m in server if m.get('id')==request['id'] and 'method' not in m])==1,
            label+' response count')
    require(next(m for m in server if m.get('id')==request['id'] and 'method' not in m)==retained,
            label+' wire response')
require(client.index(opened[0])<client.index(waits[0])<client.index(connections[0]),
        'open/wait/connect request order')
rich_calls=[x for x in client if x.get('method')=='$/lean/rpc/call']
require({x['params']['sessionId'] for x in rich_calls}=={D['connect']['result']['sessionId']},'one retained rich session')
for method in ('$/lean/plainGoal','$/lean/rpc/call'):
    requests=[x for x in client if x.get('method')==method]
    require(len(requests)==7,method+' request count')
    require([x['params']['position'] for x in requests]==[D['live'][n]['position'] for n in expected],method+' ordered positions')
    for x in requests:
        require(x['params']['textDocument']==doc,method+' document identity')
        if method=='$/lean/rpc/call':
            require(x['params']['method']=='Lean.Widget.getInteractiveGoals' and
                    x['params']['params']=={'textDocument':doc,'position':x['params']['position']},
                    'rich nested method/document/position')
        matches=[m for m in server if m.get('id')==x['id'] and 'method' not in m]
        require(len(matches)==1,method+' response pairing')
        sample=next(v for v in D['live'].values() if v['position']==x['params']['position'])
        require(matches[0]==sample['plain' if method=='$/lean/plainGoal' else 'rich'],method+' retained reply')
notices=[m for m in server if m.get('method')=='textDocument/publishDiagnostics']
require(notices and all(m['params']['uri']==doc['uri'] and m['params']['version']==doc['version']
                        for m in notices),'diagnostic URI/version')
require(all(d.get('severity')!=1 for m in notices for d in m['params']['diagnostics']),
        'no live error diagnostics')
print('PASS: Lake position transcript; 7 plain/rich pairs, 4 goals, 2 empty, 1 null; clean batch and import controls')
