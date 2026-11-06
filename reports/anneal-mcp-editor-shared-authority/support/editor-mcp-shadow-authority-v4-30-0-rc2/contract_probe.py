#!/usr/bin/env python3
"""Model a diagnostic adapter over observed LSP events; no MCP server is run."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
SOURCE=HERE/'transcript.json'
if not SOURCE.exists():SOURCE=HERE/'transcript-run3.json'
E=json.loads(SOURCE.read_text())

def until(kind):return next(e['seq'] for e in E if e['kind']==kind)
def apply(events):
 state={}
 for e in events:
  if e['kind']!='server' or e.get('server')!='initial':continue
  m=e['message']
  if m.get('method')!='textDocument/publishDiagnostics':continue
  p=m['params'];uri=p['uri'];v=p['version']
  if uri not in state or v>=state[uri]['version']:
   state[uri]={'version':v,'errors':sum(d.get('severity')==1 for d in p['diagnostics'])}
 return {uri.rsplit('/',1)[-1]:value for uri,value in state.items()}

cut=until('bad_unsaved_goal')
current=until('good_unsaved_again')
received=apply(e for e in E if e['seq']<=cut)
authoritative=apply(e for e in E if e['seq']<=current)
flat=[]
for e in E:
 if e['seq']>current:break
 m=e.get('message',{})
 if e['kind']=='server' and e.get('server')=='initial' and m.get('method')=='textDocument/publishDiagnostics':
  flat=m['params']['diagnostics']
assert received['Shadow.lean']=={'version':2,'errors':2}
assert received['Other.lean']=={'version':1,'errors':1}
assert authoritative['Shadow.lean']=={'version':3,'errors':0}
assert authoritative['Other.lean']=={'version':1,'errors':1}
result={'kind':'local_contract_model_over_recorded_lean_lsp','input_transcript':SOURCE.name,'disconnect_after_seq':cut,'reconcile_at_seq':current,'subscription_cache_without_replay':received,'authoritative_snapshot_after_poll':authoritative,'flattened_last_notification_error_count':sum(d.get('severity')==1 for d in flat),'interpretation':'Lost Shadow v3 event leaves a stale error; authoritative polling repairs Shadow while retaining Other. Flattening diagnostics by latest event loses Other.'}
(HERE/'contract-observations.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
