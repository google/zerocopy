#!/usr/bin/env python3
"""Static verification of retained direct Lean and model-replay artifacts."""
import hashlib,json,subprocess
from pathlib import Path
from probe import HERE,LEAN,SOURCE,apply_edits

raw=json.loads((HERE/'transcript.json').read_text());r=raw['responses'];caps=r['initialize']['result']['capabilities']
assert raw['server_exit']==0 and 'exception' not in r
assert raw['source_sha256']==hashlib.sha256(SOURCE.encode()).hexdigest()
assert caps.get('positionEncoding') is None
assert caps['definitionProvider'] and caps['referencesProvider'] and caps['renameProvider']['prepareProvider']
assert caps['semanticTokensProvider']['full'] and caps['completionProvider']['resolveProvider']
assert caps['codeActionProvider']['resolveProvider']
def span(start,end):return {'start':{'line':start[0],'character':start[1]},'end':{'line':end[0],'character':end[1]}}
assert r['definition']['result'][0]['targetSelectionRange']==span((0,8),(0,20))
assert [x['range'] for x in r['references']['result']]==[span((0,8),(0,20)),span((3,7),(3,19))]
assert r['prepareRename']['result']==span((3,7),(3,19))
renamed=r['rename']['result']['changes'][raw['source_uri']]
assert len(renamed)==2 and [e['range'] for e in renamed]==[span((0,8),(0,20)),span((3,7),(3,19))]
assert all(e['newText']=='renamed_demo' for e in renamed)
assert len(r['semanticTokens']['result']['data'])==75
assert len(r['completion']['result']['items'])==223
assert r['completionResolve']['result']['label']=='exact'
assert 'textEdit' not in r['completionResolve']['result']
assert r['codeAction']['result']==[]
assert raw['applications'][0]['origin']=='server rename WorkspaceEdit'
assert raw['applications'][1]['origin']=='illustrative client word replacement from completion label'
applied=(HERE/'Applied.lean').read_text()
assert applied==apply_edits(apply_edits(SOURCE,renamed),raw['applications'][1]['edits'])
assert hashlib.sha256(applied.encode()).hexdigest()==raw['applied_sha256']
assert raw['batch']['exit']==0
replay=json.loads((HERE/'projection-replay.json').read_text())
assert replay['model_only'] and replay['batch_exit']==0 and len(replay['events'])==3
assert replay['applied_sha256']==raw['applied_sha256']
assert all(e['stale_rejection']=='stale generation' for e in replay['events'])
assert hashlib.sha256((HERE/'transcript.json').read_bytes()).hexdigest()==replay['direct_transcript_sha256']
model=Path(replay['model_path'])
assert model.is_file() and hashlib.sha256(model.read_bytes()).hexdigest()==replay['model_sha256']
print('verified direct navigation, rename, completion, code-action and semantic-token responses; model replay and batch result')
