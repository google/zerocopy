#!/usr/bin/env python3
"""Static checks on the retained Lean two-file LSP and batch artifacts."""
import hashlib,json
from pathlib import Path
from probe import HERE,FILES,sha,workspace_edits,apply

t=json.loads((HERE/'transcript.json').read_text());r=t['responses'];uris=t['uri_by_name']
a=json.loads((HERE/'applied-results.json').read_text());caps=r['initialize']['result']['capabilities']
assert t['server_exit']==0 and 'exception' not in r and t['prebuild']['exit']==0
assert caps['renameProvider']['prepareProvider'] and caps['codeActionProvider']['resolveProvider']
assert caps['signatureHelpProvider'] and caps['inlayHintProvider']
rename=workspace_edits(r['rename']['result'])
assert set(rename)=={uris['Helper.lean'],uris['Main.lean']}
assert len(rename[uris['Helper.lean']])==1 and len(rename[uris['Main.lean']])==3
assert len(r['references']['result'])>=4
quick=[x for x in r['actionQuickfix']['result'] if x.get('edit')]
assert quick and any(x['title']=='Import αhelper from Helper' for x in quick)
assert r['actionSource']['result']
action_edits=workspace_edits(quick[0]['edit'])
assert set(action_edits)=={uris['Action.lean']}
assert any(e['newText']=='import Helper\n' for e in action_edits[uris['Action.lean']])
assert quick[0]['edit']['documentChanges'][0]['textDocument']['version']==1
assert r['inlay']['result'][0]['label']==' {α}' and r['inlay']['result'][0]['textEdits']
assert any(v.get('result') and v['result'].get('signatures') for k,v in r.items() if k.startswith('signature-'))
assert len(r['completion']['result']['items'])>=1 and r['completionResolve']['result']['label']=='αhelper'
assert all(k not in r['completionResolve']['result'] for k in ('textEdit','insertText','additionalTextEdits'))
assert a['transcript_sha256']==sha(HERE/'transcript.json')
assert a['branches']['rename']['source_hash_guard']['stale_rejected_atomically']
assert a['branches']['action']['version_guard']['stale_rejected']
for branch,data in a['branches'].items():
    assert all(x['exit']==0 for x in data['batch'].values()),branch
    for name,digest in data['source_sha256'].items():
        path=HERE/'applied'/(('completion' if branch=='completion_client_fallback' else branch)+'-'+name)
        assert path.exists() and sha(path)==digest
for name,digest in a['artifact_sha256'].items():assert sha(HERE/'applied'/name)==digest
assert (HERE/'applied/rename-Helper.lean').read_text()==apply(FILES['Helper.lean'],rename[uris['Helper.lean']])
assert (HERE/'applied/rename-Main.lean').read_text()==apply(FILES['Main.lean'],rename[uris['Main.lean']])
print('verified two-file rename, nonempty action, signature and inlay responses, four batch-checked edit branches')
