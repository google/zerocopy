#!/usr/bin/env python3
"""Replay real Lean edit ranges through the prior illustrative projection model."""
import hashlib,importlib.util,json
from pathlib import Path
from probe import HERE,SOURCE,offset

MODEL_PATH=HERE.parents[1]/'anneal-3730-lean-lsp-projection-code-actions-2026-09-29/support/projection_model.py'
spec=importlib.util.spec_from_file_location('illustrative_projection_model',MODEL_PATH)
model=importlib.util.module_from_spec(spec);spec.loader.exec_module(model)
raw=json.loads((HERE/'transcript.json').read_text())
source=SOURCE;version=1;events=[]
all_edits=[]
for application in raw['applications']:
    for edit in application['edits']:
        all_edits.append((application['origin'],edit))
# Server rename ranges refer to the original document. Apply higher source
# ranges before lower ones, then apply the client completion fallback.
rename=[x for x in all_edits if x[0]=='server rename WorkspaceEdit']
completion=[x for x in all_edits if x[0]!='server rename WorkspaceEdit']
rename.sort(key=lambda x:offset(SOURCE,x[1]['range']['start']),reverse=True)
for origin,edit in rename+completion:
    a=offset(source,edit['range']['start']);b=offset(source,edit['range']['end'])
    generated,segments=model.build(source)
    owner=[s for s in segments if s['source'][0]<=a<=b<=s['source'][1]]
    assert len(owner)==1
    seg=owner[0];ga=seg['generated'][0]+a-seg['source'][0];gb=ga+b-a
    previous=source
    source=model.project_edit(source,generated,segments,version,version,ga,gb,edit['newText'])
    expected=previous[:a]+edit['newText']+previous[b:]
    assert source==expected
    stale=None
    try:model.project_edit(previous,generated,segments,version,version-1,ga,gb,edit['newText'])
    except ValueError as exc:stale=str(exc)
    assert stale=='stale generation'
    events.append({'origin':origin,'version':version,'lsp_range':edit['range'],'source_offsets':[a,b],
                   'generated_offsets':[ga,gb],'owner_line':seg['line'],'replacement':edit['newText'],
                   'before_sha256':model.digest(previous),'after_sha256':model.digest(source),'stale_rejection':stale})
    version+=1
applied=(HERE/'Applied.lean').read_text()
assert source==applied
result={'model_only':True,'model_path':str(MODEL_PATH),'model_sha256':hashlib.sha256(MODEL_PATH.read_bytes()).hexdigest(),
        'direct_transcript_sha256':hashlib.sha256((HERE/'transcript.json').read_bytes()).hexdigest(),
        'source_sha256':model.digest(SOURCE),'applied_sha256':model.digest(applied),
        'events':events,'final_version':version,'batch_exit':raw['batch']['exit']}
(HERE/'projection-replay.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print('model-projected edits',len(events),'match applied Lean source',source==applied,'batch exit',raw['batch']['exit'])
