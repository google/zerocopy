#!/usr/bin/env python3
"""Static checks on retained direct LSP and illustrative model observations."""
import hashlib,json
from pathlib import Path

HERE=Path(__file__).resolve().parent
source=(HERE/'Unicode.lean').read_text()
transcript=json.loads((HERE/'lsp-transcript.json').read_text())
for tag in ('utf16_first','utf8_first'):
    run=transcript[tag];r=run['responses'];caps=r['initialize']['result']['capabilities']
    assert run['exit']==0 and 'exception' not in r
    assert run['source_sha256']==hashlib.sha256(source.encode()).hexdigest()
    assert caps.get('positionEncoding') is None
    assert caps['codeActionProvider']['codeActionKinds']
    assert caps['completionProvider']['resolveProvider']
    items=r['completion']['result']['items']
    assert len(items)==223 and any(x['label']=='exact' for x in items)
    assert r['codeAction']['result']==[]
    publications=[e['message']['params']['diagnostics'] for e in run['events']
                  if e['side']=='server' and e['message'].get('method')=='textDocument/publishDiagnostics']
    matches=[d for ds in publications for d in ds if 'unknownName' in d['message']]
    assert matches and all(d['range']['start']=={'line':3,'character':14} for d in matches)
    assert r['hover']['result']['range']=={'start':{'line':1,'character':8},'end':{'line':1,'character':10}}
assert source.splitlines()[3].index('unknownName')==13
assert len(source.splitlines()[3].split('unknownName')[0].encode('utf-16-le'))//2==14
assert len(source.splitlines()[3].split('unknownName')[0].encode('utf-8'))==16
model=json.loads((HERE/'projection-stream.json').read_text())
assert model['model_only'] and model['initial_lines']==64 and model['edits']==500
assert len(model['events'])==500 and sum('rejections' in x for x in model['events'])==20
assert all({z['kind'] for z in e['rejections']}=={'stale','synthetic','cross-segment'}
           for e in model['events'] if 'rejections' in e)
assert model['utf16_examples']['😀αx']['invalid']['1']=='split UTF-16 surrogate pair'
print('verified direct LSP encoding, capability and response observations plus 500 model edits')
