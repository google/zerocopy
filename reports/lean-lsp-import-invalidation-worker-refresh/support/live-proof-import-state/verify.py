#!/usr/bin/env python3
"""Check the retained direct Lean import-state transcript and artifacts."""
import hashlib,json
from pathlib import Path

HERE=Path(__file__).resolve().parent
x=json.loads((HERE/'transcript.json').read_text())
e={r['step']:r for r in x['events']}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def diag(r):return r['b']['diagnostics']
def hover(r,key='b_hover'):
 return r[key]['result']['contents']['value']

assert x['first_server_exit']['exit']==x['fresh_server_exit']['exit']==0
for name,digest in x['artifact_sha256'].items():assert sha(HERE/'artifacts'/name)==digest
assert e['saved_initial']['b_batch']['exit']==0
assert e['saved_initial']['a_olean_sha256']==x['artifact_sha256']['A0.olean']
assert e['rebuilt_a']['a_olean_sha256']==x['artifact_sha256']['A1.olean']
assert e['saved_initial']['a_olean_sha256']!=e['rebuilt_a']['a_olean_sha256']
assert diag(e['open_both'])==[]
assert e['open_both']['a']['diagnostics']==[]
assert e['dirty_unsaved_a']['a']['diagnostics']==[]
assert e['dirty_unsaved_a']['a_disk_sha256']==e['saved_initial']['a_source_sha256']
assert e['dirty_unsaved_a']['a_olean_sha256']==e['saved_initial']['a_olean_sha256']
assert e['b_imports_unsaved_only']['b_batch']['exit']==1
assert diag(e['b_imports_unsaved_only'])[0]['message']=='Unknown identifier `unsavedOnly`'
assert 'Unknown identifier `unsavedOnly`' in e['b_imports_unsaved_only']['b_batch']['stdout']
assert e['saved_a_without_rebuild']['b_batch']['exit']==0
assert e['saved_a_without_rebuild']['a_olean_sha256']==e['saved_initial']['a_olean_sha256']
assert e['saved_a_without_rebuild']['a_disk_sha256']!=e['saved_initial']['a_source_sha256']
assert e['rebuilt_a']['b_batch']['exit']==1
assert 'Type mismatch' in e['rebuilt_a']['b_batch']['stdout']
assert 'n + 0 = n' in hover(e['open_both'])
assert hover(e['rebuilt_a'],'old_b_hover')==hover(e['open_both'])
assert 'n + 1 = n + 1' in hover(e['new_b_same_server'])
for name in ('new_b_same_server','reopened_b_same_server','fresh_server'):
 assert len(diag(e[name]))==1 and diag(e[name])[0]['severity']==1
 assert diag(e[name])[0]['message']=='Type mismatch\n  helper n\nhas type\n  n + 1 = n + 1\nbut is expected to have type\n  n + 0 = n'
 assert e[name]['b']['barrier']['result']=={}
assert e['wrong_import_context']['b_batch']['exit']==1
assert "unknown module prefix 'A'" in e['wrong_import_context']['b_batch']['stdout']
for name in ('a','b'):
 assert e['unbuilt_import_cycle'][name]['exit']==1
 assert 'unknown module prefix' in e['unbuilt_import_cycle'][name]['stdout']
 assert len(e['live_unbuilt_import_cycle'][name]['diagnostics'])==1
 assert 'unknown module prefix' in e['live_unbuilt_import_cycle'][name]['diagnostics'][0]['message']
assert e['live_unbuilt_import_cycle']['server_exit']['exit']==0
print('PASS: saved/dirty/unsaved/rebuilt imports, worker lifetime, cycle and sandbox controls')
