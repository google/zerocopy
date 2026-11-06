#!/usr/bin/env python3
"""Offline validation of the retained nested-position Lean batch/LSP transcript."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
events=json.loads((ROOT/'transcript.json').read_text())
source=(ROOT/'Nested.lean').read_bytes()
sha=lambda x:hashlib.sha256(x).hexdigest()
one=lambda kind:next(x for x in events if x['kind']==kind)
assert [x['seq'] for x in events]==list(range(len(events)))
assert not [x for x in events if x['kind']=='fatal']
subject=one('subject')
assert '4.30.0-rc2' in subject['lean_version']
assert subject['binary_sha256']=='b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
assert subject['source_sha256']==sha(source)
batch=one('batch')
assert batch['returncode']==0 and not batch['stderr']
batch_lines=[json.loads(line) for line in batch['stdout'].splitlines() if line.strip()]
assert len(batch_lines)==1 and batch_lines[0]['kind']=='trace' and batch_lines[0]['data']=='🧪'
assert one('ready')['response']['result']=={}
assert one('stop')['returncode']==0 and one('completed')['seq']<one('stop')['seq']
diagnostics=[x['message']['params']['diagnostics'] for x in events if x['kind']=='recv'
    and x['message'].get('method')=='textDocument/publishDiagnostics'
    and x['message']['params'].get('version')==1]
assert diagnostics and any(any(d['message']=='🧪' and d['severity']==3 for d in ds) for ds in diagnostics)
assert not any(d['severity']==1 for ds in diagnostics for d in ds)

goals={x['name']:x for x in events if x['kind']=='goal'}
assert len(goals)==20
assert all('error' not in x['response'] for x in goals.values())
g=lambda name:goals[name]['response']['result']['goals']
assert len(g('nested_by'))==1 and 'h : n = 0' in g('nested_by')[0]
assert g('nested_by')==g('have_before')==g('inner_simpa_before')
assert g('inner_simpa_after')==['n : Nat\nh : n = 0\n⊢ n = 0']
assert g('first_keyword')==g('trace_before')==g('emoji_open_quote')==g('emoji_inside')==g('emoji_after')==g('outer_exact_before')
assert 'hz : n + 0 = 0' in g('first_keyword')[0]
assert g('outer_exact_after')==g('unselected_branch')==[]
assert g('constructor_before')==['n : Nat\n⊢ True ∧ n = n']
assert len(g('first_bullet'))==2 and 'case left' in g('first_bullet')[0] and 'case right' in g('first_bullet')[1]
assert g('trivial_before')==[g('first_bullet')[0]] and g('trivial_after')==[]
assert g('second_bullet')==g('rfl_before')==[g('first_bullet')[1]]
assert g('term_exact_before')==['n : Nat\n⊢ n = n'] and g('term_expr')==[]
assert goals['emoji_inside']['position']=={'line':6,'character':11}
assert goals['emoji_after']['position']=={'line':6,'character':13}
assert goals['outer_exact_before']['position']=={'line':6,'character':16}
line=source.decode().splitlines()[6]
assert line[:line.index('exact')].index('🧪')>=0
assert len(line[:line.index('exact')].encode('utf-16-le'))//2==16
assert len(line[:line.index('exact')])==15

term={x['name']:x['response'] for x in events if x['kind']=='term_goal'}
assert len(term)==3 and all('error' not in x for x in term.values())
assert term['term_exact_before']['result'] is None and term['emoji_after']['result'] is None
assert term['term_expr']['result']=={'goal':'n : Nat\n⊢ n = n',
    'range':{'start':{'line':15,'character':8},'end':{'line':15,'character':17}}}
print('PASS: Lean 4.30.0-rc2 batch + 20 nested plainGoal and 3 term-goal positions, UTF-16, diagnostics, cleanup')
