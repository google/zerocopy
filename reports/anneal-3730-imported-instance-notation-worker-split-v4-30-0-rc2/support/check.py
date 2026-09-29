#!/usr/bin/env python3
"""Offline checker for retained imported instance/notation worker split."""
import json
from pathlib import Path

r=json.loads((Path(__file__).resolve().parent/'results.json').read_text())
assert {x['label'] for x in r['cases']}=={'instance','notation'}
for x in r['cases']:
    assert x['build_old']['rc']==0 and x['build_new']['rc']==0
    assert x['batch_old']['rc']==0 and x['batch_new']['rc']!=0
    assert x['old_olean_sha256']!=x['new_olean_sha256']
    assert x['old_wait'].get('result')=={} and x['new_wait'].get('result')=={}
    assert 'no goals' in str(x['old_goal']) and 'no goals' in str(x['resident_goal'])
    assert 'no goals' in str(x['old_after_new']) and '⊢ selected = 7' in str(x['new_goal'])
    assert not x['old_diagnostics']['diagnostics'] and not x['resident_diagnostics']['diagnostics']
    assert x['new_diagnostics']['diagnostics']
    assert 'rfl' in x['batch_new']['stdout']
print('I050 imported instance/notation retained result checks passed')
