#!/usr/bin/env python3
"""Check retained direct-Lean OLean unlink and fresh-import observations."""
import json
from pathlib import Path

d = json.loads((Path(__file__).resolve().parent / 'results.json').read_text())
assert d['pin']['lean_sha256'] == 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
assert d['artifact_sha256_before'] == d['artifact_sha256_restored']
assert d['batch_before']['exit'] == 0 and d['batch_before']['stdout'] == ''
assert d['batch_missing']['exit'] == 1 and "unknown module prefix 'Dep'" in d['batch_missing']['stdout']
assert d['batch_restored']['exit'] == 0 and d['batch_restored']['stdout'] == ''
goal = d['live_initial']['goal']['result']['goals']
assert goal == ['⊢ depValue = 7']
assert d['live_same_after_unlink']['result']['goals'] == goal
assert d['live_initial']['diagnostics'][-1]['diagnostics'] == []
for name in ('live_second_after_unlink', 'fresh_missing'):
    row = d[name]
    assert row['goal']['result'] is None
    assert any("unknown module prefix 'Dep'" in diagnostic['message']
               for batch in row['diagnostics'] for diagnostic in batch['diagnostics'])
assert d['first_server']['exit'] == 0 and d['fresh_server']['exit'] == 0
assert len(d['first_server']['messages']) > 10 and len(d['fresh_server']['messages']) > 8
print('I121 retained direct Lean artifact-unlink controls passed')
