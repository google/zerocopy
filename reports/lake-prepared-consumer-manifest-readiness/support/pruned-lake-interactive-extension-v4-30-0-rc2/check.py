#!/usr/bin/env python3
"""Check retained no-build/pruned Lake interactive extension results."""
import json
from pathlib import Path

data = json.loads((Path(__file__).resolve().parent/'results.json').read_text())
full, pruned = data['full'], data['pruned']
names = ('ProofBase.lean','ProofTactic.lean','ProofExtra.lean','ProofMacro.lean')
assert all(full[name]['rc'] == 0 for name in names)
assert full['plugin_load']['rc'] == 0 and full['plugin_marker'] == 'plugin-loaded'
assert pruned['ProofBase.lean']['rc'] == 0
assert pruned['ProofTactic.lean']['rc'] == 0
assert pruned['ProofExtra.lean']['rc'] != 0 and 'Extra' in pruned['ProofExtra.lean']['stdout']
assert pruned['ProofMacro.lean']['rc'] != 0 and 'Macro' in pruned['ProofMacro.lean']['stdout']
assert pruned['plugin_load']['rc'] != 0 and pruned['plugin_marker'] is None
assert data['no_build']['extra']['rc'] != 0 and data['no_build']['macro']['rc'] != 0
assert data['before']['total_bytes'] - data['after']['total_bytes'] == sum(x['bytes'] for x in data['removed'].values())
assert len(data['live_scratch']) == 2
assert all(not x['physical_exists'] for x in data['live_scratch'])
assert '⊢ selected = 7' in str(data['live_scratch'][0]['goal'])
assert '⊢ extra = 8' in str(data['live_scratch'][1]['goal'])
assert 'lib/lean/Extra.olean' not in data['after']['files']
assert 'lib/lean/Extra.olean' not in data['after_no_build']['files']
assert 'lib/lean/Extra.olean' in data['after_live']['files']
assert 'lib/lean/Macro.olean' not in data['after_live']['files']
print('I120 pruned Lake retained result checks passed')
