#!/usr/bin/env python3
"""Check retained bounded component result and the point-in-time gate record."""
import json
from pathlib import Path

base = Path(__file__).parent
a = json.loads((base / 'availability.json').read_text())
r = json.loads((base / 'results.json').read_text())
assert a['searches'][0]['matching_archive_files'] == []
assert a['searches'][1]['matching_archive_files'] == []
assert a['searches'][2]['matching_archive_files'] == []
assert all(x.endswith('.drv') for x in a['searches'][3]['matching_entries'])
assert r['producer_unchanged']
assert r['producer_inventory_before'] == r['producer_inventory_after']
commands = {x['label']: x for x in r['commands']}
assert len(commands) == 7
for name in ['prepare-producer', 'prime-consumer', 'complete-setup', 'complete-batch']:
    assert commands[name]['exit'] == 0, name
for name in ['missing-setup', 'missing-batch', 'removed-setup']:
    assert commands[name]['exit'] != 0, name
assert "'firstGoal' does not depend on any axioms" in commands['complete-batch']['stdout']
assert 'file-write*' in ' '.join(commands['missing-setup']['argv'])
assert 'lakefile.olean.lock' in commands['missing-setup']['stderr']
assert 'package directory not found' in commands['removed-setup']['stderr']
print('PASS: availability scope and retained component oracles')
