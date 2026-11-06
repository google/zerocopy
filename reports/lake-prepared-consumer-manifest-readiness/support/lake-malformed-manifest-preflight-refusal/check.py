#!/usr/bin/env python3
"""Validate retained preflight refusal without starting Lake."""
import json
from pathlib import Path

data = json.loads((Path(__file__).parent / 'preflight.json').read_text())
mem = data['memory']
available = sum(mem[k] for k in ('free_pages', 'inactive_pages', 'speculative_pages', 'purgeable_pages')) * mem['page_bytes']
assert available == mem['estimated_available_bytes'] == 2155036672
assert round(100 * available / mem['installed_bytes'], 2) == mem['estimated_available_percent'] == 25.09
assert mem['estimated_available_percent'] < mem['required_percent'] == 30
assert data['disk']['df_available_gib_rounded_down'] >= data['disk']['required_gib'] == 10
assert data['matching_lake_lean_probe_processes'] == []
assert data['planned_mutation'] == {'file': 'consumer/lake-manifest.json', 'replacement_utf8': '{\n'}
assert data['attempted_lake_commands'] == [] and data['fixture_created'] is False
for key in ('producer_inventory_before', 'producer_inventory_after', 'cache_inventory_before',
            'cache_inventory_after', 'first_goal', 'diagnostics'):
    assert data[key] is None
assert data['decision'] == 'refused_memory_below_30_percent'
print('Malformed-manifest preflight refusal assertions passed')
