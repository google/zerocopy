#!/usr/bin/env python3
"""Deterministically summarize retained raw resource samples."""
import csv
import json
from pathlib import Path

root = Path(__file__).parent
data = json.loads((root / 'results.json').read_text())
rows = []
for segment in data['segments']:
    for index, sample in enumerate(segment['samples']):
        footprint = sample['footprint']
        disk = sample['disk']
        tree = sample['tree']
        rows.append({'segment': segment['id'], 'sample': index,
                     'label': sample['label'], 'elapsed_seconds': sample['elapsed_seconds'],
                     'processes': tree['processes'], 'rss_sum_bytes': tree['rss_sum_bytes'],
                     'footprint_summary_bytes': footprint['summary_bytes'],
                     'per_pid_phys_sum_bytes': sum(footprint['per_pid_phys_footprint_bytes']),
                     'free_percent': sample['free_percent'], 'disk_files': disk['files'],
                     'disk_payload_bytes': disk['payload_bytes'],
                     'disk_blocks_bytes': disk['blocks_bytes'],
                     'disk_distinct_inodes': disk['distinct_inodes']})
with (root / 'sample-ledger.csv').open('w', newline='') as f:
    writer = csv.DictWriter(f, fieldnames=list(rows[0]))
    writer.writeheader()
    writer.writerows(rows)
print(f'wrote {len(rows)} samples')
