#!/usr/bin/env python3
"""Validate the retained agenda snapshot and ledger without network access."""
import csv
import hashlib
import io
import json
import re
from pathlib import Path

support = Path(__file__).resolve().parent
reports = support.parent.parent
source = support / 'source-snapshot'
manifest = json.loads((source / 'manifest.json').read_text())
for name, entry in manifest['files'].items():
    assert hashlib.sha256((source / name).read_bytes()).hexdigest() == entry['sha256'], name

issue_3730 = (source / 'issue3730.txt').read_text()
issue_3731 = (source / 'issue3731.txt').read_text()
comment_3731 = (source / 'comment3731.txt').read_text()

item_pattern = re.compile(r'^\*\*(I\d{3}) — (.*?) \[([^]]+)\]\.\*\* (.+)$', re.M)
items = {m[1]: (m[2], m[3], m[4])
         for text in (issue_3731, comment_3731) for m in item_pattern.finditer(text)}
matrix = list(csv.DictReader((support / 'investigation-matrix.csv').open(newline='')))
assert len(items) == len(matrix) == 159
assert [r['id'] for r in matrix] == [f'I{i:03}' for i in range(1, 160)]
for row in matrix:
    assert (row['title'], row['methods'], row['scope']) == items[row['id']], row['id']
    for field in ('prior_evidence_packages', 'new_evidence'):
        for pointer in row[field].split(';'):
            slug = pointer.strip().split(' (')[0]
            if slug and slug != 'none in this turn':
                assert (reports / slug / 'REPORT.md').is_file(), (row['id'], slug)
    assert 'complete' not in row['disposition'].lower(), row['id']

extension_section = comment_3731.split('## Scope extensions to I001–I144', 1)[1].split('## Complete #3730', 1)[0]
extensions = re.findall(r'^\*\*(I\d{3})\.\*\* (.+)$', extension_section, re.M)
assert len(extensions) == len({item_id for item_id, _ in extensions}) == 64
assert all(item_id in items for item_id, _ in extensions)
out = io.StringIO(newline='')
writer = csv.writer(out, lineterminator='\n')
writer.writerow(('id', 'extension'))
writer.writerows(extensions)
assert (support / 'scope-extensions.csv').read_text() == out.getvalue()

crosswalk_section = comment_3731.split('## Complete #3730 → #3731 crosswalk', 1)[1]
lines = crosswalk_section.splitlines()
start = next(i for i, line in enumerate(lines) if line.startswith('| #3730 ID |'))
crosswalk_source = []
for line in lines[start + 2:]:
    if not line.startswith('| '):
        break
    fields = tuple(field.strip() for field in line.strip().strip('|').split('|'))
    assert len(fields) == 3
    crosswalk_source.append(fields)
crosswalk = list(csv.DictReader((support / '3730-to-3731-crosswalk.csv').open(newline='')))
assert len(crosswalk) == len(crosswalk_source) == 174
assert len({row['3730_id'] for row in crosswalk}) == 174
assert [tuple(row.values()) for row in crosswalk] == crosswalk_source
issue_3730_ids = set(re.findall(r'^### ([A-Z]\d{2})\.', issue_3730, re.M))
assert issue_3730_ids == {row['3730_id'] for row in crosswalk}
assert all(all(f'I{i:03}' in items for i in map(int, re.findall(r'I(\d{3})', row['3731_destination'])))
           for row in crosswalk)

new_evidence_rows = sum(row['new_evidence'] != 'none in this turn' for row in matrix)
print(f'PASS: {len(items)} base items, {len(extensions)} scope extensions, '
      f'{len(crosswalk)} crosswalk rows, {new_evidence_rows} partial new-evidence rows; '
      'source hashes and report pointers valid')
