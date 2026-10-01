#!/usr/bin/env python3
"""Bind the 83 frozen inventory IDs to previously published source reviews."""
import csv
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish')
INV = HERE / 'evidence/version-inventory-ebcdcad-581.csv'
CLASSES = {'source_revision_recheck', 'prior_comparison'}

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

rows = [r for r in csv.DictReader(INV.open()) if r['classification'] in CLASSES]
assert len(rows) == 83
reviews = {}
for matrix_path in sorted((REPO / 'reports').glob('*/support/matrix.json')):
    package = matrix_path.parent.parent
    if not (package / 'REPORT.md').exists():
        continue
    matrix = json.loads(matrix_path.read_text())
    ids = set()
    if matrix.get('inventory_id'):
        ids.add(matrix['inventory_id'])
    for record in matrix.get('rows', []):
        if isinstance(record, dict) and record.get('inventory_id'):
            ids.add(record['inventory_id'])
    cohort = package / 'support/frozen-cohort.csv'
    if cohort.exists():
        for record in csv.DictReader(cohort.open()):
            if record.get('inventory_id'):
                ids.add(record['inventory_id'])
    for rid in ids:
        reviews.setdefault(rid, []).append({
            'review_report': str((package / 'REPORT.md').relative_to(REPO)),
            'review_report_sha256': sha(package / 'REPORT.md'),
            'review_matrix': str(matrix_path.relative_to(REPO)),
            'review_matrix_sha256': sha(matrix_path),
            'row_present_in_matrix': rid == matrix.get('inventory_id') or any(
                isinstance(x, dict) and x.get('inventory_id') == rid for x in matrix.get('rows', [])),
        })

result = []
for row in rows:
    rid = row['inventory_id']
    result.append({
        'inventory_id': rid,
        'classification': row['classification'],
        'original_report': row['report_md_at_commit'],
        'original_report_sha256': sha(REPO / row['report_md_at_commit']),
        'pinned_subjects': json.loads(row['exact_pinned_subject_identities_json']),
        'inventory_target': row['newer_comparison_target'],
        'existing_source_reviews': reviews.get(rid, []),
    })

output = HERE / 'evidence/review-map-83.json'
output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps({'rows': len(result), 'with_review': sum(bool(x['existing_source_reviews']) for x in result),
                  'without_review': [x['inventory_id'] for x in result if not x['existing_source_reviews']]}, sort_keys=True))
