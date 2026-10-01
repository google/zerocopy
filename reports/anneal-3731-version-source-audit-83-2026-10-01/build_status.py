#!/usr/bin/env python3
"""Emit a conservative status crosswalk for all 83 frozen inventory rows."""
import csv
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish')
rows = json.loads((HERE / 'evidence/bundle-pairs-83.json').read_text())
heads = json.loads((HERE / 'evidence/default-heads.json').read_text())['refs']

def review_detail(row):
    result = []
    for review in row['existing_source_reviews']:
        matrix = json.loads((REPO / review['review_matrix']).read_text())
        record = next((x for x in matrix.get('rows', [])
                       if isinstance(x, dict) and x.get('inventory_id') == row['inventory_id']), matrix)
        source_result = next((record.get(k) for k in
                              ('source_result', 'source_claim_result', 'source_results', 'rechecked_source_clause')
                              if record.get(k)), None)
        target = next((record.get(k) for k in
                       ('target', 'selected_current_commit', 'target_source_commit',
                        'selected_observed_main_commit', 'source_pin_graph', 'target_version')
                       if record.get(k)), None)
        result.append({'review_report': review['review_report'],
                       'review_matrix': review['review_matrix'],
                       'review_matrix_sha256': review['review_matrix_sha256'],
                       'source_result': source_result,
                       'target_identity': target})
    return result

SPECIAL_GAP = {
    'R138': 'Prior two-bundle output result was not rerun under the September bundle.',
    'R182': 'Historical Lean 4.29/4.30 comparison; full 4.34.1 behavior unresolved.',
    'R196': 'Historical Lean 4.29/4.30 comparison; full 4.34.1 behavior unresolved.',
    'R255': 'Historical Lean 4.29/4.30 comparison; current Unicode/capability behavior unresolved.',
    'R324': 'Old report links use pre-reorganization anneal/src paths; current v1 files were also checked.',
    'R331': 'Old anneal/tests/integration.rs path was removed; current anneal/v1/tests/integration.rs differs as a relocated source file.',
    'R351': 'The unchanged Anneal design files do not recheck the report’s Cargo/rustc implementation claims.',
    'R368': 'Charon golden LLBC output was not rerun at the newer source.',
    'R423': 'Lake 4.31 to 4.34 source paths were compared; behavior was not rerun.',
    'R447': 'Historical Lean 4.29/4.30 comparison; full 4.34.1 behavior unresolved.',
    'R456': 'Historical Lean 4.29/4.30 comparison; full 4.34.1 behavior unresolved.',
    'R462': 'A narrow request source clause was rechecked; server reply-order behavior remains unresolved.',
    'R491': 'Google packaging source was checked; leangz/leantar current source and helper behavior are not directly rechecked here.',
    'R506': 'Lean persistent collection source was compared; footprint/retention behavior was not rerun.',
    'R533': 'The prior Aeneas/Charon output comparison was not rerun at the September bundle.',
    'R574': 'Anneal archive procedure source was checked; cross-version archive equivalence was not rerun.',
    'R576': 'TypeScript 7.0.2 full language-server behavior remains unresolved in the inherited review.',
    'R580': 'Zerocopy source was checked; current Rust core/reference semantics were not directly rechecked here.',
}

output = []
for row in rows:
    g = row['google_source_summary'] or {'same': 0, 'different': 0, 'unavailable_or_absent': 0}
    b = row['bundle_source_summary'] or {'same': 0, 'different': 0, 'unavailable_or_absent': 0}
    reviews = review_detail(row)
    review_result = '; '.join(str(x['source_result']) for x in reviews if x['source_result'])
    direct_changed = g['different'] + b['different']
    direct_same = g['same'] + b['same']
    external_primary = bool(reviews) and int(row['inventory_id'][1:]) >= 346
    if external_primary and row['inventory_id'] in {'R566', 'R576', 'R503'}:
        relation = {'R566': 'changed', 'R576': 'unavailable', 'R503': 'unchanged'}[row['inventory_id']]
        basis = 'inherited_published_review'
    elif external_primary and review_result:
        normalized = review_result.lower()
        if any(k in normalized for k in ('mapped_source_blobs_unchanged', 'mapped_blobs_unchanged',
                                           'mapped_docs_unchanged', 'mapped_source_paths_unchanged',
                                           'no_observable_drift', 'equal_their_original_pins',
                                           'equal_exact_report_pins', 'same_pinned_commit', 'same_as_pins', 'same_pin',
                                           'no_newer_official', 'already_current')):
            relation = 'unchanged'
        elif any(k in normalized for k in ('three_changed', 'changed', 'delta', 'diverged')):
            relation = 'changed'
        elif any(k in normalized for k in ('unresolved', 'unavailable')):
            relation = 'unavailable'
        else:
            relation = 'unavailable'
        basis = 'inherited_published_review'
    elif direct_changed:
        relation = 'changed'
        basis = 'direct_git_object'
    elif direct_same:
        relation = 'unchanged'
        basis = 'direct_git_object'
    elif review_result:
        normalized = review_result.lower()
        if any(k in normalized for k in ('mapped_source_blobs_unchanged', 'mapped_blobs_unchanged',
                                           'mapped_docs_unchanged', 'mapped_source_paths_unchanged',
                                           'no_observable_drift', 'equal_their_original_pins',
                                           'same_pinned_commit', 'same_as_pins', 'same_pin')):
            relation = 'unchanged'
        elif any(k in normalized for k in ('three_changed', 'changed', 'delta', 'diverged')):
            relation = 'changed'
        elif any(k in normalized for k in ('unchanged', 'no_newer', 'already_current', 'zero_forward')):
            relation = 'unchanged'
        else:
            relation = 'unavailable'
        basis = 'inherited_published_review'
    else:
        relation = 'unavailable'
        basis = 'no_claim_mapped_comparison'
    pinned_repos = {s['identity'].get('repository') for s in row['pinned_subjects']
                    if s['identity'].get('repository')}
    pinned_repos.update(p['repository'] for p in row['google_source_pairs'] + row['bundle_source_pairs'])
    pinned_repos = sorted(pinned_repos)
    default_refs = {repo: heads[repo]['head'] if repo in heads else None for repo in pinned_repos}
    gap = SPECIAL_GAP.get(row['inventory_id'], '')
    if g['unavailable_or_absent'] or b['unavailable_or_absent']:
        gap = (gap + ' ' if gap else '') + 'Some cited paths are absent at one or both refs; see pair evidence.'
    if row['classification'] == 'prior_comparison' and not gap:
        gap = 'Prior empirical comparison remains historical; no current runtime replay.'
    if not gap:
        gap = 'This source-only comparison does not establish target runtime or Anneal product behavior.'
    output.append({
        'inventory_id': row['inventory_id'],
        'classification': row['classification'],
        'original_report': row['original_report'],
        'source_relation_at_mapped_scope': relation,
        'basis': basis,
        'google_same': g['same'], 'google_changed': g['different'], 'google_absent': g['unavailable_or_absent'],
        'bundle_same': b['same'], 'bundle_changed': b['different'], 'bundle_absent': b['unavailable_or_absent'],
        'published_source_reviews': ' | '.join(x['review_report'] for x in reviews),
        'published_review_result': review_result,
        'pinned_repositories': ' | '.join(pinned_repos),
        'observed_default_head_refs': json.dumps(default_refs, sort_keys=True),
        'inventory_target': row['inventory_target'],
        'remaining_gap': gap,
        'target_runtime': 'unexecuted_in_this_audit',
        'anneal_product': 'unassessed_in_this_audit',
    })

assert len(output) == 83
assert len({r['inventory_id'] for r in output}) == 83
csv_path = HERE / 'status-83.csv'
with csv_path.open('w', newline='') as f:
    writer = csv.DictWriter(f, fieldnames=list(output[0]))
    writer.writeheader(); writer.writerows(output)
(HERE / 'evidence/review-details-83.json').write_text(json.dumps({r['inventory_id']: review_detail(r) for r in rows}, indent=2, sort_keys=True) + '\n')
from collections import Counter
print(json.dumps({'rows': len(output), 'relations': dict(Counter(x['source_relation_at_mapped_scope'] for x in output)),
                  'bases': dict(Counter(x['basis'] for x in output))}, sort_keys=True))
