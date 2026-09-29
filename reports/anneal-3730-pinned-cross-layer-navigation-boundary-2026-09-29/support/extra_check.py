#!/usr/bin/env python3
"""Offline validation of reorder and same-leaf-name navigation controls."""
from __future__ import annotations

import json
from pathlib import Path

from nav import StaleArtifact, digest, forward, reverse

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
REPO = HERE.parents[2]
R12 = REPO / 'reports/anneal-3730-cross-layer-comparator-mutants-2026-09-29'


def validate() -> dict:
    manifest = json.loads((HERE / 'extra-manifest.json').read_text())
    result = json.loads((HERE / 'extra-results.json').read_text())
    metadata = json.loads((PACKAGE / 'REPORT.json').read_text())
    origin = json.loads((R12 / 'support/results.json').read_text())
    assert manifest['schema'] == result['schema'] == 1
    assert manifest['r12_source_report'] == R12.name
    assert manifest['r12_results_sha256'] == digest(R12 / 'support/results.json')
    assert metadata['subjects'][1]['identity']['extra_manifest_sha256'] == digest(HERE / 'extra-manifest.json')
    assert manifest['tool_sha256'] == {k: origin['subjects'][k + '_sha256']
                                       for k in ('charon', 'aeneas', 'lean')}
    assert set(manifest['generations']) == {'reorder-base', 'reorder-reorder', 'ambiguous'}
    assert len(result['commands']) == 8 and all(x['exit'] == 0 for x in result['commands'])
    assert len(result['navigation']) == 9 and len(result['stale_rejections']) == 2
    assert result['ambiguity']['rust_test_exit'] == result['ambiguity']['lean_proof_exit'] == 0
    assert '1 passed' in result['commands'][-1]['stdout']

    entries_by_case = {}
    for case, generation in manifest['generations'].items():
        root = HERE / 'extra-artifacts' / case
        paths = {}
        for role, identity in generation['artifacts'].items():
            path = PACKAGE / identity['path']
            assert path.is_file() and path.stat().st_size == identity['bytes']
            assert digest(path) == identity['sha256']
            paths[role] = path
        source = paths['rust_source'].read_bytes()
        llbc = json.loads(paths['llbc'].read_text())
        funs = paths['generated_funs'].read_text()
        proof = paths['proof'].read_text()
        assert llbc['translated']['files'][0]['contents'].encode() == source
        assert generation['llbc_embeds_exact_rust_source'] is True
        assert len(generation['entries']) == 3
        if case.startswith('reorder-'):
            origin_case = case.removeprefix('reorder-')
            assert generation['artifacts']['rust_source']['sha256'] == origin['cases'][origin_case]['source_sha256']
            assert generation['artifacts']['llbc']['sha256'] == origin['cases'][origin_case]['llbc_sha256']
            assert generation['artifacts']['generated_funs']['sha256'] == origin['cases'][origin_case]['generated']['Funs.lean']['sha256']
            assert generation['lean_proof_exit'] == 0
        names = []
        for entry in generation['entries']:
            qualified = entry['rust_item']['qualified_name']
            lo, hi = entry['rust_item']['byte_range']
            assert source[lo:hi]
            declaration = next(d for d in llbc['translated']['fun_decls']
                               if d and d['def_id'] == entry['charon']['def_id'])
            assert declaration['item_meta']['source_text'].encode() == source[lo:hi]
            assert declaration['item_meta']['span']['data'] == entry['rust_item']['span']
            assert {k: entry['rust_item']['span'][k] for k in ('beg', 'end')} == entry['aeneas']['emitted_source_span']
            assert entry['aeneas']['emitted_name'] == qualified
            assert qualified in funs
            start, end = entry['aeneas']['declaration_lines']
            assert start <= end and funs.splitlines()[start - 1].startswith('def ')
            assert proof.splitlines()[entry['obligation']['proof_line'] - 1].startswith('theorem ' + entry['obligation']['name'] + ' ')
            assert entry['cross_stage_join_class'].endswith('no shared producer ID')
            fwd = forward(manifest, case, paths['rust_source'], (lo + hi) // 2)
            back = reverse(manifest, case, paths['rust_source'], paths['generated_funs'],
                           'generated_funs', start)
            assert len(fwd) == len(back) == 1
            assert fwd[0]['rust_item'] == back[0]['rust_item'] == qualified
            names.append(qualified)
        assert len(set(names)) == 3
        entries_by_case[case] = generation['entries']

    base = entries_by_case['reorder-base']
    changed = entries_by_case['reorder-reorder']
    b = {e['charon']['def_id']: e['rust_item']['qualified_name'] for e in base}
    c = {e['charon']['def_id']: e['rust_item']['qualified_name'] for e in changed}
    assert b[0] == 'comparator_probe::inc' and c[0] == 'comparator_probe::choose'
    assert {e['charon']['def_id']: e['rust_item']['qualified_name'] for e in base} != c
    assert [e['aeneas']['qualified_lean_name'] for e in sorted(base, key=lambda x: x['aeneas']['declaration_lines'][0])] == [
        e['aeneas']['qualified_lean_name'] for e in sorted(changed, key=lambda x: x['aeneas']['declaration_lines'][0])]
    assert result['reorder']['def_id_0_wrong_join_if_reused'] == [b[0], c[0]]
    assert result['reorder']['generated_order_base'] == result['reorder']['generated_order_reordered'] == [
        'comparator_probe.inc', 'comparator_probe.twice', 'comparator_probe.choose']

    ambiguous = entries_by_case['ambiguous']
    leaves = [e['rust_item']['qualified_name'] for e in ambiguous
              if e['rust_item']['qualified_name'].split('::')[-1] == 'step']
    assert leaves == result['ambiguity']['leaf_only_candidates'] == [
        'nav_ambig::left::step', 'nav_ambig::right::step']
    assert result['ambiguity']['qualified_span_join_unique'] is True
    traces = [json.loads(line) for line in result['ambiguity']['lean_trace'].splitlines()]
    assert len(traces) == 3 and all(x['kind'] == 'trace' and x['severity'] == 'information' for x in traces)
    assert ['nav_ambig.left.step', 'nav_ambig.right.step', 'nav_ambig.both'] == [
        e['aeneas']['qualified_lean_name'] for e in sorted(ambiguous, key=lambda x: x['obligation']['proof_line'])]
    for entry in ambiguous:
        assert any(entry['aeneas']['qualified_lean_name'] in x['data'] for x in traces)

    try:
        forward(manifest, 'reorder-base', HERE / 'extra-artifacts/reorder-reorder/source.rs', 50)
    except StaleArtifact as error:
        assert result['stale_rejections']['reordered-rust-under-base'] == str(error)
    else:
        raise AssertionError('reordered Rust was accepted')
    try:
        reverse(manifest, 'reorder-base', HERE / 'extra-artifacts/reorder-base/source.rs',
                HERE / 'extra-artifacts/reorder-reorder/Funs.lean', 'generated_funs', 21)
    except StaleArtifact as error:
        assert result['stale_rejections']['reordered-lean-under-base'] == str(error)
    else:
        raise AssertionError('reordered Lean was accepted')
    return {'reorder_generations': 2, 'ambiguous_generations': 1,
            'additional_navigation_links': 9, 'additional_stale_rejections': 2,
            'leaf_only_candidate_count': 2, 'def_id_0_changed_item': True,
            'ambiguous_lean_goal_traces': 3, 'ambiguous_rust_test_passed': True}


if __name__ == '__main__':
    print(json.dumps(validate(), indent=2))
