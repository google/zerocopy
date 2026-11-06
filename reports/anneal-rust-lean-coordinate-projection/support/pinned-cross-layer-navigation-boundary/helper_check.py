#!/usr/bin/env python3
"""Offline verification of actual one-to-three Aeneas loop declaration fanout."""
from __future__ import annotations

import json
from pathlib import Path

from nav import StaleArtifact, digest, forward, reverse

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent


def validate() -> dict:
    manifest = json.loads((HERE / 'helper-manifest.json').read_text())
    result = json.loads((HERE / 'helper-results.json').read_text())
    metadata = json.loads((PACKAGE / 'REPORT.json').read_text())
    assert manifest['schema'] == result['schema'] == 1
    assert metadata['subjects'][1]['identity']['helper_manifest_sha256'] == digest(HERE / 'helper-manifest.json')
    assert set(manifest['generations']) == {'base', 'changed'}
    assert len(result['commands']) == 18
    assert {x['label'] for x in result['commands'] if x['exit'] != 0} == {
        'base-lean-rfl-attempt', 'changed-lean-rfl-attempt'}
    assert len(result['navigation']) == 2 and len(result['stale_rejections']) == 2
    assert 'not producer-authenticated' in result['boundary']
    checks = {}
    for case, generation in manifest['generations'].items():
        root = HERE / 'helper-artifacts' / case
        paths = {}
        for role, record in generation['artifacts'].items():
            path = PACKAGE / record['path']
            assert path.is_file() and path.stat().st_size == record['bytes']
            assert digest(path) == record['sha256']
            paths[role] = path
        source = paths['rust_source'].read_bytes()
        llbc = json.loads(paths['llbc'].read_text())
        funs = paths['generated_funs'].read_text()
        assert llbc['translated']['files'][0]['contents'].encode() == source
        assert generation['llbc_embeds_exact_rust_source'] is True
        locals_ = [d for d in llbc['translated']['fun_decls'] if d and d['item_meta']['is_local']]
        assert len(locals_) == len(generation['entries']) == 1
        entry = generation['entries'][0]
        declaration = locals_[0]
        assert entry['rust_item']['qualified_name'] == 'loop_nav::sum_to'
        assert entry['charon']['def_id'] == declaration['def_id']
        assert entry['rust_item']['span'] == declaration['item_meta']['span']['data']
        lo, hi = entry['rust_item']['byte_range']
        assert source[lo:hi].decode() == declaration['item_meta']['source_text']
        assert len(entry['aeneas']['declarations']) == 3
        assert [d['role'] for d in entry['aeneas']['declarations']] == ['loop_body', 'loop', 'wrapper']
        assert [d['qualified_lean_name'] for d in entry['aeneas']['declarations']] == [
            'loop_nav.sum_to_loop.body', 'loop_nav.sum_to_loop', 'loop_nav.sum_to']
        assert 'no shared producer ID' in entry['cross_stage_join_class']
        for index, emitted in enumerate(entry['aeneas']['declarations']):
            start, end = emitted['declaration_lines']
            assert start <= end
            assert funs.splitlines()[start - 1].startswith('def ')
            assert '[loop_nav::sum_to]' in funs
            span = emitted['emitted_source_span']
            assert span['beg']['line'] == span['end']['line'] == entry['rust_item']['span']['beg']['line']
            assert span['beg']['col'] >= entry['rust_item']['span']['beg']['col']
            assert span['end']['col'] <= entry['rust_item']['span']['end']['col']
            if index < 2:
                assert span['beg']['col'] > entry['rust_item']['span']['beg']['col']
            else:
                assert span == {k: entry['rust_item']['span'][k] for k in ('beg', 'end')}
            back = reverse(manifest, case, paths['rust_source'], paths['generated_funs'],
                           'generated_funs', start)
            assert len(back) == 1 and back[0]['rust_item'] == 'loop_nav::sum_to'
        front = forward(manifest, case, paths['rust_source'], (lo + hi) // 2)
        assert len(front) == 1 and [x['name'] for x in front[0]['generated_decls']] == [
            d['qualified_lean_name'] for d in entry['aeneas']['declarations']]
        eval_back = reverse(manifest, case, paths['rust_source'], paths['lean_check'], 'lean_check', 5)
        goal_back = reverse(manifest, case, paths['rust_source'], paths['goal_attempt'], 'goal_attempt', 3)
        assert len(eval_back) == len(goal_back) == 1
        assert eval_back[0]['rust_item'] == goal_back[0]['rust_item'] == 'loop_nav::sum_to'
        info = generation['lean_diagnostics']
        assert len(info) == 4 and all(x['severity'] == 'information' for x in info)
        for name, diagnostic in zip(('sum_to_loop.body', 'sum_to_loop', 'sum_to'), info[:3]):
            assert f'loop_nav.{name}' in diagnostic['data']
        expected = 6 if case == 'base' else 4
        assert generation['selected_value'] == expected
        assert f'0x0000000{expected}' in info[-1]['data']
        attempt = generation['failed_rfl_diagnostics']
        assert len(attempt) == 2
        assert any(x['severity'] == 'error' and 'Tactic `rfl` failed' in x['data'] for x in attempt)
        assert any(x['kind'] == 'trace' and f'Result.ok {expected}#u32' in x['data'] for x in attempt)
        records = [x for x in result['commands'] if x['label'].startswith(case + '-')]
        assert len(records) == 9
        assert all(x['exit'] == 0 for x in records if x['label'] != case + '-lean-rfl-attempt')
        assert records[-1]['label'] == case + '-rust-oracle' and records[-1]['exit'] == 0
        checks[case] = {'source_sha256': generation['artifacts']['rust_source']['sha256'],
                        'funs_sha256': generation['artifacts']['generated_funs']['sha256']}
    assert checks['base']['source_sha256'] != checks['changed']['source_sha256']
    assert checks['base']['funs_sha256'] != checks['changed']['funs_sha256']
    for label, action in (
        ('changed-source-under-base', lambda: forward(manifest, 'base', HERE / 'helper-artifacts/changed/source.rs', 75)),
        ('changed-helper-file-under-base', lambda: reverse(manifest, 'base', HERE / 'helper-artifacts/base/source.rs',
                                                           HERE / 'helper-artifacts/changed/generated/Funs.lean',
                                                           'generated_funs', 22)),
    ):
        try:
            action()
        except StaleArtifact as error:
            assert result['stale_rejections'][label] == str(error)
        else:
            raise AssertionError(label + ' accepted')
    return {'loop_generations': 2, 'rust_items_per_generation': 1,
            'generated_declarations_per_item': 3,
            'reverse_helper_links': 6, 'additional_stale_rejections': 2,
            'lean_evaluations_passed': 2, 'rfl_attempts_failed': 2}


if __name__ == '__main__':
    print(json.dumps(validate(), indent=2))
