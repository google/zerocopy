#!/usr/bin/env python3
"""Offline, byte-level validation of pinned provenance candidates and navigation."""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

from nav import StaleArtifact, digest, forward, reverse
from extra_check import validate as validate_extra
from helper_check import validate as validate_helper

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
REPO = HERE.parents[2]
ORIGIN = REPO / 'reports/anneal-3730-compatible-bundle-upgrade-golden-2026-09-29'
M = json.loads((HERE / 'manifest.json').read_text())
R = json.loads((HERE / 'results.json').read_text())
O = json.loads((ORIGIN / 'support/results.json').read_text())
META = json.loads((PACKAGE / 'REPORT.json').read_text())


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


assert M['schema'] == R['schema'] == 1
assert META['subjects'][1]['identity']['manifest_sha256'] == digest(HERE / 'manifest.json')
assert M['origin_report'] == ORIGIN.name
assert M['origin_results_sha256'] == digest(ORIGIN / 'support/results.json')
assert set(M['generations']) == {'base', 'changed'}
assert len(R['commands']) == 2 and len(R['navigation_checks']) == 6
assert len(R['stale_rejections']) == 3
assert 'no common producer-issued' in R['boundary']

locators = {}
for case, generation in M['generations'].items():
    root = HERE / 'artifacts' / case
    paths = {}
    for role, record in generation['artifacts'].items():
        path = PACKAGE / record['path']
        assert path.is_file()
        assert path.stat().st_size == record['bytes']
        assert digest(path) == record['sha256']
        paths[role] = path
    assert generation['source_case'] == 'june3-' + case
    origin_case = O['cases'][generation['source_case']]
    assert generation['artifacts']['rust_source']['sha256'] == origin_case['source_sha256']
    assert generation['artifacts']['llbc']['sha256'] == origin_case['llbc_sha256']
    assert generation['artifacts']['generated_funs']['sha256'] == origin_case['generated']['Funs.lean']['sha256']
    assert generation['artifacts']['proof']['sha256'] == origin_case['consumer']['Proof.lean']['sha256']
    assert generation['tool_pins']['charon_sha256'] == O['bundles']['june3']['binary_sha256']['charon']
    assert generation['tool_pins']['aeneas_sha256'] == O['bundles']['june3']['binary_sha256']['aeneas']
    assert generation['tool_pins']['lean_sha256'] == O['bundles']['june3']['lean_sha256']
    assert generation['tool_pins']['charon_llbc_version'] == '0.1.210'
    assert generation['prior_proof_exit'] == origin_case['proof_exit'] == 0
    assert 'sorryAx' not in origin_case['proof_stdout']
    source = paths['rust_source'].read_bytes()
    llbc = json.loads(paths['llbc'].read_text())
    funs = paths['generated_funs'].read_text()
    proof = paths['proof'].read_text()
    trace = generation['fresh_goal_probe']
    diagnostics = [json.loads(x) for x in trace['stdout'].splitlines()]
    assert trace['exit'] == 0 and trace['stderr'] == '' and len(diagnostics) == 3
    assert llbc['translated']['files'][0]['contents'].encode() == source
    assert llbc['translated']['files'][0]['name']['Local'] == 'src/lib.rs'
    assert generation['llbc_embeds_exact_rust_source'] is True
    assert len(generation['entries']) == 3
    signatures = []
    for index, entry in enumerate(generation['entries']):
        name = ('inc', 'twice', 'choose')[index]
        item = entry['rust_item']
        charon = entry['charon']
        aeneas = entry['aeneas']
        obligation = entry['obligation']
        assert item['qualified_name'] == charon['qualified_name'] == aeneas['emitted_name'] == f'bundle_golden::{name}'
        assert aeneas['qualified_lean_name'] == f'bundle_golden.{name}'
        assert obligation['name'] == f'obl_{name}'
        assert charon['file_id'] == 0 and charon['def_id'] == index
        lo, hi = item['byte_range']
        actual_text = source[lo:hi]
        assert sha(actual_text) == item['source_text_sha256']
        assert actual_text.startswith(f'pub fn {name}'.encode())
        assert {k: item['span'][k] for k in ('beg', 'end')} == aeneas['emitted_source_span']
        decl = next(x for x in llbc['translated']['fun_decls'] if x and x['def_id'] == index)
        assert decl['item_meta']['source_text'].encode() == actual_text
        assert decl['item_meta']['span']['data'] == item['span']
        assert charon['source_text_matches_rust'] is True
        assert aeneas['emitted_comment_matches_charon_name_span'] is True
        assert re.search(rf"\[bundle_golden::{name}\]:\n\s+Source: 'src/lib.rs', lines {item['span']['beg']['line']}:{item['span']['beg']['col']}-{item['span']['end']['line']}:{item['span']['end']['col']}", funs)
        start, end = aeneas['declaration_lines']
        assert funs.splitlines()[start - 1].startswith(f'def {name} ')
        assert end >= start
        assert proof.splitlines()[obligation['proof_line'] - 1].startswith(f'theorem obl_{name} : bundle_golden.{name} ')
        diag = diagnostics[index]
        assert diag['severity'] == 'information' and diag['kind'] == 'trace'
        assert diag['data'] == obligation['goal_text']
        assert diag['pos']['line'] == obligation['goal_trace_line']
        assert f'bundle_golden.{name}' in diag['data']
        assert 'fixture-authored' in obligation['provenance']
        assert 'no shared producer ID' in entry['cross_stage_join_class']
        found = forward(M, case, paths['rust_source'], (lo + hi) // 2)
        assert len(found) == 1 and found[0]['charon_def_id'] == index
        for role, line in (('generated_funs', start), ('proof', obligation['proof_line']),
                           ('goal_probe', obligation['goal_trace_line'])):
            back = reverse(M, case, paths['rust_source'], paths[role], role, line)
            assert len(back) == 1 and back[0]['rust_byte_range'] == [lo, hi]
        signatures.append((item['qualified_name'], tuple(item['byte_range']), index,
                           tuple(aeneas['declaration_lines']), obligation['proof_line']))
    locators[case] = signatures

assert locators['base'] == locators['changed']
assert M['generations']['base']['artifacts']['rust_source']['sha256'] != M['generations']['changed']['artifacts']['rust_source']['sha256']
assert M['generations']['base']['artifacts']['generated_funs']['sha256'] != M['generations']['changed']['artifacts']['generated_funs']['sha256']
for label, role, rust_case, lean_case in (
    ('base-source-with-changed-rust', None, 'changed', None),
    ('base-declaration-with-changed-lean', 'generated_funs', 'base', 'changed'),
    ('base-proof-with-changed-proof', 'proof', 'base', 'changed'),
):
    try:
        if role is None:
            forward(M, 'base', HERE / 'artifacts' / rust_case / 'Rust.lean-input.rs', 75)
        else:
            line = 21 if role == 'generated_funs' else 2
            reverse(M, 'base', HERE / 'artifacts' / rust_case / 'Rust.lean-input.rs',
                    HERE / 'artifacts' / lean_case / ('Funs.lean' if role == 'generated_funs' else 'Proof.lean'),
                    role, line)
    except StaleArtifact as error:
        assert R['stale_rejections'][label] == str(error)
    else:
        raise AssertionError(label + ' did not reject')

summary = {'generations': 2, 'items_per_generation': 3, 'forward_reverse_checks': 6,
           'fresh_goal_traces': 6, 'stale_rejections': 3,
           'same_name_span_id_and_lean_lines_despite_changed_bytes': True,
           'shared_producer_id_across_charon_aeneas_and_obligation': False}
summary['additional_join_controls'] = validate_extra()
summary['generated_helper_fanout'] = validate_helper()
(HERE / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print('PASS: 15 item links plus six helper links, seven stale controls, actual loop fanout and failed rfl preserved')
