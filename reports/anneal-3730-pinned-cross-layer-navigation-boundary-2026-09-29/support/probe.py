#!/usr/bin/env python3
"""Derive pinned navigation evidence from already-retained R44 full-pipeline output."""
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
from pathlib import Path

from nav import StaleArtifact, digest, forward, reverse

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
R44 = REPO / 'reports/anneal-3730-compatible-bundle-upgrade-golden-2026-09-29'
R44_RESULTS = json.loads((R44 / 'support/results.json').read_text())
ARTIFACTS = HERE / 'artifacts'
LEAN_ROOT = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2')
AENEAS_ROOT = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/aeneas-release')
PACKAGES = ('Cli', 'batteries', 'Qq', 'aesop', 'proofwidgets', 'importGraph',
            'LeanSearchClient', 'plausible', 'mathlib')
NAMES = ('inc', 'twice', 'choose')
DOC = re.compile(r"/-- \[bundle_golden::(?P<name>\w+)\]:\n\s+Source: '(?P<path>[^']+)', lines (?P<begin_line>\d+):(?P<begin_col>\d+)-(?P<end_line>\d+):(?P<end_col>\d+)\n\s+Visibility: public -/\n(?P<definition>def (?P<def_name>\w+)\b)")
THEOREM = re.compile(r'^theorem (obl_(\w+)) : bundle_golden\.(\w+)\b', re.M)


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def artifact(path: Path) -> dict:
    return {'path': str(path.relative_to(HERE.parent)), 'bytes': path.stat().st_size, 'sha256': digest(path)}


def byte_span(source: bytes, span: dict) -> list[int]:
    data = span['data']
    lines = source.splitlines(keepends=True)
    begin, end = data['beg'], data['end']
    assert 1 <= begin['line'] <= len(lines) and 1 <= end['line'] <= len(lines)
    lo = sum(len(x) for x in lines[:begin['line'] - 1]) + begin['col']
    hi = sum(len(x) for x in lines[:end['line'] - 1]) + end['col']
    return [lo, hi]


def lean_env(root: Path) -> dict:
    cached = AENEAS_ROOT / 'backends/lean/.lake/packages'
    libs = [root, AENEAS_ROOT / 'backends/lean/.lake/build/lib/lean']
    libs += [cached / p / '.lake/build/lib/lean' for p in PACKAGES]
    libs += [LEAN_ROOT / 'lib/lean']
    env = dict(os.environ)
    env['LEAN_PATH'] = os.pathsep.join(str(p) for p in libs if p.is_dir())
    env['LEAN_NUM_THREADS'] = '1'
    return env


def one(case: str) -> tuple[dict, dict]:
    original = R44 / 'support/work' / f'june3-{case}'
    source_case = R44_RESULTS['cases'][f'june3-{case}']
    copied = ARTIFACTS / case
    (copied / 'Current').mkdir(parents=True)
    selected = {
        'rust_source': ('crate/src/lib.rs', 'Rust.lean-input.rs'),
        'llbc': ('current.llbc', 'current.llbc'),
        'generated_funs': ('generated/Funs.lean', 'Funs.lean'),
        'generated_types': ('generated/Types.lean', 'Types.lean'),
        'generated_entry': ('generated/Current.lean', 'Current.lean'),
        'proof': ('consumer/Proof.lean', 'Proof.lean'),
        'types_olean': ('consumer/Current/Types.olean', 'Current/Types.olean'),
        'funs_olean': ('consumer/Current/Funs.olean', 'Current/Funs.olean'),
        'entry_olean': ('consumer/Current.olean', 'Current.olean'),
    }
    paths = {}
    for role, (from_name, to_name) in selected.items():
        target = copied / to_name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(original / from_name, target)
        paths[role] = target
    source = paths['rust_source'].read_bytes()
    llbc = json.loads(paths['llbc'].read_text())
    generated = paths['generated_funs'].read_text()
    proof = paths['proof'].read_text()
    assert source.decode() == llbc['translated']['files'][0]['contents']
    assert sha(source) == source_case['source_sha256']
    assert digest(paths['llbc']) == source_case['llbc_sha256']
    assert digest(paths['generated_funs']) == source_case['generated']['Funs.lean']['sha256']
    assert llbc['translated']['files'][0]['name']['Local'] == 'src/lib.rs'
    assert llbc['translated']['files'][0]['id'] == 0

    doc_matches = list(DOC.finditer(generated))
    assert [x.group('name') for x in doc_matches] == list(NAMES)
    theorem_matches = list(THEOREM.finditer(proof))
    assert [(x.group(1), x.group(2), x.group(3)) for x in theorem_matches] == [
        ('obl_' + n, n, n) for n in NAMES]
    defs = {d['item_meta']['name'][-1]['Ident'][0]: d for d in llbc['translated']['fun_decls']
            if d and d['item_meta']['name'][-1].get('Ident') and d['item_meta']['name'][0].get('Ident', [None])[0] == 'bundle_golden'}

    values = (1, 2, 3) if case == 'base' else (2, 4, 5)
    goal_lines = ['import Current']
    for name, value in zip(NAMES, values):
        goal_lines += [f'theorem nav_{name} : bundle_golden.{name} 0#u32 = .ok {value}#u32 := by',
                       '  trace_state', '  rfl']
    paths['goal_probe'] = copied / 'GoalProbe.lean'
    paths['goal_probe'].write_text('\n'.join(goal_lines) + '\n')
    run = subprocess.run([str(LEAN_ROOT / 'bin/lean'), '--json', 'GoalProbe.lean'], cwd=copied,
                         env=lean_env(copied), capture_output=True, text=True, timeout=60)
    diagnostics = [json.loads(x) for x in run.stdout.splitlines()]
    assert run.returncode == 0 and not run.stderr and len(diagnostics) == 3, (run.returncode, run.stdout, run.stderr)
    assert all(d['severity'] == 'information' and d['kind'] == 'trace' for d in diagnostics)

    entries = []
    for index, name in enumerate(NAMES):
        declaration = defs[name]
        span = declaration['item_meta']['span']
        region = byte_span(source, span)
        original_text = declaration['item_meta']['source_text']
        assert source[region[0]:region[1]].decode() == original_text
        match = doc_matches[index]
        assert match.group('name') == match.group('def_name') == name
        comment_span = {'beg': {'line': int(match.group('begin_line')), 'col': int(match.group('begin_col'))},
                        'end': {'line': int(match.group('end_line')), 'col': int(match.group('end_col'))}}
        assert comment_span == {'beg': span['data']['beg'], 'end': span['data']['end']}
        assert match.group('path') == 'src/lib.rs'
        def_line = generated.count('\n', 0, match.start('definition')) + 1
        next_start = doc_matches[index + 1].start() if index + 1 < len(doc_matches) else generated.index('\nend bundle_golden')
        end_line = generated.count('\n', 0, next_start)
        proof_line = proof.count('\n', 0, theorem_matches[index].start()) + 1
        trace = diagnostics[index]
        assert f'bundle_golden.{name} 0#u32' in trace['data']
        assert trace['pos']['line'] == 3 + index * 3
        entries.append({
            'rust_item': {'qualified_name': f'bundle_golden::{name}', 'source_path': 'src/lib.rs',
                          'byte_range': region, 'span': span['data'], 'source_text_sha256': sha(original_text.encode())},
            'charon': {'file_id': 0, 'def_id': declaration['def_id'],
                       'qualified_name': f'bundle_golden::{name}', 'source_text_matches_rust': True},
            'aeneas': {'emitted_source_path': match.group('path'), 'emitted_source_span': comment_span,
                       'emitted_name': f'bundle_golden::{name}', 'qualified_lean_name': f'bundle_golden.{name}',
                       'declaration_lines': [def_line, end_line],
                       'emitted_comment_matches_charon_name_span': True},
            'obligation': {'name': f'obl_{name}', 'proof_line': proof_line,
                           'proposition': theorem_matches[index].group(0),
                           'goal_trace_line': trace['pos']['line'], 'goal_text': trace['data'],
                           'provenance': 'fixture-authored theorem/probe, not Aeneas or Anneal producer issued'},
            'cross_stage_join_class': 'derived match on producer-emitted qualified name and source span; no shared producer ID',
        })
    generation = {'source_case': f'june3-{case}', 'tool_pins': {
        'charon_sha256': R44_RESULTS['bundles']['june3']['binary_sha256']['charon'],
        'aeneas_sha256': R44_RESULTS['bundles']['june3']['binary_sha256']['aeneas'],
        'lean_sha256': R44_RESULTS['bundles']['june3']['lean_sha256'],
        'charon_llbc_version': llbc['charon_version']},
        'artifacts': {role: artifact(path) for role, path in paths.items()},
        'llbc_embeds_exact_rust_source': True,
        'fresh_goal_probe': {'exit': run.returncode, 'stdout': run.stdout, 'stderr': run.stderr},
        'prior_proof_exit': source_case['proof_exit'],
        'entries': entries}
    return generation, {'case': case, 'goal_probe_command': [str(LEAN_ROOT / 'bin/lean'), '--json', 'GoalProbe.lean'],
                        'cwd': str(copied), 'exit': run.returncode, 'stdout': run.stdout, 'stderr': run.stderr}


def main() -> None:
    assert (LEAN_ROOT / 'bin/lean').is_file() and AENEAS_ROOT.is_dir()
    if ARTIFACTS.exists():
        shutil.rmtree(ARTIFACTS)
    generations, commands = {}, []
    for case in ('base', 'changed'):
        generations[case], record = one(case)
        commands.append(record)
    manifest = {'schema': 1, 'origin_report': R44.name, 'origin_results_sha256': digest(R44 / 'support/results.json'),
                'join_assurance': 'content-pinned artifacts and checked emitted spans; Charon ID-to-Lean declaration and obligation links are derived/manual, not authenticated by a shared producer key',
                'generations': generations}
    (HERE / 'manifest.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
    checks = []
    for case, gen in generations.items():
        root = ARTIFACTS / case
        for entry in gen['entries']:
            mid = sum(entry['rust_item']['byte_range']) // 2
            target = forward(manifest, case, root / 'Rust.lean-input.rs', mid)
            assert len(target) == 1 and target[0]['rust_item'] == entry['rust_item']['qualified_name']
            back_def = reverse(manifest, case, root / 'Rust.lean-input.rs', root / 'Funs.lean',
                               'generated_funs', entry['aeneas']['declaration_lines'][0])
            back_proof = reverse(manifest, case, root / 'Rust.lean-input.rs', root / 'Proof.lean',
                                 'proof', entry['obligation']['proof_line'])
            back_goal = reverse(manifest, case, root / 'Rust.lean-input.rs', root / 'GoalProbe.lean',
                                'goal_probe', entry['obligation']['goal_trace_line'])
            assert len(back_def) == len(back_proof) == len(back_goal) == 1
            assert all(x[0]['charon_def_id'] == entry['charon']['def_id'] for x in (back_def, back_proof, back_goal))
            checks.append({'case': case, 'rust_item': entry['rust_item']['qualified_name'],
                           'forward': target, 'reverse_declaration': back_def,
                           'reverse_proof': back_proof, 'reverse_goal': back_goal})
    failures = {}
    controls = [
        ('base-source-with-changed-rust', lambda: forward(manifest, 'base', ARTIFACTS / 'changed/Rust.lean-input.rs', 75)),
        ('base-declaration-with-changed-lean', lambda: reverse(manifest, 'base', ARTIFACTS / 'base/Rust.lean-input.rs',
                                                               ARTIFACTS / 'changed/Funs.lean', 'generated_funs', 21)),
        ('base-proof-with-changed-proof', lambda: reverse(manifest, 'base', ARTIFACTS / 'base/Rust.lean-input.rs',
                                                         ARTIFACTS / 'changed/Proof.lean', 'proof', 2)),
    ]
    for label, control in controls:
        try:
            control()
        except StaleArtifact as error:
            failures[label] = str(error)
        else:
            raise AssertionError('stale control passed: ' + label)
    output = {'schema': 1, 'commands': commands, 'navigation_checks': checks,
              'stale_rejections': failures,
              'boundary': 'Rust bytes are embedded by Charon and Aeneas comments match name/span, but no common producer-issued declaration/obligation ID exists in retained outputs.'}
    (HERE / 'results.json').write_text(json.dumps(output, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'generations': len(generations), 'forward_reverse_checks': len(checks),
                      'stale_rejections': failures}, indent=2))


if __name__ == '__main__':
    main()
