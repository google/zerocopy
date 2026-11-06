#!/usr/bin/env python3
"""Stress derived navigation joins with reorder and same-leaf-name fixtures."""
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
from pathlib import Path

from nav import StaleArtifact, digest, forward, reverse
from probe import AENEAS_ROOT, ARTIFACTS, HERE, LEAN_ROOT, REPO, byte_span, lean_env

R12 = REPO / 'reports/anneal-3730-cross-layer-comparator-mutants-2026-09-29'
R12_RESULT = json.loads((R12 / 'support/results.json').read_text())
TOOLS = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RUSTBIN = TOOLS / 'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
EXTRA = HERE / 'extra-artifacts'
DOC = re.compile(r"/-- \[(?P<qualified>[^]]+)\]:\n\s+Source: '(?P<path>[^']+)', lines (?P<bl>\d+):(?P<bc>\d+)-(?P<el>\d+):(?P<ec>\d+)\n\s+Visibility: public -/\n(?P<definition>def (?P<lean_name>[^\s(]+))")
THM = re.compile(r'^theorem\s+(?P<name>\w+)\s*:\s*(?P<target>[\w.]+)\b', re.M)
AMBIGUOUS = '''#![allow(dead_code)]
pub mod left { pub fn step(x: u32) -> u32 { x.wrapping_add(1) } }
pub mod right { pub fn step(x: u32) -> u32 { x.wrapping_add(2) } }
pub fn both(x: u32) -> u32 { left::step(right::step(x)) }
#[cfg(test)] mod tests { use super::*; #[test] fn values() { assert_eq!(left::step(0), 1); assert_eq!(right::step(0), 2); assert_eq!(both(0), 3); } }
'''


def artifact(path: Path) -> dict:
    return {'path': str(path.relative_to(HERE.parent)), 'bytes': path.stat().st_size, 'sha256': digest(path)}


def rust_env() -> dict:
    env = dict(os.environ)
    env.update({'RUSTUP_HOME': str(TOOLS / 'rustup'), 'CARGO_HOME': str(TOOLS / 'cargo'),
                'CHARON_TOOLCHAIN_IS_IN_PATH': '1',
                'PATH': os.pathsep.join((str(RUSTBIN), str(TOOLS / 'bin'), env.get('PATH', ''))),
                'DYLD_LIBRARY_PATH': os.pathsep.join((str(RUSTBIN.parent / 'lib'),
                    str(RUSTBIN.parent / 'lib/rustlib/aarch64-apple-darwin/lib'),
                    env.get('DYLD_LIBRARY_PATH', '')))})
    return env


def run(label: str, argv: list, cwd: Path, env=None, timeout=90) -> dict:
    p = subprocess.run([str(x) for x in argv], cwd=cwd, env=env,
                       capture_output=True, text=True, timeout=timeout)
    return {'label': label, 'argv': [str(x) for x in argv], 'cwd': str(cwd),
            'exit': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr}


def copied_reorder(case: str) -> dict:
    original = R12 / 'support/work' / case
    dest = EXTRA / ('reorder-' + case)
    dest.mkdir(parents=True)
    names = {'rust_source': ('source.rs', 'source.rs'),
             'llbc': ('Source.llbc', 'Source.llbc'),
             'generated_funs': ('generated/Funs.lean', 'Funs.lean'),
             'proof': (f'../consumer-{case}/Proof.lean', 'Proof.lean')}
    paths = {}
    for role, (source, target) in names.items():
        paths[role] = dest / target
        shutil.copyfile(original / source, paths[role])
    for role, key in (('rust_source', 'source_sha256'), ('llbc', 'llbc_sha256')):
        assert digest(paths[role]) == R12_RESULT['cases'][case][key]
    assert digest(paths['generated_funs']) == R12_RESULT['cases'][case]['generated']['Funs.lean']['sha256']
    return paths


def ambiguous_case() -> tuple[dict, list[dict]]:
    dest = EXTRA / 'ambiguous'
    dest.mkdir(parents=True)
    paths = {'rust_source': dest / 'source.rs', 'llbc': dest / 'current.llbc',
             'generated_funs': dest / 'generated/Funs.lean', 'proof': dest / 'Proof.lean'}
    paths['rust_source'].write_text(AMBIGUOUS)
    output = dest / 'generated'
    output.mkdir()
    commands = []
    charon = AENEAS_ROOT / 'charon'
    aeneas = AENEAS_ROOT / 'aeneas'
    commands.append(run('ambiguous-charon', [charon, 'rustc', '--preset', 'aeneas', '--dest-file', paths['llbc'],
                                           '--', paths['rust_source'], '--crate-type', 'lib', '--crate-name',
                                           'nav_ambig', '--edition', '2021'], dest, rust_env()))
    assert commands[-1]['exit'] == 0, commands[-1]
    commands.append(run('ambiguous-aeneas', [aeneas, '-backend', 'lean', '-no-progress-bar', '-sequential',
                                            '-split-files', '-gen-lib-entry', '-dest', output, paths['llbc']], dest))
    assert commands[-1]['exit'] == 0, commands[-1]
    paths['generated_types'] = output / 'Types.lean'
    paths['generated_entry'] = output / 'Current.lean'
    (dest / 'Current').mkdir()
    shutil.copyfile(paths['generated_types'], dest / 'Current/Types.lean')
    shutil.copyfile(paths['generated_funs'], dest / 'Current/Funs.lean')
    shutil.copyfile(paths['generated_entry'], dest / 'Current.lean')
    for module in ('Current/Types', 'Current/Funs', 'Current'):
        commands.append(run('ambiguous-lean-compile-' + module,
                            [LEAN_ROOT / 'bin/lean', '-o', module + '.olean', module + '.lean'],
                            dest, lean_env(dest)))
        assert commands[-1]['exit'] == 0, commands[-1]
    paths['types_olean'] = dest / 'Current/Types.olean'
    paths['funs_olean'] = dest / 'Current/Funs.olean'
    paths['entry_olean'] = dest / 'Current.olean'
    proof = ('import Current\n'
             'theorem obl_left_step : nav_ambig.left.step 0#u32 = .ok 1#u32 := by\n  trace_state\n  rfl\n'
             'theorem obl_right_step : nav_ambig.right.step 0#u32 = .ok 2#u32 := by\n  trace_state\n  rfl\n'
             'theorem obl_both : nav_ambig.both 0#u32 = .ok 3#u32 := by\n  trace_state\n  rfl\n')
    paths['proof'].write_text(proof)
    commands.append(run('ambiguous-lean-proof', [LEAN_ROOT / 'bin/lean', '--json', 'Proof.lean'],
                        dest, lean_env(dest)))
    assert commands[-1]['exit'] == 0 and len(commands[-1]['stdout'].splitlines()) == 3, commands[-1]
    test_binary = dest / 'rust-test'
    commands.append(run('ambiguous-rust-test-build', [RUSTBIN / 'rustc', '--edition', '2021',
                        '--test', paths['rust_source'], '-o', test_binary], dest, rust_env()))
    assert commands[-1]['exit'] == 0, commands[-1]
    commands.append(run('ambiguous-rust-test', [test_binary], dest))
    assert commands[-1]['exit'] == 0 and '1 passed' in commands[-1]['stdout'], commands[-1]
    test_binary.unlink()
    return paths, commands


def generation(label: str, paths: dict) -> dict:
    source = paths['rust_source'].read_bytes()
    llbc = json.loads(paths['llbc'].read_text())
    funs = paths['generated_funs'].read_text()
    proof = paths['proof'].read_text()
    assert llbc['translated']['files'][0]['contents'].encode() == source
    docs = list(DOC.finditer(funs))
    docs_by_qualified = {x.group('qualified'): x for x in docs}
    theorems = {x.group('target'): x for x in THM.finditer(proof)}
    entries = []
    for declaration in llbc['translated']['fun_decls']:
        if not declaration or not declaration['item_meta']['is_local']:
            continue
        qualified = '::'.join(x['Ident'][0] for x in declaration['item_meta']['name'] if 'Ident' in x)
        match = docs_by_qualified[qualified]
        name = match.group('lean_name')
        lean_qualified = qualified.split('::')[0] + '.' + name
        theorem = theorems[lean_qualified]
        span = declaration['item_meta']['span']['data']
        positions = byte_span(source, declaration['item_meta']['span'])
        assert source[positions[0]:positions[1]].decode() == declaration['item_meta']['source_text']
        comment_span = {'beg': {'line': int(match.group('bl')), 'col': int(match.group('bc'))},
                        'end': {'line': int(match.group('el')), 'col': int(match.group('ec'))}}
        assert comment_span == {'beg': span['beg'], 'end': span['end']}
        assert Path(match.group('path')).name == 'source.rs'
        def_line = funs.count('\n', 0, match.start('definition')) + 1
        next_doc = next((d.start() for d in docs if d.start() > match.start()), funs.index('\nend ' + qualified.split('::')[0]))
        end_line = funs.count('\n', 0, next_doc)
        proof_line = proof.count('\n', 0, theorem.start()) + 1
        entries.append({'rust_item': {'qualified_name': qualified, 'byte_range': positions, 'span': span,
                                      'source_text_sha256': hashlib.sha256(declaration['item_meta']['source_text'].encode()).hexdigest()},
                        'charon': {'def_id': declaration['def_id'], 'file_id': span['file_id']},
                        'aeneas': {'emitted_name': qualified, 'emitted_source_path': match.group('path'),
                                   'emitted_source_span': comment_span,
                                   'qualified_lean_name': lean_qualified,
                                   'declaration_lines': [def_line, end_line]},
                        'obligation': {'name': theorem.group('name'), 'proof_line': proof_line,
                                       'goal_trace_line': proof_line + 1 if label == 'ambiguous' else None,
                                       'provenance': 'fixture-authored, not producer-authenticated'},
                        'cross_stage_join_class': 'derived qualified-name/span match; no shared producer ID'})
    assert len(entries) == 3
    return {'source_case': label, 'artifacts': {k: artifact(v) for k, v in paths.items()},
            'llbc_embeds_exact_rust_source': True, 'entries': entries,
            'lean_proof_exit': 0,
            'qualified_names': [e['rust_item']['qualified_name'] for e in entries]}


def main() -> None:
    assert shutil.disk_usage(HERE).free > 10 * 1024**3
    assert digest(AENEAS_ROOT / 'charon') == R12_RESULT['subjects']['charon_sha256']
    assert digest(AENEAS_ROOT / 'aeneas') == R12_RESULT['subjects']['aeneas_sha256']
    assert digest(LEAN_ROOT / 'bin/lean') == R12_RESULT['subjects']['lean_sha256']
    if EXTRA.exists():
        shutil.rmtree(EXTRA)
    EXTRA.mkdir()
    paths = {case: copied_reorder(case) for case in ('base', 'reorder')}
    paths['ambiguous'], commands = ambiguous_case()
    generations = {'reorder-' + case: generation('reorder-' + case, paths[case])
                   for case in ('base', 'reorder')}
    generations['ambiguous'] = generation('ambiguous', paths['ambiguous'])
    manifest = {'schema': 1, 'r12_source_report': R12.name,
                'r12_results_sha256': digest(R12 / 'support/results.json'),
                'tool_sha256': {'charon': digest(AENEAS_ROOT / 'charon'),
                                'aeneas': digest(AENEAS_ROOT / 'aeneas'),
                                'lean': digest(LEAN_ROOT / 'bin/lean')},
                'generations': generations,
                'boundary': 'fully qualified names and emitted spans are derived joins, not shared producer-issued IDs'}
    (HERE / 'extra-manifest.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
    nav_results = []
    for case, gen in generations.items():
        root = EXTRA / case
        for e in gen['entries']:
            lo, hi = e['rust_item']['byte_range']
            fwd = forward(manifest, case, root / 'source.rs', (lo + hi) // 2)
            funs_path = HERE.parent / gen['artifacts']['generated_funs']['path']
            rev = reverse(manifest, case, root / 'source.rs', funs_path,
                          'generated_funs', e['aeneas']['declaration_lines'][0])
            assert len(fwd) == len(rev) == 1
            assert fwd[0]['rust_item'] == rev[0]['rust_item'] == e['rust_item']['qualified_name']
            nav_results.append({'case': case, 'item': e['rust_item']['qualified_name'],
                                'forward': fwd, 'reverse': rev})
    base = generations['reorder-base']['entries']
    changed = generations['reorder-reorder']['entries']
    base_by_id = {e['charon']['def_id']: e['rust_item']['qualified_name'] for e in base}
    reorder_by_id = {e['charon']['def_id']: e['rust_item']['qualified_name'] for e in changed}
    base_by_name = {e['rust_item']['qualified_name']: e['charon']['def_id'] for e in base}
    reorder_by_name = {e['rust_item']['qualified_name']: e['charon']['def_id'] for e in changed}
    assert base_by_id[0] == 'comparator_probe::inc'
    assert reorder_by_id[0] == 'comparator_probe::choose'
    assert base_by_name['comparator_probe::inc'] == 0
    assert reorder_by_name['comparator_probe::inc'] == 2
    generated_order_base = [e['aeneas']['qualified_lean_name'] for e in sorted(base, key=lambda e: e['aeneas']['declaration_lines'][0])]
    generated_order_reorder = [e['aeneas']['qualified_lean_name'] for e in sorted(changed, key=lambda e: e['aeneas']['declaration_lines'][0])]
    assert generated_order_base == generated_order_reorder == ['comparator_probe.inc', 'comparator_probe.twice', 'comparator_probe.choose']
    ambig = generations['ambiguous']['entries']
    same_leaf = [e['rust_item']['qualified_name'] for e in ambig if e['rust_item']['qualified_name'].endswith('::step')]
    assert same_leaf == ['nav_ambig::left::step', 'nav_ambig::right::step']
    stale = {}
    for label, action in (
        ('reordered-rust-under-base', lambda: forward(manifest, 'reorder-base', EXTRA / 'reorder-reorder/source.rs', 50)),
        ('reordered-lean-under-base', lambda: reverse(manifest, 'reorder-base', EXTRA / 'reorder-base/source.rs',
                                                      EXTRA / 'reorder-reorder/Funs.lean', 'generated_funs', 21)),
    ):
        try:
            action()
        except StaleArtifact as error:
            stale[label] = str(error)
        else:
            raise AssertionError(label + ' accepted')
    output = {'schema': 1, 'commands': commands, 'navigation': nav_results,
              'reorder': {'base_by_def_id': base_by_id, 'reordered_by_def_id': reorder_by_id,
                          'base_def_id_by_name': base_by_name, 'reordered_def_id_by_name': reorder_by_name,
                          'generated_order_base': generated_order_base,
                          'generated_order_reordered': generated_order_reorder,
                          'def_id_0_wrong_join_if_reused': [base_by_id[0], reorder_by_id[0]]},
              'ambiguity': {'leaf': 'step', 'leaf_only_candidates': same_leaf,
                            'qualified_span_join_unique': True,
                            'rust_test_exit': commands[-1]['exit'],
                            'lean_proof_exit': next(x['exit'] for x in commands if x['label'] == 'ambiguous-lean-proof'),
                            'lean_trace': next(x['stdout'] for x in commands if x['label'] == 'ambiguous-lean-proof')},
              'stale_rejections': stale}
    (HERE / 'extra-results.json').write_text(json.dumps(output, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'navigation_cases': len(nav_results), 'stale_rejections': stale,
                      'def_id_0_changes': output['reorder']['def_id_0_wrong_join_if_reused'],
                      'leaf_step_candidates': same_leaf}, indent=2))


if __name__ == '__main__':
    main()
