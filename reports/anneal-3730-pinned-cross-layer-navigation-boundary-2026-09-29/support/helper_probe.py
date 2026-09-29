#!/usr/bin/env python3
"""One Rust loop item → three Aeneas Lean declarations under pinned local tools."""
from __future__ import annotations

import hashlib
import json
import re
import shutil
from pathlib import Path

from extra_probe import RUSTBIN, run, rust_env
from nav import StaleArtifact, digest, forward, reverse
from probe import AENEAS_ROOT, HERE, LEAN_ROOT, byte_span, lean_env

ROOT = HERE / 'helper-artifacts'
SOURCE = ('#![allow(dead_code)]\n'
          'pub fn sum_to(n: u32) -> u32 { let mut x = 0u32; let mut i = 0u32; while i < n { '
          'x = x.wrapping_add(i); i = i.wrapping_add(1); } x }\n')
CHANGED = SOURCE.replace('x = x.wrapping_add(i)', 'x = x.wrapping_add(1)')
COMMENT = re.compile(r"/-- \[loop_nav::sum_to\]:(?P<kind>[^\n]*)\n\s+Source: '(?P<path>[^']+)', lines (?P<bl>\d+):(?P<bc>\d+)-(?P<el>\d+):(?P<ec>\d+)\n\s+Visibility: public -/")


def artifact(path: Path) -> dict:
    return {'path': str(path.relative_to(HERE.parent)), 'bytes': path.stat().st_size, 'sha256': digest(path)}


def one(case: str) -> tuple[dict, list[dict]]:
    root = ROOT / case
    root.mkdir(parents=True)
    source = SOURCE if case == 'base' else CHANGED
    (root / 'source.rs').write_text(source)
    generated = root / 'generated'
    generated.mkdir()
    llbc = root / 'current.llbc'
    commands = []
    commands.append(run(case + '-charon', [AENEAS_ROOT / 'charon', 'rustc', '--preset', 'aeneas',
                                         '--dest-file', llbc, '--', root / 'source.rs', '--crate-type', 'lib',
                                         '--crate-name', 'loop_nav', '--edition', '2021'], root, rust_env()))
    assert commands[-1]['exit'] == 0, commands[-1]
    commands.append(run(case + '-aeneas', [AENEAS_ROOT / 'aeneas', '-backend', 'lean', '-no-progress-bar',
                                          '-sequential', '-split-files', '-gen-lib-entry', '-dest', generated, llbc], root))
    assert commands[-1]['exit'] == 0, commands[-1]
    (root / 'Current').mkdir()
    for name in ('Types', 'Funs'):
        shutil.copyfile(generated / f'{name}.lean', root / 'Current' / f'{name}.lean')
    shutil.copyfile(generated / 'Current.lean', root / 'Current.lean')
    for module in ('Current/Types', 'Current/Funs', 'Current'):
        commands.append(run(case + '-lean-compile-' + module,
                            [LEAN_ROOT / 'bin/lean', '-o', module + '.olean', module + '.lean'],
                            root, lean_env(root)))
        assert commands[-1]['exit'] == 0, commands[-1]
    value = 6 if case == 'base' else 4
    check = ('import Current\n'
             '#check loop_nav.sum_to_loop.body\n'
             '#check loop_nav.sum_to_loop\n'
             '#check loop_nav.sum_to\n'
             '#eval loop_nav.sum_to 4#u32\n')
    (root / 'Check.lean').write_text(check)
    commands.append(run(case + '-lean-check-eval', [LEAN_ROOT / 'bin/lean', '--json', 'Check.lean'], root, lean_env(root)))
    assert commands[-1]['exit'] == 0, commands[-1]
    attempt = ('import Current\n'
               f'theorem selected : loop_nav.sum_to 4#u32 = .ok {value}#u32 := by\n'
               '  trace_state\n  rfl\n')
    (root / 'Attempt.lean').write_text(attempt)
    commands.append(run(case + '-lean-rfl-attempt', [LEAN_ROOT / 'bin/lean', '--json', 'Attempt.lean'], root, lean_env(root)))
    assert commands[-1]['exit'] == 1 and 'Tactic `rfl` failed' in commands[-1]['stdout'], commands[-1]
    oracle = ('#[path = "source.rs"] mod subject;\n'
              f'fn main() {{ assert_eq!(subject::sum_to(4), {value}); }}\n')
    (root / 'RustOracle.rs').write_text(oracle)
    binary = root / 'rust-oracle'
    commands.append(run(case + '-rustc', [RUSTBIN / 'rustc', '--edition', '2021',
                                         root / 'RustOracle.rs', '-o', binary], root, rust_env()))
    assert commands[-1]['exit'] == 0, commands[-1]
    commands.append(run(case + '-rust-oracle', [binary], root))
    assert commands[-1]['exit'] == 0, commands[-1]
    binary.unlink()

    obj = json.loads(llbc.read_text())
    assert obj['translated']['files'][0]['contents'] == source
    locals_ = [d for d in obj['translated']['fun_decls'] if d and d['item_meta']['is_local']]
    assert len(locals_) == 1
    decl = locals_[0]
    assert '::'.join(x['Ident'][0] for x in decl['item_meta']['name'] if 'Ident' in x) == 'loop_nav::sum_to'
    span = decl['item_meta']['span']['data']
    source_bytes = source.encode()
    lo, hi = byte_span(source_bytes, decl['item_meta']['span'])
    assert source_bytes[lo:hi].decode() == decl['item_meta']['source_text']
    funs = (generated / 'Funs.lean').read_text()
    comments = list(COMMENT.finditer(funs))
    assert len(comments) == 3
    roles = ('loop_body', 'loop', 'wrapper')
    expected_names = ('loop_nav.sum_to_loop.body', 'loop_nav.sum_to_loop', 'loop_nav.sum_to')
    declarations = []
    for index, match in enumerate(comments):
        next_start = comments[index + 1].start() if index < 2 else funs.index('\nend loop_nav')
        block = funs[match.end():next_start]
        definition = re.search(r'^def\s+([\w.]+)\b', block, re.M)
        assert definition is not None
        name = 'loop_nav.' + definition.group(1)
        assert name == expected_names[index]
        begin = funs.count('\n', 0, match.end() + definition.start()) + 1
        end = funs.count('\n', 0, next_start)
        emitted_span = {'beg': {'line': int(match.group('bl')), 'col': int(match.group('bc'))},
                        'end': {'line': int(match.group('el')), 'col': int(match.group('ec'))}}
        assert span['beg']['line'] <= emitted_span['beg']['line'] <= emitted_span['end']['line'] <= span['end']['line']
        assert Path(match.group('path')).name == 'source.rs'
        declarations.append({'role': roles[index], 'qualified_lean_name': name,
                             'declaration_lines': [begin, end], 'emitted_source_path': match.group('path'),
                             'emitted_source_span': emitted_span, 'emitted_comment_kind': match.group('kind').strip()})
    check_record = next(x for x in commands if x['label'] == case + '-lean-check-eval')
    attempt_record = next(x for x in commands if x['label'] == case + '-lean-rfl-attempt')
    diagnostics = [json.loads(x) for x in check_record['stdout'].splitlines()]
    attempts = [json.loads(x) for x in attempt_record['stdout'].splitlines()]
    assert len(diagnostics) == 4 and len(attempts) == 2
    assert 'Result.ok' in diagnostics[-1]['data'] and f'0x0000000{value}' in diagnostics[-1]['data']
    assert any(x['kind'] == 'trace' and f'loop_nav.sum_to 4#u32 = Aeneas.Std.Result.ok {value}#u32' in x['data'] for x in attempts)
    paths = {'rust_source': root / 'source.rs', 'llbc': llbc,
             'generated_funs': generated / 'Funs.lean',
             'generated_types': generated / 'Types.lean',
             'generated_entry': generated / 'Current.lean',
             'funs_olean': root / 'Current/Funs.olean',
             'entry_olean': root / 'Current.olean', 'lean_check': root / 'Check.lean',
             'goal_attempt': root / 'Attempt.lean',
             'rust_oracle': root / 'RustOracle.rs'}
    generation = {'source_case': case, 'artifacts': {role: artifact(path) for role, path in paths.items()},
                  'llbc_embeds_exact_rust_source': True,
                  'entries': [{'rust_item': {'qualified_name': 'loop_nav::sum_to', 'byte_range': [lo, hi],
                                            'span': span, 'source_text_sha256': hashlib.sha256(decl['item_meta']['source_text'].encode()).hexdigest()},
                               'charon': {'def_id': decl['def_id'], 'file_id': span['file_id']},
                               'aeneas': {'declarations': declarations},
                               'obligation': {'name': 'selected_value_eval', 'proof_line': 5, 'goal_trace_line': 3,
                                              'provenance': 'fixture-authored evaluation and failed rfl attempt, not producer-issued'},
                               'cross_stage_join_class': 'Aeneas emitted same source item name and contained spans for three declarations; no shared producer ID'}],
                  'lean_diagnostics': diagnostics, 'failed_rfl_diagnostics': attempts,
                  'selected_value': value}
    return generation, commands


def main() -> None:
    assert shutil.disk_usage(HERE).free > 10 * 1024**3
    if ROOT.exists():
        shutil.rmtree(ROOT)
    ROOT.mkdir()
    generations, commands = {}, []
    for case in ('base', 'changed'):
        generations[case], record = one(case)
        commands.extend(record)
    manifest = {'schema': 1, 'tool_sha256': {'charon': digest(AENEAS_ROOT / 'charon'),
                                             'aeneas': digest(AENEAS_ROOT / 'aeneas'),
                                             'lean': digest(LEAN_ROOT / 'bin/lean')},
                'generations': generations,
                'join_assurance': 'producer-emitted repeated source name and contained spans; helper relation is derived, not a shared stable ID'}
    (HERE / 'helper-manifest.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
    navigation = []
    for case, generation in generations.items():
        root = ROOT / case
        rust = root / 'source.rs'
        item = generation['entries'][0]
        lo, hi = item['rust_item']['byte_range']
        targets = forward(manifest, case, rust, (lo + hi) // 2)
        assert len(targets) == 1 and len(targets[0]['generated_decls']) == 3
        links = []
        for declaration in item['aeneas']['declarations']:
            result = reverse(manifest, case, rust, root / 'generated/Funs.lean',
                             'generated_funs', declaration['declaration_lines'][0])
            assert len(result) == 1 and result[0]['rust_item'] == 'loop_nav::sum_to'
            links.append({'declaration': declaration['qualified_lean_name'], 'reverse': result})
        eval_back = reverse(manifest, case, rust, root / 'Check.lean', 'lean_check', 5)
        goal_back = reverse(manifest, case, rust, root / 'Attempt.lean', 'goal_attempt', 3)
        assert len(eval_back) == len(goal_back) == 1
        assert eval_back[0]['rust_item'] == goal_back[0]['rust_item'] == 'loop_nav::sum_to'
        navigation.append({'case': case, 'forward': targets, 'reverse_helpers': links,
                           'reverse_eval': eval_back, 'reverse_goal_attempt': goal_back})
    stale = {}
    for label, action in (
        ('changed-source-under-base', lambda: forward(manifest, 'base', ROOT / 'changed/source.rs', 75)),
        ('changed-helper-file-under-base', lambda: reverse(manifest, 'base', ROOT / 'base/source.rs',
                                                           ROOT / 'changed/generated/Funs.lean', 'generated_funs',
                                                           generations['base']['entries'][0]['aeneas']['declarations'][0]['declaration_lines'][0])),
    ):
        try:
            action()
        except StaleArtifact as error:
            stale[label] = str(error)
        else:
            raise AssertionError(label + ' accepted')
    assert generations['base']['artifacts']['rust_source']['sha256'] != generations['changed']['artifacts']['rust_source']['sha256']
    assert generations['base']['artifacts']['generated_funs']['sha256'] != generations['changed']['artifacts']['generated_funs']['sha256']
    output = {'schema': 1, 'commands': commands, 'navigation': navigation,
              'stale_rejections': stale,
              'boundary': 'One Charon local sum_to item and three Aeneas generated Lean defs; same-name/contained-span relation is derived, not producer-authenticated.'}
    (HERE / 'helper-results.json').write_text(json.dumps(output, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'generations': 2, 'generated_declarations_per_source_item': 3,
                      'reverse_helper_links': sum(len(x['reverse_helpers']) for x in navigation),
                      'stale_rejections': stale}, indent=2))


if __name__ == '__main__':
    main()
