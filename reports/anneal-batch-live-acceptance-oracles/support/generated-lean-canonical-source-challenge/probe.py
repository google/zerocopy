#!/usr/bin/env python3
"""Synthetic Rust-hosted view over canonical Lean proof; not Anneal V2."""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
from pathlib import Path

RUST_1 = 'pub fn model_add(x: u32) -> u32 { x + 1 }\n'
PROOF_1 = ('import Model\n\n-- source note: 🦀 β\n'
           'theorem claim : modelAdd 1 = 2 := by\n  rfl\n')
PREFIX = '//| '
BEGIN = '// BEGIN SYNTHETIC LEAN PROOF VIEW'
END = '// END SYNTHETIC LEAN PROOF VIEW'


def digest(data):
    if isinstance(data, Path):
        data = data.read_bytes()
    if isinstance(data, str):
        data = data.encode()
    return hashlib.sha256(data).hexdigest()


def run(argv, cwd, env=None):
    p = subprocess.run([str(x) for x in argv], cwd=cwd, env=env,
                       capture_output=True, text=True, timeout=25)
    return {'argv': [str(x) for x in argv], 'exit': p.returncode,
            'stdout': p.stdout, 'stderr': p.stderr}


def unit16(text):
    return len(text.encode('utf-16-le')) // 2


def index_from_unit16(text, offset):
    if offset < 0:
        raise ValueError('negative UTF-16 offset')
    for index in range(len(text) + 1):
        units = unit16(text[:index])
        if units == offset:
            return index
        if units > offset:
            raise ValueError('UTF-16 offset splits scalar')
    raise ValueError('UTF-16 offset past line')


def render(rust, proof):
    head = (rust.rstrip('\n') + '\n\n'
            + f'// Generated Rust-hosted view; canonical Proof.lean SHA-256: {digest(proof)}\n'
            + BEGIN + '\n')
    view_lines = head.splitlines(keepends=True)
    mappings = []
    for proof_line, line in enumerate(proof.splitlines(keepends=True)):
        view_line = len(view_lines)
        view_lines.append(PREFIX + line)
        mappings.append({'proof_line_0': proof_line, 'view_line_0': view_line,
                         'view_prefix_utf16': unit16(PREFIX),
                         'proof_line_sha256': digest(line)})
    view_lines.append(END + '\n')
    view = ''.join(view_lines)
    return view, {'proof_sha256': digest(proof), 'rust_sha256': digest(rust),
                  'view_sha256': digest(view), 'mappings': mappings}


def parse_view(view):
    lines = view.splitlines(keepends=True)
    begin = next(i for i, line in enumerate(lines) if line.rstrip('\n') == BEGIN)
    end = next(i for i, line in enumerate(lines) if line.rstrip('\n') == END)
    assert begin < end
    body = lines[begin + 1:end]
    assert all(line.startswith(PREFIX) for line in body)
    return ''.join(line[len(PREFIX):] for line in body)


def edit_proof_via_view(proof_path, rust, expected_hash, view_line, start16, end16, replacement):
    proof = proof_path.read_text()
    if digest(proof) != expected_hash:
        return {'accepted': False, 'reason': 'stale canonical proof hash',
                'current_proof_sha256': digest(proof)}
    view, source_map = render(rust, proof)
    by_view = {m['view_line_0']: m for m in source_map['mappings']}
    if view_line not in by_view:
        return {'accepted': False, 'reason': 'generated or Rust scaffolding is read-only',
                'current_proof_sha256': digest(proof)}
    mapping = by_view[view_line]
    line_number = mapping['proof_line_0']
    lines = proof.splitlines(keepends=True)
    line = lines[line_number]
    newline = '\n' if line.endswith('\n') else ''
    body = line[:-1] if newline else line
    prefix = mapping['view_prefix_utf16']
    try:
        start = index_from_unit16(body, start16 - prefix)
        end = index_from_unit16(body, end16 - prefix)
    except ValueError as exc:
        return {'accepted': False, 'reason': str(exc), 'current_proof_sha256': digest(proof)}
    if start > end:
        return {'accepted': False, 'reason': 'reversed range', 'current_proof_sha256': digest(proof)}
    old = body[start:end]
    byte_start = len(''.join(lines[:line_number]).encode()) + len(body[:start].encode())
    byte_end = byte_start + len(old.encode())
    lines[line_number] = body[:start] + replacement + body[end:] + newline
    updated = ''.join(lines)
    proof_path.write_text(updated)
    after_view, after_map = render(rust, updated)
    assert parse_view(after_view) == updated
    return {'accepted': True, 'old_text': old, 'replacement': replacement,
            'proof_line_0': line_number, 'view_line_0': view_line,
            'view_range_utf16': [start16, end16],
            'proof_range_utf16': [start16 - prefix, end16 - prefix],
            'proof_byte_range': [byte_start, byte_end],
            'before_proof_sha256': expected_hash, 'after_proof_sha256': digest(updated),
            'after_view_sha256': digest(after_view), 'after_map': after_map}


def model_from_rust(rust):
    match = re.fullmatch(r'pub fn model_add\(x: u32\) -> u32 \{ x \+ (\d+) \}\n', rust)
    if not match:
        raise ValueError('synthetic Rust subset did not match')
    return f'def modelAdd (x : Nat) : Nat := x + {int(match.group(1))}\n'


def batch(lean, root):
    env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(root))
    model = model_from_rust((root / 'RustSource.rs').read_text())
    (root / 'Model.lean').write_text(model)
    compile_model = run([lean, '--json', '-o', 'Model.olean', 'Model.lean'], root, env)
    assert compile_model['exit'] == 0, compile_model
    proof = run([lean, '--json', 'Proof.lean'], root, env)
    diagnostics = []
    for line in proof['stdout'].splitlines():
        try:
            diagnostics.append(json.loads(line))
        except ValueError:
            diagnostics.append({'unparsed': line})
    return {'model_source_sha256': digest(root / 'Model.lean'),
            'model_olean_sha256': digest(root / 'Model.olean'),
            'proof_source_sha256': digest(root / 'Proof.lean'),
            'compile_model': compile_model, 'proof': proof, 'diagnostics': diagnostics}


def diagnostic_view_spans(diagnostics, source_map):
    by_proof = {m['proof_line_0']: m for m in source_map['mappings']}
    result = []
    for diagnostic in diagnostics:
        pos = diagnostic.get('pos')
        if not isinstance(pos, dict) or 'line' not in pos:
            continue
        proof_line = int(pos['line']) - 1
        mapping = by_proof.get(proof_line)
        result.append({'proof_position_raw': pos, 'proof_line_0': proof_line,
                       'view_line_0': mapping['view_line_0'] if mapping else None,
                       'view_column_if_ascii': int(pos.get('column', 0)) + unit16(PREFIX) if mapping else None,
                       'message': diagnostic.get('data', diagnostic.get('message'))})
    return result


def rust_check(rustc, root):
    return run([rustc, '--crate-type', 'lib', '--edition=2021',
                '-o', 'hostview.rlib', 'HostView.rs'], root)


def materialize_view(root):
    rust = (root / 'RustSource.rs').read_text()
    proof = (root / 'Proof.lean').read_text()
    view, mapping = render(rust, proof)
    (root / 'HostView.rs').write_text(view)
    (root / 'source-map.json').write_text(json.dumps(mapping, indent=2, ensure_ascii=False) + '\n')
    assert parse_view(view) == proof
    return view, mapping


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--rustc', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    a = parser.parse_args()
    if a.work.exists():
        raise SystemExit('work path must be absent')
    a.work.mkdir(parents=True)
    a.out.mkdir(parents=True, exist_ok=True)
    df = run(['/bin/df', '-P', str(a.work)], a.work)
    pressure = run(['/usr/bin/memory_pressure', '-Q'], a.work)
    assert df['exit'] == pressure['exit'] == 0
    block_bytes = 512 if '512-blocks' in df['stdout'].splitlines()[0] else 1024
    assert int(df['stdout'].splitlines()[1].split()[3]) * block_bytes > 5 * (1 << 30)
    free = re.search(r'System-wide memory free percentage: (\d+)%', pressure['stdout'])
    assert free and int(free.group(1)) >= 30
    (a.work / 'RustSource.rs').write_text(RUST_1)
    (a.work / 'Proof.lean').write_text(PROOF_1)
    result = {'lean_sha256': digest(a.lean), 'rustc_version': run([a.rustc, '--version'], a.work),
              'preflight': {'df': df, 'memory_pressure': pressure, 'free_percent': int(free.group(1)),
                            'df_block_bytes': block_bytes},
              'steps': {}, 'decisions': []}
    artifacts = a.out / 'artifacts'
    artifacts.mkdir(exist_ok=True)

    view, mapping = materialize_view(a.work)
    initial_rust = rust_check(a.rustc, a.work)
    initial_batch = batch(a.lean, a.work)
    assert initial_rust['exit'] == initial_batch['proof']['exit'] == 0
    result['steps']['initial'] = {'rust_compile': initial_rust, 'batch': initial_batch,
                                  'proof_sha256': digest(a.work / 'Proof.lean'),
                                  'view_sha256': digest(view), 'roundtrip_exact': parse_view(view) == PROOF_1,
                                  'map': mapping}
    for name in ('RustSource.rs', 'Proof.lean', 'HostView.rs', 'Model.lean', 'source-map.json'):
        shutil.copyfile(a.work / name, artifacts / ('initial-' + name))

    # An astral emoji before beta makes this edit sensitive to UTF-16, not Python indexes.
    comment = PROOF_1.splitlines()[2]
    beta_index = comment.index('β')
    comment_map = mapping['mappings'][2]
    expected = digest(a.work / 'Proof.lean')
    unicode_edit = edit_proof_via_view(a.work / 'Proof.lean', RUST_1, expected,
        comment_map['view_line_0'], unit16(PREFIX + comment[:beta_index]),
        unit16(PREFIX + comment[:beta_index + 1]), 'λ')
    assert unicode_edit['accepted'] and unicode_edit['old_text'] == 'β'
    view, mapping = materialize_view(a.work)
    assert '🦀 λ' in view
    unicode_rust = rust_check(a.rustc, a.work)
    unicode_batch = batch(a.lean, a.work)
    assert unicode_rust['exit'] == unicode_batch['proof']['exit'] == 0
    result['steps']['unicode_view_edit'] = {'edit': unicode_edit, 'rust_compile': unicode_rust,
                                            'batch': unicode_batch, 'roundtrip_exact': parse_view(view) == (a.work / 'Proof.lean').read_text()}

    # Edit a tactic through its Rust-hosted projected range, then round-trip.
    proof = (a.work / 'Proof.lean').read_text()
    tactic_line = proof.splitlines()[4]
    tactic_map = mapping['mappings'][4]
    rfl = tactic_line.index('rfl')
    tactic_edit = edit_proof_via_view(a.work / 'Proof.lean', RUST_1, digest(proof),
        tactic_map['view_line_0'], unit16(PREFIX + tactic_line[:rfl]),
        unit16(PREFIX + tactic_line[:rfl + 3]), 'decide')
    assert tactic_edit['accepted'] and tactic_edit['old_text'] == 'rfl'
    view, mapping = materialize_view(a.work)
    tactic_batch = batch(a.lean, a.work)
    assert tactic_batch['proof']['exit'] == 0 and parse_view(view) == (a.work / 'Proof.lean').read_text()
    result['steps']['tactic_view_edit'] = {'edit': tactic_edit, 'batch': tactic_batch,
                                          'rust_compile': rust_check(a.rustc, a.work)}

    # A direct canonical Lean edit must replace the projected view; stale view CAS fails.
    stale_hash = digest(a.work / 'Proof.lean')
    canonical = (a.work / 'Proof.lean').read_text().replace('  decide\n', '  rfl\n')
    (a.work / 'Proof.lean').write_text(canonical)
    new_view, new_map = materialize_view(a.work)
    stale = edit_proof_via_view(a.work / 'Proof.lean', RUST_1, stale_hash,
                                tactic_map['view_line_0'], 0, 0, 'BAD')
    assert not stale['accepted'] and stale['reason'] == 'stale canonical proof hash'
    scaffold = edit_proof_via_view(a.work / 'Proof.lean', RUST_1, digest(canonical),
                                   0, 0, 0, 'BAD')
    assert not scaffold['accepted'] and 'scaffolding' in scaffold['reason']
    assert digest(a.work / 'Proof.lean') == digest(canonical)
    result['steps']['direct_canonical_and_rejected_edits'] = {
        'direct_proof_sha256': digest(canonical), 'rendered_view_sha256': digest(new_view),
        'roundtrip_exact': parse_view(new_view) == canonical, 'stale_result': stale,
        'scaffold_result': scaffold, 'map': new_map}

    # Bad proof edit via hosted view: compiler error remains owned by canonical Lean.
    theorem = canonical.splitlines()[3]
    rhs = theorem.index('= 2') + 2
    theorem_map = new_map['mappings'][3]
    wrong = edit_proof_via_view(a.work / 'Proof.lean', RUST_1, digest(canonical),
        theorem_map['view_line_0'], unit16(PREFIX + theorem[:rhs]),
        unit16(PREFIX + theorem[:rhs + 1]), '3')
    assert wrong['accepted'] and wrong['old_text'] == '2'
    wrong_view, wrong_map = materialize_view(a.work)
    bad_batch = batch(a.lean, a.work)
    assert bad_batch['proof']['exit'] != 0 and bad_batch['diagnostics']
    result['steps']['wrong_proof'] = {'edit': wrong, 'batch': bad_batch,
        'view_sha256': digest(wrong_view),
        'attributed_diagnostics': diagnostic_view_spans(bad_batch['diagnostics'], wrong_map)}
    for name in ('Proof.lean', 'HostView.rs', 'source-map.json'):
        shutil.copyfile(a.work / name, artifacts / ('wrong-proof-' + name))

    # Repair through the view. Then mutate the Rust model alone: proof text is fixed.
    wrong_source = (a.work / 'Proof.lean').read_text()
    theorem = wrong_source.splitlines()[3]
    rhs = theorem.index('= 3') + 2
    repair = edit_proof_via_view(a.work / 'Proof.lean', RUST_1, digest(wrong_source),
        wrong_map['mappings'][3]['view_line_0'], unit16(PREFIX + theorem[:rhs]),
        unit16(PREFIX + theorem[:rhs + 1]), '2')
    assert repair['accepted'] and repair['old_text'] == '3'
    repaired_view, repaired_map = materialize_view(a.work)
    repaired_batch = batch(a.lean, a.work)
    assert repaired_batch['proof']['exit'] == 0
    proof_fixed_hash = digest(a.work / 'Proof.lean')
    result['steps']['repair'] = {'edit': repair, 'batch': repaired_batch,
                                 'view_sha256': digest(repaired_view)}

    rust_2 = RUST_1.replace('x + 1', 'x + 2')
    (a.work / 'RustSource.rs').write_text(rust_2)
    model_view, model_map = materialize_view(a.work)
    changed_rust_compile = rust_check(a.rustc, a.work)
    assert changed_rust_compile['exit'] == 0
    changed_model = batch(a.lean, a.work)
    assert changed_model['proof']['exit'] != 0 and digest(a.work / 'Proof.lean') == proof_fixed_hash
    result['steps']['rust_model_changed'] = {'rust_source_sha256': digest(rust_2),
        'proof_unchanged_sha256': proof_fixed_hash, 'batch': changed_model,
        'rust_compile': changed_rust_compile,
        'view_sha256': digest(model_view),
        'attributed_diagnostics': diagnostic_view_spans(changed_model['diagnostics'], model_map)}
    for name in ('RustSource.rs', 'Proof.lean', 'HostView.rs', 'Model.lean'):
        shutil.copyfile(a.work / name, artifacts / ('changed-model-' + name))

    # Generated model bytes are derivative; an unauthorized direct edit is erased.
    (a.work / 'RustSource.rs').write_text(RUST_1)
    recovered_view, recovered_map = materialize_view(a.work)
    (a.work / 'Model.lean').write_text('def modelAdd (x : Nat) : Nat := x + 99\n')
    tampered_hash = digest(a.work / 'Model.lean')
    recovered = batch(a.lean, a.work)
    assert recovered['proof']['exit'] == 0
    assert recovered['model_source_sha256'] != tampered_hash
    assert recovered['model_source_sha256'] == initial_batch['model_source_sha256']
    assert digest(a.work / 'Proof.lean') == proof_fixed_hash
    result['steps']['derivative_regeneration'] = {
        'tampered_model_sha256': tampered_hash, 'restored_model_sha256': recovered['model_source_sha256'],
        'proof_unchanged_sha256': proof_fixed_hash, 'batch': recovered,
        'view_sha256': digest(recovered_view), 'roundtrip_exact': parse_view(recovered_view) == (a.work / 'Proof.lean').read_text(),
        'map': recovered_map}
    for name in ('RustSource.rs', 'Proof.lean', 'HostView.rs', 'Model.lean', 'source-map.json'):
        shutil.copyfile(a.work / name, artifacts / ('final-' + name))
    result['decisions'] = [
        {'surface': 'RustSource.rs', 'authority': 'Rust function semantics; generates Model.lean'},
        {'surface': 'Proof.lean', 'authority': 'Lean proof text; Rust-hosted view edits CAS into it'},
        {'surface': 'HostView.rs', 'authority': 'generated projection, never independently authoritative'},
        {'surface': 'Model.lean', 'authority': 'generated derivative, regenerated from RustSource.rs'}]
    (a.out / 'results.json').write_text(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True) + '\n')
    print(json.dumps({'steps': list(result['steps']), 'initial_pass': initial_batch['proof']['exit'] == 0,
                      'wrong_proof_fails': bad_batch['proof']['exit'] != 0,
                      'model_change_fails': changed_model['proof']['exit'] != 0,
                      'recovered_pass': recovered['proof']['exit'] == 0}))


if __name__ == '__main__':
    main()
