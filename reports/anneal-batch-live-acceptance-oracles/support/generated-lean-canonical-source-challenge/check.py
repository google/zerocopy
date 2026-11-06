#!/usr/bin/env python3
"""Offline invariants for synthetic generated-Lean-as-canonical challenge."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).parent
artifacts = root / 'artifacts'
x = json.loads((root / 'results.json').read_text())
s = x['steps']

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def parse_view(path):
    lines = path.read_text().splitlines(keepends=True)
    begin = next(i for i, line in enumerate(lines) if line.rstrip('\n') == '// BEGIN SYNTHETIC LEAN PROOF VIEW')
    end = next(i for i, line in enumerate(lines) if line.rstrip('\n') == '// END SYNTHETIC LEAN PROOF VIEW')
    assert begin < end
    assert all(line.startswith('//| ') for line in lines[begin + 1:end])
    return ''.join(line[4:] for line in lines[begin + 1:end])

assert x['lean_sha256'] == 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
assert x['rustc_version']['exit'] == 0 and 'rustc 1.98.1' in x['rustc_version']['stdout']
assert x['preflight']['free_percent'] >= 30
assert int(x['preflight']['df']['stdout'].splitlines()[1].split()[3]) * x['preflight']['df_block_bytes'] > 5 * (1 << 30)
assert set(s) == {'initial', 'unicode_view_edit', 'tactic_view_edit',
                  'direct_canonical_and_rejected_edits', 'wrong_proof', 'repair',
                  'rust_model_changed', 'derivative_regeneration'}
assert [d['authority'] for d in x['decisions']] == [
    'Rust function semantics; generates Model.lean',
    'Lean proof text; Rust-hosted view edits CAS into it',
    'generated projection, never independently authoritative',
    'generated derivative, regenerated from RustSource.rs']

initial = s['initial']
assert initial['rust_compile']['exit'] == initial['batch']['proof']['exit'] == 0
assert initial['roundtrip_exact']
assert sha(artifacts / 'initial-Proof.lean') == initial['proof_sha256']
assert sha(artifacts / 'initial-HostView.rs') == initial['view_sha256']
assert sha(artifacts / 'initial-Model.lean') == initial['batch']['model_source_sha256']

unicode = s['unicode_view_edit']
assert unicode['edit']['accepted'] and unicode['edit']['old_text'] == 'β'
assert unicode['edit']['replacement'] == 'λ'
assert unicode['edit']['view_range_utf16'] == [23, 24]
assert unicode['edit']['proof_range_utf16'] == [19, 20]
assert unicode['edit']['proof_byte_range'][1] - unicode['edit']['proof_byte_range'][0] == 2
assert unicode['rust_compile']['exit'] == unicode['batch']['proof']['exit'] == 0
assert unicode['roundtrip_exact']

tactic = s['tactic_view_edit']
assert tactic['edit']['accepted'] and tactic['edit']['old_text'] == 'rfl'
assert tactic['edit']['replacement'] == 'decide'
assert tactic['batch']['proof']['exit'] == tactic['rust_compile']['exit'] == 0
direct = s['direct_canonical_and_rejected_edits']
assert direct['roundtrip_exact']
assert not direct['stale_result']['accepted'] and 'stale' in direct['stale_result']['reason']
assert not direct['scaffold_result']['accepted'] and 'scaffolding' in direct['scaffold_result']['reason']
assert direct['stale_result']['current_proof_sha256'] == direct['direct_proof_sha256']

wrong = s['wrong_proof']
assert wrong['edit']['accepted'] and wrong['edit']['old_text'] == '2' and wrong['edit']['replacement'] == '3'
assert wrong['batch']['proof']['exit'] != 0
assert sha(artifacts / 'wrong-proof-Proof.lean') == wrong['batch']['proof_source_sha256']
assert sha(artifacts / 'wrong-proof-HostView.rs') == wrong['view_sha256']
assert wrong['batch']['model_source_sha256'] == initial['batch']['model_source_sha256']
assert wrong['attributed_diagnostics']
assert all(d['proof_line_0'] == 4 and d['view_line_0'] == 8 and d['view_column_if_ascii'] == 6
           for d in wrong['attributed_diagnostics'])
assert all('rfl' in d['message'] for d in wrong['attributed_diagnostics'])

repair = s['repair']
assert repair['edit']['accepted'] and repair['batch']['proof']['exit'] == 0
changed = s['rust_model_changed']
assert changed['rust_compile']['exit'] == 0 and changed['batch']['proof']['exit'] != 0
assert changed['proof_unchanged_sha256'] == repair['batch']['proof_source_sha256']
assert changed['batch']['model_source_sha256'] != repair['batch']['model_source_sha256']
assert changed['batch']['model_olean_sha256'] != repair['batch']['model_olean_sha256']
assert sha(artifacts / 'changed-model-Proof.lean') == changed['proof_unchanged_sha256']
assert sha(artifacts / 'changed-model-Model.lean') == changed['batch']['model_source_sha256']
assert changed['attributed_diagnostics'] and all(d['view_line_0'] == 8 for d in changed['attributed_diagnostics'])

end = s['derivative_regeneration']
assert end['batch']['proof']['exit'] == 0 and end['roundtrip_exact']
assert end['tampered_model_sha256'] != end['restored_model_sha256']
assert end['restored_model_sha256'] == initial['batch']['model_source_sha256']
assert end['proof_unchanged_sha256'] == changed['proof_unchanged_sha256']
assert sha(artifacts / 'final-Proof.lean') == end['proof_unchanged_sha256']
assert sha(artifacts / 'final-Model.lean') == end['restored_model_sha256']
for label in ('initial', 'wrong-proof', 'changed-model', 'final'):
    assert parse_view(artifacts / f'{label}-HostView.rs') == (artifacts / f'{label}-Proof.lean').read_text()
print('PASS: source authority, Unicode UTF-16 range, CAS/rejection, mapped Lean errors, model/proof provenance, exact view round trips')
