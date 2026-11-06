#!/usr/bin/env python3
"""Validate retained direct Lean LSP / polling-build evidence."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
data = json.loads((HERE / 'results.json').read_text())
events = {e['label']: e for e in data['watch_events']}
obs = {e['step']: e for e in data['observations']}
diag = data['diagnostic_versions']

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def consumed(step):
    return obs[step]['consumed']

assert data['lsp_exit']['exit'] == 0
assert diag['v1'] == [] and diag['v3'] == [] and diag['v4'] == [] and diag['v5'] == []
assert len(diag['v2']) == 1 and diag['v2'][0]['severity'] == 1
assert diag['v2'][0]['message'] == 'unsolved goals\nn : Nat\n⊢ n + 0 = n'
assert events['initial']['status']['exit'] == 0
assert events['dirty-buffer-poll']['event'] == 'duplicate_suppressed'
assert obs['dirty_unsaved']['disk_source_sha256'] == events['initial']['source_sha256']
assert consumed('dirty_unsaved') == events['initial']['consumed_after']
assert events['save-invalid']['status']['exit'] == 1
assert 'unsolved goals' in events['save-invalid']['status']['stdout']
assert events['duplicate-save-event']['event'] == 'duplicate_suppressed'
assert consumed('save_invalid') == consumed('dirty_unsaved')
assert events['external-overwrite']['status']['exit'] == 0
assert consumed('external_disk_while_open')['source_sha256'] == obs['external_disk_while_open']['disk_source_sha256']
assert consumed('external_disk_while_open') != consumed('dirty_unsaved')
assert obs['external_disk_while_open']['diagnostics'] == diag['v2']
assert obs['reopen_external']['diagnostics'] == []
assert consumed('reopen_external') == consumed('external_disk_while_open')
assert obs['rustfmt']['rust_before_sha256'] != obs['rustfmt']['rust_after_sha256']
assert obs['rustfmt']['lean_disk_unchanged'] == consumed('external_disk_while_open')['source_sha256']
assert obs['rustfmt']['consumed'] == consumed('external_disk_while_open')
assert events['lean-format-edit']['status']['exit'] == 0
assert obs['lean_format_edit']['diagnostics'] == []
assert events['cancelled-rebuild']['status']['exit'] == -9
assert events['cancelled-rebuild']['consumed_before'] == events['cancelled-rebuild']['consumed_after']
assert events['retry-after-cancel']['status']['exit'] == 0
assert events['retry-after-cancel']['source_sha256'] == events['cancelled-rebuild']['source_sha256']
assert obs['cancel_retry']['consumed_before'] != obs['cancel_retry']['consumed_after']
assert data['final'] == events['retry-after-cancel']['consumed_after']

for name, digest in data['artifact_sha256'].items():
    assert sha(HERE / 'artifacts' / name) == digest, name
assert data['artifact_sha256']['v1-Generated.lean'] == events['initial']['source_sha256']
assert data['artifact_sha256']['v1-Generated.olean'] == events['initial']['consumed_after']['olean_sha256']
assert data['artifact_sha256']['final-Generated.lean'] == data['final']['source_sha256']
assert data['artifact_sha256']['final-Generated.olean'] == data['final']['olean_sha256']
assert data['artifact_sha256']['formatted-Source.rs'] == obs['rustfmt']['rust_after_sha256']

publications = [e['message']['params'] for e in data['lsp_events']
                if e['side'] == 'server' and e['message'].get('method') == 'textDocument/publishDiagnostics']
for version in range(1, 6):
    assert any(p.get('version') == version and p['diagnostics'] == diag[f'v{version}'] for p in publications)
assert len({p['uri'] for p in publications}) == 1
print('PASS: direct LSP versions 1–5, hash-polling events, artifact hashes, failure/cancellation retention')
