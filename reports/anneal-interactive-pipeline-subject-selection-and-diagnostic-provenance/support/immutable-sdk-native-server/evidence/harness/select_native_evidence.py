#!/usr/bin/env python3
"""Create compact, redacted support evidence for the native SDK report.

Reads existing experiment records only. It never invokes Lean, Lake, or a
compiler. Output is confined to the reference report's evidence/ directory.
Each preserved text file has an original SHA-256 and transformed SHA-256 in
INDEX.json; absolute home paths become declared tokens.
"""

import hashlib
import json
import re
import subprocess
from pathlib import Path

PROJECT = Path('<PROJECT>')
EXPERIMENT = PROJECT / 'Data/20261003-anneal-v1-validation'
HELPER = PROJECT / 'Data/20261003-114500-anneal-reference-reports'
SOURCE = PROJECT / '.worktrees/anneal-v1-cleanup'
OUT = PROJECT / '.worktrees/anneal-sdk-reference-reports/reports/anneal-immutable-sdk-native-server-v4-30-0-rc2/evidence'
TOKENS = {'<PROJECT>': 'the local zerocopy project root',
          '<HOME>': 'the local user home directory'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def redacted(data):
    text = data.decode('utf-8')
    text = text.replace(str(PROJECT), '<PROJECT>')
    text = text.replace('<HOME>', '<HOME>')
    return text.encode('utf-8')


manifest = {'schema': 1, 'redaction_tokens': TOKENS,
            'notes': [
                'Source SHA-256 covers original local bytes before redaction.',
                'Output SHA-256 covers preserved report bytes after redaction or selection.',
                'Original large inventories and LSP/dyld logs are intentionally not copied.',
                'Snapshot equality covers the extracted Aeneas tree and primary SDK view, not the unextracted Lean/Rust archive roots.'
            ], 'files': []}


def save(name, output, sources, transform):
    target = OUT / name
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.is_symlink():
        raise ValueError(f'Refusing symlink output {target}')
    target.write_bytes(output)
    item = {'output': name, 'output_sha256': digest(output),
            'bytes': len(output), 'transformation': transform,
            'sources': []}
    for source in sources:
        raw = source.read_bytes()
        item['sources'].append({'path': str(source).replace(str(PROJECT), '<PROJECT>'),
                                'sha256': digest(raw), 'bytes': len(raw)})
    manifest['files'].append(item)


def preserve(name, source):
    save(name, redacted(source.read_bytes()), [source],
         'UTF-8 text; replace project and home prefixes with declared tokens')


def json_bytes(obj):
    return (json.dumps(obj, indent=2, ensure_ascii=False, sort_keys=True) + '\n').encode()


def snapshot_pair(before_name, after_name, root_scope):
    before = EXPERIMENT / before_name
    after = EXPERIMENT / after_name
    a, b = before.read_bytes(), after.read_bytes()
    rows_a, rows_b = json.loads(a), json.loads(b)
    fields = sorted(set().union(*(row.keys() for row in rows_a)))
    return {'scope': root_scope, 'before': before_name, 'after': after_name,
            'entry_count_before': len(rows_a), 'entry_count_after': len(rows_b),
            'raw_sha256_before': digest(a), 'raw_sha256_after': digest(b),
            'byte_equal': a == b, 'parsed_equal': rows_a == rows_b,
            'entry_fields': fields}


def run_summary(label, runs, cells):
    row = runs[label]
    samples = row.get('samples', [])
    cell = cells.get(label)
    return {'label': label, 'command': row.get('cmd'), 'exit': row.get('exit'),
            'abort': row.get('abort'), 'elapsed_s': row.get('elapsed_s'),
            'peak_sampled_rss_mib': round(max((s['rss_kib'] for s in samples), default=0)/1024, 1),
            'min_host_free_pct': min((s['memory_free_pct'] for s in samples
                                      if s['memory_free_pct'] is not None), default=None),
            'min_disk_free_gib': round(min((s['disk_free_bytes'] for s in samples), default=0)/1024**3, 2),
            'blocked_shared_attempts': len(cell['shared_attempts']) if cell else None,
            'network_attempts': len(cell['network_attempts']) if cell else None}


def lsp_summary(label):
    result_path = EXPERIMENT / 'records' / (label + '.lsp.result.json')
    messages_path = EXPERIMENT / 'records' / (label + '.lsp.messages.jsonl')
    events_path = EXPERIMENT / 'records' / (label + '.lsp.events.jsonl')
    result = json.loads(result_path.read_text())
    messages = [json.loads(x) for x in messages_path.read_text().splitlines()]
    events = [json.loads(x) for x in events_path.read_text().splitlines()]
    by_id = {str(m['id']): m for m in messages if 'id' in m and 'method' not in m}
    diagnostics = {}
    for message in messages:
        if message.get('method') == 'textDocument/publishDiagnostics':
            p = message['params']
            if p.get('uri') == Path(result['source']).as_uri():
                diagnostics[str(p.get('version'))] = p.get('diagnostics', [])
    selected = {key: by_id[key].get('result', by_id[key].get('error'))
                for key in ('1', '2', '3', '4', '5', '6', '7', '8', '9') if key in by_id}
    return {'label': label, 'result': result.get('result'), 'exit': result.get('exit'),
            'abort': result.get('abort'), 'elapsed_s': result.get('elapsed_s'),
            'peak_sampled_rss_mib': result.get('peak_sampled_rss_mib'),
            'min_memory_free_pct': result.get('min_memory_free_pct'),
            'min_disk_free_gib': result.get('min_disk_free_gib'),
            'goal_position': result.get('goal_position'), 'goal': result.get('goal'),
            'restored_goal': result.get('restored_goal'),
            'false_edit_error_count': result.get('false_edit_error_count'),
            'definitions': result.get('definitions'),
            'responses': selected, 'last_diagnostics_by_version': diagnostics,
            'trace': {'process_loads': sum(e['kind']=='load' for e in events),
                      'blocked_shared_mutations': sum(e['kind']=='mutation' and e.get('blocked') for e in events),
                      'network_attempts': sum(e['kind']=='network' for e in events)}}


OUT.mkdir(parents=True, exist_ok=True)

# Full small source inputs and test harnesses. These are data, not instructions.
full_files = {
    'fixture/expected-aeneas.stdout': SOURCE/'anneal/v1/tests/fixtures/expand_output/expected-aeneas.stdout',
    'fixture/expected-anneal.stdout': SOURCE/'anneal/v1/tests/fixtures/expand_output/expected-anneal.stdout',
    'fixture/NativeSmoke.lean': EXPERIMENT/'work/native-lsp-navigation/NativeSmoke.lean',
    'fixture/V1-Specs.lean': EXPERIMENT/'work/native-lake-v1/generated/ExpandOutputExpandOutput1d49e11e5683007f/Specs.lean',
    'fixture/V1-lakefile.lean': EXPERIMENT/'work/native-lake-v1/lakefile.lean',
    'fixture/V1-SdkIdentity.lean': EXPERIMENT/'work/native-lake-v1/anneal/SdkIdentity.lean',
    'fixture/V1-Config.lean': EXPERIMENT/'work/native-lake-v1/anneal/Config.lean',
    'fixture/V1-Anneal.lean': EXPERIMENT/'work/native-lake-v1/anneal/Anneal.lean',
    'fixture/V1-Types.lean': EXPERIMENT/'work/native-lake-v1/generated/ExpandOutputExpandOutput1d49e11e5683007f/Types.lean',
    'fixture/V1-Funs.lean': EXPERIMENT/'work/native-lake-v1/generated/ExpandOutputExpandOutput1d49e11e5683007f/Funs.lean',
    'fixture/V1-Generated.lean': EXPERIMENT/'work/native-lake-v1/generated/Generated.lean',
    'fixture/V1-Audit.lean': EXPERIMENT/'work/native-lake-v1/Audit.lean',
    'fixture/V1-FalseProof.lean': EXPERIMENT/'work/native-lake-v1/FalseProof.lean',
    'fixture/V1-SorryProof.lean': EXPERIMENT/'work/native-lake-v1/SorryProof.lean',
    'environment/real-sdk-lsp-navigation-env.json': EXPERIMENT/'real-sdk-lsp-navigation-env.json',
    'coherent-sdk-results.jsonl': EXPERIMENT/'coherent-sdk-results.jsonl',
    'harness/guard.py': EXPERIMENT/'guard.py',
    'harness/trace.c': EXPERIMENT/'trace.c',
    'harness/lsp_driver.py': EXPERIMENT/'lsp_driver.py',
    'harness/native_lake.py': EXPERIMENT/'native_lake.py',
    'harness/native_lake_followups.py': EXPERIMENT/'native_lake_followups.py',
    'harness/real_sdk_lake.py': EXPERIMENT/'real_sdk_lake.py',
    'harness/sdk_missing_probe.py': EXPERIMENT/'sdk_missing_probe.py',
    'harness/coherent_sdk_probe.py': EXPERIMENT/'coherent_sdk_probe.py',
    'harness/probes.py': EXPERIMENT/'probes.py',
    'harness/check_final.py': EXPERIMENT/'check_final.py',
    'harness/select_native_evidence.py': HELPER/'select_native_evidence.py',
    'manifest/upstream-aeneas-git-manifest.json': HELPER/'upstream-aeneas-manifest.json',
    'manifest/bundled-aeneas-path-manifest.json': EXPERIMENT/'bundle/aeneas/backends/lean/lake-manifest.json',
    'manifest/bundled-mathlib-path-manifest.json': EXPERIMENT/'bundle/aeneas/packages/mathlib/lake-manifest.json',
}
for name, source in full_files.items():
    preserve(name, source)
preserve('source/producer-primer-blame.txt', HELPER/'producer-primer-blame.txt')

flake = SOURCE/'anneal/flake.nix'
cargo = SOURCE/'anneal/v1/Cargo.toml'
def source_lines(path, ranges):
    lines = path.read_text().splitlines()
    return '\n'.join(f'{i}: {lines[i-1]}' for start, end in ranges
                     for i in range(start, end+1)) + '\n'
save('source/producer-primer-and-gate.txt',
     redacted(source_lines(flake, [(449,474),(612,618)]).encode()), [flake],
     'Select current flake.nix lines 449-474 and 612-618 with line numbers, then redact paths')
save('source/v1-cargo-pins.txt',
     redacted(source_lines(cargo, [(23,40),(100,110)]).encode()), [cargo],
     'Select V1 Cargo.toml archive and source pins with line numbers, then redact paths')

entries_path = EXPERIMENT/'bundle-entries.jsonl'
config_entries = [json.loads(line) for line in entries_path.read_text().splitlines()
                  if line.startswith('{"path": "aeneas/backends/lean/.lake/config/')]
config_paths = [row['path'] for row in config_entries]
assert any('/[anonymous]/lakefile.olean' in path for path in config_paths)
assert not any('/aeneas/lakefile.olean' in path for path in config_paths)
save('producer-gap.json', json_bytes({
    'bundle_release_published_utc': '2026-06-07T02:41:58Z',
    'primer_commit': '64bd6d6f1142022eb9297e880214ceb2d87ef72a',
    'primer_commit_url': 'https://github.com/google/zerocopy/commit/64bd6d6f1142022eb9297e880214ceb2d87ef72a',
    'primer_commit_date_utc': '2026-06-16',
    'bundled_backend_config_entries': config_entries,
    'aeneas_dependency_config_olean_present': False,
    'basis': 'tar entry inventory plus current flake.nix primer/gate and Git blame'},
    ), [entries_path, flake],
    'Select backend config tar entries and annotate source chronology; no archive bytes copied')

upstream = HELPER/'upstream-aeneas-manifest.json'
upstream_manifest = json.loads(upstream.read_text())
bundled_manifest_path = EXPERIMENT/'bundle/aeneas/backends/lean/lake-manifest.json'
bundled_manifest = json.loads(bundled_manifest_path.read_text())
assert [p['name'] for p in upstream_manifest['packages']] == [p['name'] for p in bundled_manifest['packages']]
aeneas_source = EXPERIMENT/'bundle/aeneas/backends/lean/AeneasMeta/Saturate/Tactic.lean'
mathlib_source = EXPERIMENT/'bundle/aeneas/packages/mathlib/Mathlib/Data/Nat/Basic.lean'
assert digest(aeneas_source.read_bytes()) == '2be40f83847d5439769e24b03f89df3fb4b8c5878d9e819d817847e3c3f4c7f8'
assert digest(mathlib_source.read_bytes()) == '37e27d3f660143df6b8cca8e02dbb0cfac4302a7cd64e8cbfb108a1a9e32fc0e'
bundle_inventory_path = EXPERIMENT/'bundle-inventory.json'
bundle_inventory = json.loads(bundle_inventory_path.read_text())
identity = {
    'platform': 'macos-aarch64',
    'archive': {'url': 'https://github.com/google/zerocopy/releases/download/anneal-toolchains-v0.1.0-alpha.24-27079750833-09497849a10d/anneal-toolchain-macos-aarch64.tar.zst',
                'sha256': bundle_inventory['sha256'], 'compressed_bytes': bundle_inventory['compressed_bytes']},
    'source_worktree_commit': '79a357870ee0f5a403cf7c7dd43055c0eddbeda2',
    'bundled_lean': {'version': 'v4.30.0-rc2',
                     'commit': '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc'},
    'aeneas_release': {'tag': 'nightly-2026.06.03',
                       'commit': 'ac9f1bc5262a5e4ff1e24ca78617121382202727',
                       'source_manifest_url': 'https://raw.githubusercontent.com/AeneasVerif/aeneas/ac9f1bc5262a5e4ff1e24ca78617121382202727/backends/lean/lake-manifest.json'},
    'upstream_package_revisions': [{'name': p['name'], 'url': p['url'], 'revision': p['rev']}
                                   for p in upstream_manifest['packages']],
    'bundled_path_package_names_match_upstream_manifest': True,
    'sample_source_byte_matches': [
        {'path': 'AeneasMeta/Saturate/Tactic.lean', 'repository': 'AeneasVerif/aeneas',
         'revision': 'ac9f1bc5262a5e4ff1e24ca78617121382202727',
         'sha256': digest(aeneas_source.read_bytes())},
        {'path': 'Mathlib/Data/Nat/Basic.lean', 'repository': 'leanprover-community/mathlib4',
         'revision': '5450b53e5ddc75d46418fabb605edbf36bd0beb6',
         'sha256': digest(mathlib_source.read_bytes())}],
    'qualification': 'The path manifest omits Git revisions; matching names plus two matched source files do not prove whole-tree byte identity to the upstream commits.'
}
save('subject-identity.json', json_bytes(identity),
     [bundle_inventory_path, upstream, bundled_manifest_path,
      aeneas_source, mathlib_source, EXPERIMENT/'records/rc2-trace-version.stdout'],
     'Combine release metadata and manifests; verify two selected source hashes against public immutable revisions')

log_labels = [
    'rc2-trace-version', 'pristine-normal', 'pristine-old',
    'native-lake-v1-audit', 'native-lake-v1-false', 'native-lake-v1-sorry',
    'native-lake-smoke-setup', 'native-lake-smoke-false',
    'sdk-missing-stock-lake', 'sdk-missing-native-stock-lake',
    'native-lake-followup-bad-plugin', 'final-rc2-mismatch',
]
for label in log_labels:
    for ext in ('stdout', 'stderr'):
        source = EXPERIMENT/'records'/(label+'.'+ext)
        if source.is_file() and source.stat().st_size:
            preserve('logs/'+label+'.'+ext, source)

followup_labels = ['native-lake-followup-baseline', 'native-lake-followup-noop',
                   'native-lake-followup-edit', 'native-lake-followup-delete-output']
followup_sources = []
followup_actions = []
for label in followup_labels:
    source = EXPERIMENT/'records'/(label+'.stdout')
    preserve('logs/'+label+'.stdout', source)
    followup_sources.append(source)
    actions = [line for line in source.read_text().splitlines()
               if 'Built Smoke' in line or 'Replayed Smoke' in line or
               'Build completed' in line]
    followup_actions.append({'label': label, 'actions': actions})
save('followup-local-output-actions.json', redacted(json_bytes({
    'cells': followup_actions,
    'scope': 'Lake stdout proves built/replayed action labels. The no-op output mtime/size equality printed by the enclosing controller was not retained in these child logs; do not infer byte identity from this summary alone.'
})), followup_sources,
     'Select local Smoke build/replay/completion lines and state output-identity limit')

noop = EXPERIMENT/'records/native-lake-v1-noop.stdout'
lines = noop.read_text().splitlines()
selected = [line for line in lines if any(token in line for token in
            ('Replayed ', 'Built ', 'Build completed', 'Ran job computation'))]
save('logs/native-lake-v1-noop.selected.txt', redacted(('\n'.join(selected)+'\n').encode()),
     [noop], 'Select Lake replay/build/completion lines, then redact paths')

dyld = EXPERIMENT/'records/native-sdk-lsp-1.lsp.stderr'
lines = dyld.read_text(errors='replace').splitlines()
selected = [f'{i}: {line}' for i, line in enumerate(lines, 1)
            if 'libaeneas_AeneasMeta.dylib' in line]
save('logs/native-plugin-load.selected.txt', redacted(('\n'.join(selected)+'\n').encode()),
     [dyld], 'Select dylib load lines with original line numbers, then redact paths')

before_archive = EXPERIMENT/'archive-pristine-before.json'
after_archive = EXPERIMENT/'archive-final-after.json'
before_sdk = EXPERIMENT/'real-sdk-overlay-before.json'
after_sdk = EXPERIMENT/'sdk-final-after.json'
snapshots = [snapshot_pair(before_archive.name, after_archive.name,
                           'entire extracted bundle/aeneas tree; excludes unextracted Lean and Rust roots'),
             snapshot_pair(before_sdk.name, after_sdk.name,
                           'primary SDK overlay view')]
assert all(x['byte_equal'] and x['parsed_equal'] for x in snapshots)
save('snapshot-equality.json', json_bytes(snapshots),
     [before_archive, after_archive, before_sdk, after_sdk],
     'Compare complete JSON snapshot bytes and parsed rows; retain counts and digests only')

runs_path = EXPERIMENT/'runs.jsonl'
cells_path = EXPERIMENT/'cells.jsonl'
runs = {r['label']: r for r in (json.loads(x) for x in runs_path.read_text().splitlines())}
cells = {r['case']: r for r in (json.loads(x) for x in cells_path.read_text().splitlines())}
success = ['native-lake-smoke-target','native-lake-smoke-build','native-lake-smoke-setup',
 'native-lake-v1-audit','native-lake-v1-setup','native-lake-followup-baseline',
 'native-lake-followup-noop','native-lake-followup-edit','native-lake-followup-delete-output',
 'native-lake-v1-noop','20261003-112910-prefix','20261003-112910-build','20261003-112910-setup']
success += ['native-lake-v1-build-'+s for s in
            ['SdkIdentity','Config','ExpandOutputExpandOutput1d49e11e5683007f.Types',
             'ExpandOutputExpandOutput1d49e11e5683007f.Funs','Anneal','Generated']]
failures = ['native-lake-smoke-false','native-lake-v1-false','native-lake-v1-sorry',
 'native-lake-followup-bad-plugin','sdk-missing-stock-lake',
 'sdk-missing-native-stock-lake','final-rc2-mismatch']
assert len(success)+len(failures) == 26
for label in success:
    assert runs[label]['exit'] == 0 and runs[label]['abort'] is None
for label in failures:
    assert runs[label]['exit'] == 1 and runs[label]['abort'] is None
outcomes = {'expected_successes': [run_summary(x,runs,cells) for x in success],
            'expected_failures': [run_summary(x,runs,cells) for x in failures]}
save('selected-outcomes.json', redacted(json_bytes(outcomes)), [runs_path, cells_path],
     'Select 26 checked labels from check_final.py; summarize status and sampled resources')

lsp_sources = []
lsp = []
for label in ('native-sdk-lsp-1', 'native-sdk-lsp-navigation-1'):
    lsp.append(lsp_summary(label))
    for suffix in ('.lsp.result.json','.lsp.messages.jsonl','.lsp.events.jsonl'):
        lsp_sources.append(EXPERIMENT/'records'/(label+suffix))
save('lsp-selected.json', redacted(json_bytes(lsp)), lsp_sources,
     'Select handshake/goal/definition/edit responses, final diagnostics by version, and tracer counts; omit progress spam')

final_check = EXPERIMENT/'final-check.json'
preserve('final-check.json', final_check)

def du_kib(path):
    result = subprocess.run(['du','-sk',str(path)],check=True,capture_output=True,text=True)
    return int(result.stdout.split()[0])

coherent_view = EXPERIMENT/'coherent-sdk-probe/20261003-112910/view'
primary_view = EXPERIMENT/'sdk-install'
rc2_lake = PROJECT/'.anneal-local-tools/scratch/20260927-reference-experiments/nix_toolchain_relocation/relocated_lean/bin/lake'
launchers = {
    'coherent_lean': coherent_view/'bin/lean',
    'coherent_lake': coherent_view/'bin/lake',
    'primary_sdk_lean': primary_view/'bin/lean',
    'original_rc2_lake': rc2_lake,
}
sizes = {'measurement': 'du -sk filesystem allocation at evidence selection time; KiB means 1024 bytes',
         'directories': {name: {'du_kib': du_kib(path),
                                'relative_to_project': str(path).replace(str(PROJECT),'<PROJECT>')}
                         for name,path in {
                             'v1_workspace': EXPERIMENT/'work/native-lake-v1',
                             'primary_sdk_view': primary_view,
                             'extracted_aeneas': EXPERIMENT/'bundle/aeneas',
                             'final_lean_runtime': EXPERIMENT/'lean-final',
                         }.items()},
         'launchers': {name: {'bytes': path.stat().st_size,
                              'sha256': digest(path.read_bytes()),
                              'relative_to_project': str(path).replace(str(PROJECT),'<PROJECT>')}
                       for name,path in launchers.items()}}
assert sizes['launchers']['coherent_lean']['sha256'] == sizes['launchers']['primary_sdk_lean']['sha256']
assert sizes['launchers']['coherent_lake']['sha256'] == sizes['launchers']['original_rc2_lake']['sha256']
save('size-and-launcher-identity.json', json_bytes(sizes), list(launchers.values()),
     'Read-only du -sk of four directories plus stat/SHA-256 of copied Lean/Lake launchers')

manifest_path = OUT/'INDEX.json'
manifest_path.write_bytes(json_bytes(manifest))
print(json.dumps({'output': str(OUT), 'files': len(manifest['files']),
                  'total_bytes': sum(x['bytes'] for x in manifest['files']),
                  'index_sha256': digest(manifest_path.read_bytes())}))
