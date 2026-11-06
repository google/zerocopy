#!/usr/bin/env python3
"""Pinned, bounded Charon/Aeneas CLI identity and output-manifest probe."""
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
TOOLS = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON = TOOLS / 'bin/charon'
AENEAS = TOOLS / 'bin/aeneas'
RUST_BIN = TOOLS / 'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
REGISTRY = TOOLS / 'sources/aeneas/src/extract/ExtractBuiltinLean.ml'
WORK = HERE / 'work'
INPUTS = HERE / 'inputs'
OUTPUTS = HERE / 'outputs'
RESULTS = HERE / 'results.json'
HANDOFF = HERE / 'handoff-manifest.json'
BASE_FLAGS = ['-backend', 'lean', '-no-progress-bar', '-sequential', '-split-files', '-gen-lib-entry']

BASE = '''#![allow(dead_code)]
#[derive(Clone, Copy)]
pub struct Wrap(pub u32);
pub trait Bump { fn bump(self) -> u32; }
impl Bump for Wrap { fn bump(self) -> u32 { self.0.wrapping_add(1) } }
pub fn step(x: u32) -> u32 { x.wrapping_add(1) }
pub fn use_step(x: u32) -> u32 { step(x) }
pub fn use_bump(x: Wrap) -> u32 { x.bump() }
pub fn even(n: u32) -> bool { if n == 0 { true } else { odd(n - 1) } }
pub fn odd(n: u32) -> bool { if n == 0 { false } else { even(n - 1) } }
'''

SOURCES = {
    'base': BASE,
    'function_body': BASE.replace('x.wrapping_add(1) }\npub fn use_step', 'x.wrapping_add(2) }\npub fn use_step'),
    'type_shape': BASE.replace('pub struct Wrap(pub u32);', 'pub struct Wrap(pub u32, pub u32);'),
    'trait_impl': BASE.replace('self.0.wrapping_add(1)', 'self.0.wrapping_add(3)'),
    'recursive_group': BASE.replace('if n == 0 { true } else { odd(n - 1) }', 'if n <= 1 { true } else { odd(n - 1) }'),
    'helper_insert': BASE.replace('pub fn step(x:', 'pub fn helper(x: u32) -> u32 { x }\npub fn step(x:'),
    'delete_step': BASE.replace('pub fn step(x: u32) -> u32 { x.wrapping_add(1) }\n', '').replace('pub fn use_step(x: u32) -> u32 { step(x) }\n', ''),
}


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def inventory(root):
    return {str(p.relative_to(root)): {'sha256': digest(p), 'bytes': p.stat().st_size}
            for p in sorted(root.rglob('*')) if p.is_file()}


def invoke(argv, env=None, timeout=40):
    t = time.monotonic()
    r = subprocess.run([str(x) for x in argv], cwd=WORK, env=env,
                       text=True, capture_output=True, timeout=timeout)
    return {'argv': [str(x) for x in argv], 'exit': r.returncode,
            'seconds': round(time.monotonic()-t, 5), 'stdout': r.stdout, 'stderr': r.stderr}


def declaration_manifest(dest):
    files = {}
    for p in sorted(dest.rglob('*.lean')):
        lines = p.read_text().splitlines()
        declarations = []
        namespace = []
        origins = []
        for n, line in enumerate(lines, 1):
            s = line.strip()
            if s.startswith('namespace '): namespace.append(s.split(' ', 1)[1])
            if s.startswith('end ') and namespace and s[4:] == namespace[-1]: namespace.pop()
            if s.startswith('/-- [') or s.startswith('/-- Trait implementation: ['):
                origins.append({'line': n, 'text': s})
            match = re.match(r'^\s*(?:def|abbrev|structure|inductive|opaque|theorem|instance|partial def)\s+([^\s(:]+)', line)
            if match:
                declarations.append({'line': n, 'name': '.'.join(namespace+[match.group(1)]),
                                     'head': s, 'origin_comment': origins[-1] if origins else None})
        files[str(p.relative_to(dest))] = {
            **inventory(dest)[str(p.relative_to(dest))],
            'imports': [x.strip() for x in lines if x.lstrip().startswith('import ')],
            'declarations': declarations,
        }
    return files


def llbc_declarations(path):
    data = json.loads(path.read_text())
    t = data['translated']
    def name(parts):
        return '::'.join(x['Ident'][0] if 'Ident' in x else '<impl>' for x in parts)
    rows = []
    for kind in ('type_decls', 'trait_decls', 'trait_impls', 'fun_decls'):
        for item in t[kind]:
            if item is None: continue
            meta = item['item_meta']
            rows.append({'kind': kind, 'id': item['def_id'], 'name': name(meta['name']),
                         'span': meta.get('span'), 'local': meta.get('is_local')})
    return {'charon_version': data['charon_version'], 'crate_name': t['crate_name'],
            'has_errors': data['has_errors'], 'declarations': rows,
            'source_files': [{'id': x['id'], 'name': x['name'], 'contents_sha256':
                              hashlib.sha256(x['contents'].encode()).hexdigest() if x.get('contents') is not None else None}
                             for x in t['files']]}


def translate(label, input_path, flags=BASE_FLAGS, binary=AENEAS, existing=None):
    shutil.copyfile(input_path, WORK/'current.llbc')
    dest = existing or OUTPUTS/label
    dest.mkdir(parents=True, exist_ok=True)
    run = invoke([binary, *flags, '-dest', dest, WORK/'current.llbc'])
    run.update({'label': label, 'input_sha256': digest(input_path), 'flags': flags,
                'binary_sha256': digest(binary), 'inventory': inventory(dest),
                'declaration_manifest': declaration_manifest(dest)})
    return run


def main():
    for p in (WORK, INPUTS, OUTPUTS):
        if p.exists(): shutil.rmtree(p)
        p.mkdir(parents=True)
    env = dict(os.environ)
    env.update({'RUSTUP_HOME': str(TOOLS/'rustup'), 'CARGO_HOME': str(TOOLS/'cargo'),
                'CHARON_TOOLCHAIN_IS_IN_PATH': '1',
                'PATH': os.pathsep.join((str(RUST_BIN), str(TOOLS/'bin'), env.get('PATH','')))})
    extracted = {}
    for label, source in SOURCES.items():
        (INPUTS/f'{label}.rs').write_text(source)
        (WORK/'source.rs').write_text(source)
        raw = invoke([CHARON, 'rustc', '--preset', 'aeneas', '--dest-file', WORK/'extract.llbc',
                      '--', WORK/'source.rs', '--crate-type', 'lib', '--crate-name',
                      'identity_probe', '--edition', '2021'], env)
        assert raw['exit'] == 0, (label, raw)
        shutil.copyfile(WORK/'extract.llbc', INPUTS/f'{label}.llbc')
        extracted[label] = {'charon': raw, 'source_sha256': digest(INPUTS/f'{label}.rs'),
                            'llbc_sha256': digest(INPUTS/f'{label}.llbc'),
                            'llbc_manifest': llbc_declarations(INPUTS/f'{label}.llbc')}
    translations = {label: translate(label, INPUTS/f'{label}.llbc') for label in SOURCES}
    assert all(x['exit'] == 0 for x in translations.values()), {k:v['stderr'] for k,v in translations.items()}
    # Identical bytes, different LLBC locator, and a copied executable.
    shutil.copyfile(AENEAS, WORK/'aeneas-copy')
    (WORK/'aeneas-copy').chmod(0o755)
    copy_without_libs = translate('binary_copy_without_libs', INPUTS/'base.llbc', binary=WORK/'aeneas-copy')
    shutil.copytree(TOOLS/'aeneas-release/libs', WORK/'libs')
    identity_controls = {
        'repeat': translate('repeat', INPUTS/'base.llbc'),
        'binary_copy_with_libs': translate('binary_copy_with_libs', INPUTS/'base.llbc', binary=WORK/'aeneas-copy'),
        'namespace': translate('namespace', INPUTS/'base.llbc', [*BASE_FLAGS, '-namespace', 'Alternate']),
        'unsplit': translate('unsplit', INPUTS/'base.llbc', ['-backend','lean','-no-progress-bar','-sequential']),
        'heartbeat': translate('heartbeat', INPUTS/'base.llbc', [*BASE_FLAGS, '-max-heartbeats','500000']),
        'impl_namespace': translate('impl_namespace', INPUTS/'base.llbc', [*BASE_FLAGS, '-impl-namespace']),
        'tuple_projector': translate('tuple_projector', INPUTS/'base.llbc', [*BASE_FLAGS, '-tuple-nested-proj']),
    }
    # A schema marker revision is separate from the semantically changed Rust inputs.
    d = json.loads((INPUTS/'base.llbc').read_text())
    d['charon_version'] = '0.1.999'
    (INPUTS/'schema_marker.llbc').write_text(json.dumps(d, separators=(',',':')))
    identity_controls['schema_marker'] = translate('schema_marker', INPUTS/'schema_marker.llbc')
    d = json.loads((INPUTS/'base.llbc').read_text())
    d['translated']['short_names'] = []
    (INPUTS/'short_names_cleared.llbc').write_text(json.dumps(d, separators=(',',':')))
    identity_controls['short_names_cleared'] = translate('short_names_cleared', INPUTS/'short_names_cleared.llbc')
    # Existing destination controls: user file, successful shrink, then a failed request.
    shared = OUTPUTS/'shared'
    shared.mkdir()
    user_file = shared/'UserModel.lean'
    user_file.write_text('-- authored sentinel, never owned by Aeneas\ndef userModel : Nat := 17\n')
    prior = translate('shared_base', INPUTS/'base.llbc', existing=shared)
    deletion = translate('shared_delete', INPUTS/'delete_step.llbc', existing=shared)
    # A preserved prior error specimen; replay does not depend on another report.
    unsupported_path = HERE/'fixture'/'unsupported.llbc'
    shutil.copyfile(unsupported_path, INPUTS/'unsupported.llbc')
    failed = translate('shared_unsupported', INPUTS/'unsupported.llbc', existing=shared)
    assert failed['exit'] != 0
    mode_shared = OUTPUTS/'mode_shared'
    mode_first = translate('mode_split_first', INPUTS/'base.llbc', existing=mode_shared)
    mode_second = translate('mode_unsplit_second', INPUTS/'base.llbc',
                            ['-backend','lean','-no-progress-bar','-sequential'], existing=mode_shared)
    mode_stale = sorted(set(mode_second['inventory']) - set(identity_controls['unsplit']['inventory']))
    assert mode_first['exit'] == mode_second['exit'] == 0 and mode_stale == ['Funs.lean', 'Types.lean']
    clean_delete = translations['delete_step']['declaration_manifest']
    stale = sorted(set(deletion['inventory']) - set(translations['delete_step']['inventory']) - {'UserModel.lean'})
    result = {'environment': {'platform': platform.platform(), 'python': sys.version,
               'aeneas_sha256': digest(AENEAS), 'charon_sha256': digest(CHARON),
               'registry_source_sha256': digest(REGISTRY), 'registry_source_path': str(REGISTRY),
               'runtime_libs': inventory(TOOLS/'aeneas-release/libs'),
               'rustc_version': invoke([RUST_BIN/'rustc', '--version'], env)['stdout'].strip(),
               'aeneas_version': invoke([AENEAS, '-version'])['stdout'].strip()},
              'extractions': extracted, 'translations': translations,
              'identity_controls': identity_controls,
              'binary_copy_without_libs': copy_without_libs,
              'shared_controls': {'prior': prior, 'deletion': deletion, 'failed': failed,
                                  'user_file_sha256': digest(user_file),
                                  'stale_paths_after_deletion': stale,
                                  'mode_split_first': mode_first, 'mode_unsplit_second': mode_second,
                                  'stale_paths_after_mode_change': mode_stale,
                                  'clean_delete_manifest': clean_delete},
              'comparisons': {}}
    base_inv = translations['base']['inventory']
    for key, record in {**translations, **identity_controls}.items():
        result['comparisons'][key] = {'same_bytes_as_base': record['inventory'] == base_inv,
            'changed_paths': sorted(p for p in set(base_inv)|set(record['inventory'])
                                    if base_inv.get(p) != record['inventory'].get(p))}
    assert identity_controls['repeat']['inventory'] == base_inv
    assert copy_without_libs['exit'] != 0 and not copy_without_libs['inventory']
    assert identity_controls['binary_copy_with_libs']['inventory'] == base_inv
    assert digest(user_file) == hashlib.sha256(b'-- authored sentinel, never owned by Aeneas\ndef userModel : Nat := 17\n').hexdigest()
    def declarations(record):
        return sorted(x['name'] for f in record['declaration_manifest'].values() for x in f['declarations'])
    result['shared_controls']['removed_declarations_after_deletion'] = sorted(
        set(declarations(translations['base'])) - set(declarations(translations['delete_step'])))
    result['shared_controls']['failed_output_contains_sorry'] = any(
        'sorry' in p.read_text() for p in shared.rglob('*.lean'))
    assert result['shared_controls']['removed_declarations_after_deletion'] == ['identity_probe.step', 'identity_probe.use_step']
    assert result['shared_controls']['failed_output_contains_sorry']
    handoff = {'schema': 'anneal-research-aeneas-output-manifest-v1',
               'provenance_level': 'exact input and emitted bytes; Aeneas comment hints only, no verified Rust-to-Lean declaration map',
               'tool': {'aeneas_binary_sha256': digest(AENEAS),
                        'aeneas_runtime_libraries': result['environment']['runtime_libs'],
                        'charon_binary_sha256': digest(CHARON),
                        'lean_external_registry_source_sha256': digest(REGISTRY)},
               'generations': {k: {'source_sha256': extracted[k]['source_sha256'],
                                    'llbc_sha256': extracted[k]['llbc_sha256'],
                                    'llbc_schema_version': extracted[k]['llbc_manifest']['charon_version'],
                                    'llbc_declarations': extracted[k]['llbc_manifest']['declarations'],
                                    'aeneas_flags': BASE_FLAGS,
                                    'generated_files': translations[k]['declaration_manifest'],
                                    'declarations': declarations(translations[k]),
                                    'anneal_obligations': None,
                                    'proven_mapping_to_rust_items': None}
                               for k in SOURCES},
               'deletion': {'removed_declarations': result['shared_controls']['removed_declarations_after_deletion'],
                            'shared_destination_failed_to_remove_old_paths': stale},
               'mode_change': {'stale_paths_after_unsplit': mode_stale},
               'failed_publication': {'exit': failed['exit'], 'reject_candidate': True,
                                      'partial_generated_files': failed['inventory']}}
    HANDOFF.write_text(json.dumps(handoff, indent=2, sort_keys=True)+'\n')
    RESULTS.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    shutil.rmtree(WORK)
    print(json.dumps({'translations': len(translations), 'option_controls': len(identity_controls),
                      'changed': {k:v['changed_paths'] for k,v in result['comparisons'].items()},
                      'stale_paths': stale, 'failed_exit': failed['exit']}, sort_keys=True))

if __name__ == '__main__': main()
