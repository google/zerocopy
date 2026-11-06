#!/usr/bin/env python3
"""Offline Charon control: two Cargo packages with one exported crate name."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
TOOLS = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RBIN = TOOLS / 'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
RLIB = TOOLS / 'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/lib'
CHARON = TOOLS / 'bin/charon'
CARGO = RBIN / 'cargo'
RUSTC = RBIN / 'rustc'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def projection(path):
    data = json.loads(path.read_text())
    translated = data['translated']
    local = [f for f in translated['fun_decls'] if f and f['item_meta']['is_local']]
    assert len(local) == 1
    statements = local[0]['body']['Structured']['body']['statements']
    literal = statements[0]['kind']['Assign'][1]['Use'][0]['Const']['kind']['Literal']['Scalar']['Unsigned']
    return {
        'charon_version': data['charon_version'],
        'crate_name': translated['crate_name'],
        'has_errors': data['has_errors'],
        'source_name': translated['files'][0]['name']['Local'],
        'source_text': translated['files'][0]['contents'],
        'function_name': [part['Ident'][0] for part in local[0]['item_meta']['name']],
        'literal': literal,
    }

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--work', type=Path, required=True, help='Absent disposable work directory')
    args = parser.parse_args()
    work = args.work.resolve()
    if work.exists():
        raise SystemExit('--work must be absent')
    if shutil.disk_usage(work.parent).free < 2 * (1 << 30):
        raise SystemExit('2 GiB free-disk guard')
    for binary in (CHARON, CARGO, RUSTC):
        if not binary.is_file():
            raise SystemExit(f'missing cached binary: {binary}')
    shutil.copytree(HERE / 'inputs', work)
    env = dict(os.environ)
    env.update({
        'RUSTUP_HOME': str(TOOLS / 'rustup'), 'CARGO_HOME': str(TOOLS / 'cargo'),
        'CARGO_TARGET_DIR': str(work / 'target'), 'CARGO_BUILD_JOBS': '1',
        'CARGO_INCREMENTAL': '0', 'RAYON_NUM_THREADS': '1',
        'CHARON_TOOLCHAIN_IS_IN_PATH': '1',
        'PATH': os.pathsep.join([str(RBIN), str(TOOLS / 'bin'), env.get('PATH', '')]),
        'DYLD_LIBRARY_PATH': os.pathsep.join([
            str(RLIB), str(RLIB / 'rustlib/aarch64-apple-darwin/lib'),
            env.get('DYLD_LIBRARY_PATH', '')]),
    })
    results = {
        'tool_sha256': {'charon': sha(CHARON), 'cargo': sha(CARGO), 'rustc': sha(RUSTC)},
        'input_sha256': {str(path.relative_to(HERE / 'inputs')): sha(path)
                         for path in sorted((HERE / 'inputs').rglob('*')) if path.is_file()},
        'commands': [], 'outputs': {},
    }
    for name, value in (('left', '11'), ('right', '29')):
        dest = HERE / 'artifacts' / f'{name}.llbc'
        command = [CHARON, 'cargo', '--preset', 'aeneas', '--dest-file', dest, '--',
                   '--manifest-path', work / 'Cargo.toml', '--package', f'{name}_package',
                   '--lib', '--offline', '--locked', '-v']
        started = time.monotonic()
        process = subprocess.run([str(x) for x in command], cwd=work, env=env,
                                 capture_output=True, text=True, timeout=30)
        normalize = lambda s: s.replace(str(work), '$WORK').replace(str(TOOLS), '$TOOLS').replace(str(HERE), '$REPORT')
        results['commands'].append({
            'case': name, 'argv': [normalize(str(x)) for x in command],
            'returncode': process.returncode, 'stdout': normalize(process.stdout),
            'stderr': normalize(process.stderr), 'seconds': round(time.monotonic() - started, 4),
        })
        if process.returncode != 0:
            raise RuntimeError(f'{name} Charon failed: {process.stderr[-500:]}')
        results['outputs'][name] = {'sha256': sha(dest), 'bytes': dest.stat().st_size,
                                    'projection': projection(dest)}
        assert results['outputs'][name]['projection']['crate_name'] == 'shared_unit'
        assert results['outputs'][name]['projection']['literal'] == ['U32', value]
    assert results['outputs']['left']['sha256'] != results['outputs']['right']['sha256']
    (HERE / 'results.json').write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
    print('PASS: two successful Charon outputs share a crate/function name but differ in source and body')

if __name__ == '__main__':
    main()
