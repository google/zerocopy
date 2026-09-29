#!/usr/bin/env python3
"""Bounded Lake configuration execution and sandbox-denial control."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
BIN = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
LAKE = BIN / 'lake'
LEAN = BIN / 'lean'
SANDBOX = Path('/usr/bin/sandbox-exec')
MARKER_TEXT = 'lake config executed\n'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--work', type=Path, required=True, help='Absent owned work directory')
    args = parser.parse_args()
    work = args.work.resolve()
    if work.exists():
        raise SystemExit('--work must be absent')
    if shutil.disk_usage(work.parent).free < 2 * (1 << 30):
        raise SystemExit('2 GiB free-disk guard')
    if not all(path.is_file() for path in (LAKE, LEAN, SANDBOX)):
        raise SystemExit('pinned Lake/Lean or sandbox-exec missing')
    work.mkdir()
    results = {
        'tool_sha256': {'lake': sha(LAKE), 'lean': sha(LEAN), 'sandbox_exec': sha(SANDBOX)},
        'input_sha256': {p.name: sha(p) for p in sorted((HERE / 'inputs').iterdir()) if p.is_file()},
        'cases': [],
    }
    for label, config, denied in (
        ('dynamic-allow', 'dynamic-lakefile.lean', False),
        ('dynamic-deny', 'dynamic-lakefile.lean', True),
        ('static-deny', 'static-lakefile.lean', True),
    ):
        root = work / label
        workspace = root / 'workspace'
        outside = root / 'outside'
        private_home = root / 'home'
        for path in (workspace, outside, private_home):
            path.mkdir(parents=True)
        shutil.copy2(HERE / 'inputs' / 'Dep.lean', workspace / 'Dep.lean')
        shutil.copy2(HERE / 'inputs' / config, workspace / 'lakefile.lean')
        marker = outside / 'marker.txt'
        profile = root / 'profile.sb'
        if denied:
            profile.write_text(f'(version 1)\n(allow default)\n(deny file-write* (subpath "{outside}"))\n(deny network*)\n')
        command = [str(LAKE), '--keep-toolchain', '--no-cache', 'build', 'Dep']
        if denied:
            command = [str(SANDBOX), '-f', str(profile), *command]
        env = dict(os.environ)
        env.update({
            'ELAN_TOOLCHAIN': 'leanprover/lean4:v4.30.0-rc2',
            'LEAN_NUM_THREADS': '1', 'LAKE_NO_NET': '1',
            'LAKE_ARTIFACT_CACHE': 'false', 'LAKE_CACHE_DIR': '',
            'I126_MARKER_PATH': str(marker), 'HOME': str(private_home),
            'XDG_CACHE_HOME': str(private_home / 'cache'),
            'PATH': str(BIN) + os.pathsep + env.get('PATH', ''),
        })
        assert not marker.exists()
        started = time.monotonic()
        run = subprocess.run(command, cwd=workspace, env=env, capture_output=True,
                             text=True, timeout=30)
        elapsed = round(time.monotonic() - started, 4)
        normalize = lambda value: value.replace(str(work), '$WORK').replace(str(BIN), '$BIN')
        observed = {
            'label': label, 'config': config, 'sandbox_denies_outside_write': denied,
            'argv': [normalize(arg) for arg in command],
            'profile': normalize(profile.read_text()) if denied else None,
            'returncode': run.returncode, 'stdout': normalize(run.stdout),
            'stderr': normalize(run.stderr), 'stdout_sha256': hashlib.sha256(run.stdout.encode()).hexdigest(),
            'stderr_sha256': hashlib.sha256(run.stderr.encode()).hexdigest(),
            'seconds': elapsed, 'marker_exists': marker.exists(),
            'marker_sha256': sha(marker) if marker.exists() else None,
            'source_sha256': sha(workspace / 'Dep.lean'),
            'config_sha256': sha(workspace / 'lakefile.lean'),
        }
        results['cases'].append(observed)
        if label == 'dynamic-allow':
            assert run.returncode == 0 and marker.read_text() == MARKER_TEXT
        elif label == 'dynamic-deny':
            assert run.returncode != 0 and not marker.exists()
            assert 'operation not permitted' in run.stderr and str(marker) in run.stderr
        else:
            assert run.returncode == 0 and not marker.exists()
    (HERE / 'results.json').write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
    print('PASS: Lake config wrote an owned outside marker; sandbox blocked it; static config built')

if __name__ == '__main__':
    main()
