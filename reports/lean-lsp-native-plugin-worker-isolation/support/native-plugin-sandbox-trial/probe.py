#!/usr/bin/env python3
"""Bounded, isolated native Lean plugin initializer control on owned scratch."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent
LEAN = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
SANDBOX = Path('/usr/bin/sandbox-exec')
PLUGIN_NAME = 'plugin__probe_Plugin.dylib'
PLUGIN_SHA256 = '3f4a1cb3a67a0027f0c90e819afc20d009ddb921cb7f4c0e0095db074e085aa4'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def limits():
    resource.setrlimit(resource.RLIMIT_CPU, (10, 10))
    resource.setrlimit(resource.RLIMIT_NOFILE, (256, 256))
    resource.setrlimit(resource.RLIMIT_FSIZE, (16 * 1024 * 1024, 16 * 1024 * 1024))

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--work', type=Path, required=True, help='new absent owned scratch directory')
    args = parser.parse_args()
    work = args.work.resolve()
    if work.exists():
        raise SystemExit('--work must be absent')
    if not work.parent.is_dir() or shutil.disk_usage(work.parent).free < 2 * (1 << 30):
        raise SystemExit('need an existing parent with at least 2 GiB free')
    if not LEAN.is_file() or not SANDBOX.is_file():
        raise SystemExit('pinned Lean or sandbox-exec missing')
    inputs = HERE / 'inputs'
    assert sha(inputs / PLUGIN_NAME) == PLUGIN_SHA256
    assert (inputs / 'Plugin.lean').read_text() == (
        'import Lean\ninitialize do\n'
        '  let p := (← IO.getEnv "PLUGIN_MARKER").getD ""\n'
        '  if !p.isEmpty then IO.FS.writeFile p "plugin-v1"\n')
    work.mkdir()
    output = {
        'tool_sha256': {'lean': sha(LEAN), 'sandbox_exec': sha(SANDBOX)},
        'input_sha256': {p.name: sha(p) for p in sorted(inputs.iterdir()) if p.is_file()},
        'case_timeout_seconds': 15,
        'resource_limits': {'cpu_seconds': 10, 'nofile': 256, 'file_bytes': 16 * 1024 * 1024},
        'cases': [],
    }
    raw_streams = HERE / 'raw-streams'
    raw_streams.mkdir(exist_ok=True)
    for label, deny_marker, use_plugin in (
        ('plugin-allow', False, True),
        ('plugin-deny', True, True),
        ('plain-deny', True, False),
    ):
        root = work / label
        workspace, outside, home, temp = [root / name for name in ('workspace', 'outside', 'home', 'temp')]
        for path in (workspace, outside, home, temp):
            path.mkdir(parents=True)
        shutil.copy2(inputs / 'Proof.lean', workspace / 'Proof.lean')
        shutil.copy2(inputs / PLUGIN_NAME, workspace / PLUGIN_NAME)
        plugin = workspace / PLUGIN_NAME
        assert sha(plugin) == PLUGIN_SHA256
        marker = outside / 'marker.txt'
        profile = root / 'profile.sb'
        profile.write_text('(version 1)\n(allow default)\n'
                           + (f'(deny file-write* (subpath "{outside}"))\n' if deny_marker else '')
                           + '(deny network*)\n')
        command = [str(SANDBOX), '-f', str(profile), str(LEAN)]
        if use_plugin:
            command.append('--plugin=' + str(plugin))
        command.append('Proof.lean')
        env = {
            'PATH': str(LEAN.parent) + ':/usr/bin:/bin',
            'HOME': str(home), 'TMPDIR': str(temp) + '/',
            'XDG_CACHE_HOME': str(home / 'cache'),
            'LEAN_PATH': str(workspace), 'LEAN_NUM_THREADS': '1',
            'PLUGIN_MARKER': str(marker), 'LANG': 'C',
        }
        started = time.monotonic()
        process = subprocess.Popen(command, cwd=workspace, env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, start_new_session=True,
                                   preexec_fn=limits)
        timed_out = False
        try:
            stdout, stderr = process.communicate(timeout=15)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate(timeout=5)
        (raw_streams / f'{label}.stdout').write_bytes(stdout)
        (raw_streams / f'{label}.stderr').write_bytes(stderr)
        normalize = lambda value: value.replace(str(work), '$WORK').replace(str(LEAN.parent), '$BIN')
        case = {
            'label': label, 'plugin_used': use_plugin, 'marker_write_denied': deny_marker,
            'argv': [normalize(item) for item in command],
            'profile': normalize(profile.read_text()),
            'returncode': process.returncode, 'timed_out': timed_out,
            'process_exited': process.poll() is not None,
            'seconds': round(time.monotonic() - started, 4),
            'stdout': normalize(stdout.decode(errors='replace')),
            'stderr': normalize(stderr.decode(errors='replace')),
            'stdout_raw_sha256': hashlib.sha256(stdout).hexdigest(),
            'stderr_raw_sha256': hashlib.sha256(stderr).hexdigest(),
            'marker_exists': marker.exists(),
            'marker_sha256': sha(marker) if marker.exists() else None,
            'plugin_sha256': sha(plugin),
            'proof_sha256': sha(workspace / 'Proof.lean'),
        }
        output['cases'].append(case)
        assert not timed_out and case['process_exited']
        if label == 'plugin-allow':
            assert process.returncode == 0 and marker.read_text() == 'plugin-v1'
        elif label == 'plugin-deny':
            assert process.returncode != 0 and not marker.exists()
            assert b'operation not permitted' in stderr and str(marker).encode() in stderr
        else:
            assert process.returncode == 0 and not marker.exists()
    (HERE / 'results.json').write_text(json.dumps(output, indent=2, sort_keys=True) + '\n')
    print('PASS: native initializer wrote the owned marker; sandbox denied it; no-plugin control passed')

if __name__ == '__main__':
    main()
