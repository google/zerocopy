#!/usr/bin/env python3
"""Bounded Lean 4.30.0-rc2 plugin cwd/realpath alias probe; cached inputs only."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PRIOR = HERE.parent.parent / 'anneal-3730-plugin-reversal-worker-order-2026-09-29' / 'support'
SOURCE = HERE.parent.parent / 'anneal-3730-lake-plugin-artifact-identity-v4-30-0-rc2' / 'support/work/seed-v1'
BIN = None
PINNED_LEAN_SHA256 = 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
NAME = 'plugin__probe_Plugin.dylib'
spec = importlib.util.spec_from_file_location('prior_plugin_probe', PRIOR / 'probe.py')
prior = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prior)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

class Server(prior.Server):
    def __init__(self, label, root, cwd):
        self.label = label
        self.root = root
        self.buf = b''
        self.n = 10
        env = dict(os.environ, LEAN_NUM_THREADS='1',
                   LEAN_PATH=str(root / '.lake/build/lib/lean'),
                   PLUGIN_MARKER=str(root / 'marker.txt'))
        self.p = subprocess.Popen([str(BIN), '--plugin=' + NAME, '--server'], cwd=cwd,
                                  env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, bufsize=0)
        prior.ev('server_start', label=label, pid=self.p.pid, cwd=str(cwd),
                 arg=NAME, resolved=str((cwd / NAME).resolve()),
                 resolved_sha256=sha((cwd / NAME).resolve()))
        self.send(dict(jsonrpc='2.0', id=1, method='initialize', params=dict(
            processId=os.getpid(), rootUri=root.as_uri(), capabilities={},
            initializationOptions={'hasWidgets': False})))
        self.until(1, 20)
        self.send(dict(jsonrpc='2.0', method='initialized', params={}))

def phase(server, label, name, cwd):
    response = server.open(name)
    marker = server.root / 'marker.txt'
    prior.ev('phase', label=label, file=name, cwd=str(cwd),
             resolved=str((cwd / NAME).resolve()),
             resolved_sha256=sha((cwd / NAME).resolve()),
             marker=marker.read_text() if marker.exists() else None,
             wait=response['wait'], goal=response['goal'])
    assert 'error' not in response['wait'] and 'error' not in response['goal']

def cli(label, cwd, env, expected_success):
    marker = Path(env['PLUGIN_MARKER'])
    marker.unlink(missing_ok=True)
    result = subprocess.run([str(BIN), '--plugin=' + NAME, '--version'], cwd=cwd,
                            env=env, text=True, capture_output=True, timeout=20)
    prior.ev('cli', label=label, cwd=str(cwd), lean_path=env['LEAN_PATH'],
             exit=result.returncode, stdout=result.stdout, stderr=result.stderr,
             resolved=str((cwd / NAME).resolve()) if (cwd / NAME).exists() else None,
             marker=marker.read_text() if marker.exists() else None)
    assert (result.returncode == 0) == expected_success

def main():
    global BIN
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean', required=True, type=Path, help='pinned Lean executable')
    ap.add_argument('--work', required=True, type=Path, help='absent scratch directory')
    args = ap.parse_args()
    BIN = args.lean.resolve(strict=True)
    work = args.work.absolute()
    if work.exists():
        raise SystemExit('--work must be absent; no existing data will be removed')
    assert sha(BIN) == PINNED_LEAN_SHA256
    assert SOURCE.is_dir() and PRIOR.is_dir()
    assert shutil.disk_usage(work.parent).free >= 10 * 1024**3
    pressure = subprocess.run(['memory_pressure', '-Q'], text=True, capture_output=True, timeout=5)
    match = re.search(r'System-wide memory free percentage: (\d+)%', pressure.stdout)
    assert match and int(match.group(1)) >= 25, pressure.stdout
    live = work / 'live'
    shutil.copytree(SOURCE, live)
    for name in ['P0.lean', 'P1.lean', 'P2.lean']:
        (live / name).write_bytes((live / 'Proof.lean').read_bytes())
    (live / 'marker.txt').unlink(missing_ok=True)
    a, b, empty, alias = (work / x for x in ('a', 'b', 'empty', 'alias'))
    for p in (a, b, empty, alias): p.mkdir()
    shutil.copy2(PRIOR / 'artifacts/plugin-v1.dylib', a / NAME)
    shutil.copy2(PRIOR / 'artifacts/plugin-v2.dylib', b / NAME)
    env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(a),
               PLUGIN_MARKER=str(live / 'marker.txt'))
    prior.ev('subject', lean_sha256=sha(BIN), v1_sha256=sha(a / NAME),
             v2_sha256=sha(b / NAME), dep_olean_sha256=sha(live / '.lake/build/lib/lean/Dep.olean'),
             proof_sha256=sha(live / 'Proof.lean'), free_memory_percent=int(match.group(1)),
             free_disk_bytes=shutil.disk_usage(HERE).free)
    cli('lean-path-a-cwd-empty', empty, env, False)
    cli('cwd-a', a, env, True)
    cli('cwd-b', b, env, True)
    (alias / NAME).symlink_to(a / NAME)
    (live / 'marker.txt').unlink(missing_ok=True)
    retained = Server('retained', live, alias)
    try:
        phase(retained, 'alias-a-first-worker', 'P0.lean', alias)
        (alias / NAME).unlink()
        (alias / NAME).symlink_to(b / NAME)
        prior.ev('alias_switch', resolved=str((alias / NAME).resolve()),
                 resolved_sha256=sha((alias / NAME).resolve()))
        phase(retained, 'alias-b-new-worker', 'P1.lean', alias)
        goal = retained.goal('P0.lean')
        prior.ev('old_worker_goal', goal=goal)
        assert 'error' not in goal
    finally:
        retained.stop()
    (live / 'marker.txt').unlink(missing_ok=True)
    fresh = Server('fresh', live, alias)
    try: phase(fresh, 'alias-b-fresh-server', 'P2.lean', alias)
    finally: fresh.stop()
    out = work / 'transcript.json'
    out.write_text(json.dumps(prior.LOG, indent=2) + '\n')
    print(json.dumps([(x['label'], x['marker']) for x in prior.LOG if x['kind'] == 'phase']))

if __name__ == '__main__':
    main()
