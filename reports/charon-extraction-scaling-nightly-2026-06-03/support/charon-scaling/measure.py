#!/usr/bin/env python3
"""Bounded single-file Charon measurement; one fresh process per mode."""
import json
import os
import resource
import signal
import subprocess
import sys
import time
from pathlib import Path

mode = sys.argv[1]
scratch = Path('.anneal-local-tools/scratch/charon-scaling')
source = Path('.anneal-local-tools/scratch/translation-goldens/probe.rs')
options = {
    'whole': [],
    'one': ['--start-from', 'crate::choose'],
    'three': [
        '--start-from', 'crate::choose',
        '--start-from', 'crate::bump',
        '--start-from', 'crate::checked_add',
    ],
    'whole_no_serialize': ['--no-serialize'],
}[mode]
cmd = ['charon', 'rustc', '--preset', 'aeneas', *options]
if mode != 'whole_no_serialize':
    cmd += ['--dest-file', str(scratch / f'{mode}.llbc')]
cmd += ['--', str(source), '--crate-type', 'lib', '--crate-name', 'probe', '--edition', '2021']
env = os.environ.copy()
env.update(CHARON_TOOLCHAIN_IS_IN_PATH='1', CARGO_BUILD_JOBS='1', RAYON_NUM_THREADS='1', CARGO_INCREMENTAL='0')
begin = time.monotonic()
with (scratch / f'{mode}.stdout').open('wb') as stdout, (scratch / f'{mode}.stderr').open('wb') as stderr:
    proc = subprocess.Popen(cmd, env=env, stdout=stdout, stderr=stderr, start_new_session=True)
    try:
        exit_code = proc.wait(timeout=20)
        timed_out = False
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
        exit_code = proc.returncode
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
result = {
    'mode': mode, 'cmd': cmd, 'exit_code': exit_code, 'timed_out': timed_out,
    'elapsed_seconds': round(time.monotonic() - begin, 6),
    'child_user_seconds': round(usage.ru_utime, 6),
    'child_system_seconds': round(usage.ru_stime, 6),
    'child_maxrss_bytes': usage.ru_maxrss,
    'llbc_bytes': (scratch / f'{mode}.llbc').stat().st_size if (scratch / f'{mode}.llbc').exists() else None,
}
(scratch / f'{mode}.json').write_text(json.dumps(result, indent=2) + '\n')
with (scratch / 'runs.jsonl').open('a') as runs:
    runs.write(json.dumps(result) + '\n')
print(json.dumps(result))
