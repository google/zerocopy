import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

root = Path(__file__).resolve().parent
version, label, cwd, *args = sys.argv[1:]
toolroot = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains')
binroot = toolroot / ('leanprover--lean4---v' + version) / 'bin'
cmd = [str(binroot / 'lake'), *args]
env = os.environ.copy()
env.update(ELAN_TOOLCHAIN='leanprover/lean4:v' + version,
           PATH=str(binroot) + ':' + env.get('PATH', ''),
           LEAN_NUM_THREADS='1', LAKE_ARTIFACT_CACHE='false',
           LAKE_CACHE_DIR=str(root / 'cache' / version),
           MATHLIB_NO_CACHE_ON_UPDATE='1', HOME=str(root / 'home'))
Path(env['HOME']).mkdir(exist_ok=True)
Path(env['LAKE_CACHE_DIR']).mkdir(parents=True, exist_ok=True)

def free_disk():
    d = shutil.disk_usage(root)
    return d.free

def free_memory_pct():
    out = subprocess.check_output(['memory_pressure', '-Q'], text=True)
    return int(re.search(r'System-wide memory free percentage:\s*(\d+)%', out).group(1))

def group_rss_kib(pgid):
    out = subprocess.check_output(['ps', '-axo', 'pgid=,rss='], text=True)
    return sum(int(parts[1]) for line in out.splitlines()
               if (parts := line.split()) and len(parts) == 2 and int(parts[0]) == pgid)

samples = []
before = {'disk_free_bytes': free_disk(), 'memory_pressure_free_pct': free_memory_pct()}
if before['disk_free_bytes'] <= 10 * 1024**3 or before['memory_pressure_free_pct'] < 10:
    raise SystemExit('Admission gate failed: ' + json.dumps(before))
t0 = time.monotonic()
p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE,
                     stderr=subprocess.PIPE, start_new_session=True)
reason = None
while p.poll() is None:
    sample = {'seconds': round(time.monotonic()-t0, 3),
              'rss_kib': group_rss_kib(p.pid),
              'disk_free_bytes': free_disk(),
              'memory_pressure_free_pct': free_memory_pct()}
    samples.append(sample)
    if sample['rss_kib'] * 1024 >= 2 * 1024**3:
        reason = 'process group RSS reached 2 GiB'
    elif sample['disk_free_bytes'] <= 10 * 1024**3:
        reason = 'disk free reached 10 GiB'
    elif sample['memory_pressure_free_pct'] < 10:
        reason = 'memory_pressure free fell below 10%'
    elif sample['seconds'] > 45:
        reason = '45-second command deadline'
    if reason:
        os.killpg(p.pid, signal.SIGKILL)
        break
    time.sleep(0.2)
stdout, stderr = p.communicate()
record = {'label': label, 'version': version, 'cmd': cmd, 'cwd': cwd,
          'env': {k: env[k] for k in ('ELAN_TOOLCHAIN','LEAN_NUM_THREADS','LAKE_ARTIFACT_CACHE','LAKE_CACHE_DIR','MATHLIB_NO_CACHE_ON_UPDATE','HOME')},
          'before': before, 'samples': samples, 'after': {'disk_free_bytes': free_disk(), 'memory_pressure_free_pct': free_memory_pct()},
          'exit': p.returncode, 'abort': reason, 'seconds': round(time.monotonic()-t0, 3),
          'stdout': stdout.decode(errors='replace'), 'stderr': stderr.decode(errors='replace')}
with (root / 'runs.jsonl').open('a') as f:
    f.write(json.dumps(record) + '\n')
print(label, 'exit', p.returncode, 'abort', reason, 'seconds', record['seconds'])
print(record['stdout'][-1000:])
print(record['stderr'][-1000:])
sys.exit(0 if p.returncode == 0 and reason is None else 1)
