#!/usr/bin/env python3
"""One guarded offline Charon extraction for a Unicode span fixture."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent
TOOLS = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RUST = TOOLS / 'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
CHARON = TOOLS / 'bin/charon'
WORK = HERE / 'work'
OUT = HERE / 'unicode.llbc'
RESULTS = HERE / 'results.json'
MIN_FREE_DISK = 10 * 1024**3
MIN_FREE_MEMORY_PERCENT = 30
MAX_EXTRA_RSS_KIB = 800 * 1024
MAX_SCRATCH_BYTES = 1024**3
TIMEOUT_SECONDS = 45

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def headroom():
    raw = subprocess.check_output(['/usr/bin/memory_pressure', '-Q'], text=True)
    match = re.search(r'System-wide memory free percentage: (\d+)%', raw)
    if not match:
        raise RuntimeError('memory_pressure output not understood')
    return {'free_memory_percent': int(match.group(1)),
            'free_disk_bytes': shutil.disk_usage(HERE).free}

def scratch_bytes():
    if not WORK.exists():
        return 0
    return sum(p.stat().st_size for p in WORK.rglob('*') if p.is_file())

def tree_rss_kib(root):
    raw = subprocess.check_output(['/bin/ps', '-axo', 'pid=,ppid=,rss='], text=True)
    rows = [tuple(map(int, line.split())) for line in raw.splitlines() if len(line.split()) == 3]
    children = {}
    rss = {}
    for pid, ppid, kib in rows:
        children.setdefault(ppid, []).append(pid)
        rss[pid] = kib
    stack = [root]
    seen = set()
    while stack:
        pid = stack.pop()
        if pid not in seen:
            seen.add(pid)
            stack.extend(children.get(pid, []))
    return sum(rss.get(pid, 0) for pid in seen)

def main():
    if WORK.exists() or OUT.exists() or RESULTS.exists():
        raise RuntimeError('fresh absent work/output/results paths required')
    assert CHARON.is_file() and (RUST / 'cargo').is_file()
    assert (HERE / 'fixture/Cargo.toml').is_file()
    before = headroom()
    if before['free_memory_percent'] < MIN_FREE_MEMORY_PERCENT or before['free_disk_bytes'] < MIN_FREE_DISK:
        raise RuntimeError(f'preflight refused: {before}')
    shutil.copytree(HERE / 'fixture', WORK)
    env = dict(os.environ)
    env.update(RUSTUP_HOME=str(TOOLS / 'rustup'), CARGO_HOME=str(TOOLS / 'cargo'),
               CHARON_TOOLCHAIN_IS_IN_PATH='1', CARGO_BUILD_JOBS='1',
               CARGO_INCREMENTAL='0', RAYON_NUM_THREADS='1', CARGO_NET_OFFLINE='true',
               CARGO_TARGET_DIR=str(WORK / 'target'),
               PATH=os.pathsep.join((str(RUST), str(TOOLS / 'bin'), env.get('PATH', ''))),
               DYLD_LIBRARY_PATH=os.pathsep.join((str(RUST.parent / 'lib'),
                   str(RUST.parent / 'lib/rustlib/aarch64-apple-darwin/lib'),
                   env.get('DYLD_LIBRARY_PATH', ''))))
    cmd = [str(CHARON), 'cargo', '--preset', 'aeneas', '--dest-file', str(OUT), '--',
           '--manifest-path', str(WORK / 'Cargo.toml'), '--package', 'unicode_span_probe',
           '--lib', '--offline', '--locked']
    started = time.monotonic()
    proc = subprocess.Popen(cmd, cwd=WORK, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, start_new_session=True)
    samples = []
    stop = None
    try:
        while proc.poll() is None:
            h = headroom()
            sample = {'elapsed_seconds': round(time.monotonic()-started, 4),
                      'rss_kib': tree_rss_kib(proc.pid), 'scratch_bytes': scratch_bytes(), **h}
            samples.append(sample)
            if sample['rss_kib'] > MAX_EXTRA_RSS_KIB:
                stop = 'rss cap'
            elif sample['scratch_bytes'] > MAX_SCRATCH_BYTES:
                stop = 'scratch cap'
            elif sample['free_memory_percent'] < MIN_FREE_MEMORY_PERCENT or sample['free_disk_bytes'] < MIN_FREE_DISK:
                stop = 'headroom'
            elif sample['elapsed_seconds'] > TIMEOUT_SECONDS:
                stop = 'timeout'
            if stop:
                os.killpg(proc.pid, signal.SIGTERM)
                break
            time.sleep(0.05)
        try:
            stdout, stderr = proc.communicate(timeout=3)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            stdout, stderr = proc.communicate(timeout=3)
        final_scratch = scratch_bytes()
        if final_scratch > MAX_SCRATCH_BYTES:
            stop = 'scratch cap at exit'
        result = {
            'preflight': before, 'limits': {'min_free_memory_percent': MIN_FREE_MEMORY_PERCENT,
                'min_free_disk_bytes': MIN_FREE_DISK, 'max_extra_rss_kib': MAX_EXTRA_RSS_KIB,
                'max_scratch_bytes': MAX_SCRATCH_BYTES, 'timeout_seconds': TIMEOUT_SECONDS},
            'versions': {'charon_sha256': sha(CHARON), 'cargo_sha256': sha(RUST/'cargo'),
                         'rustc_sha256': sha(RUST/'rustc')},
            'fixture_sha256': {str(p.relative_to(HERE/'fixture')): sha(p)
                               for p in sorted((HERE/'fixture').rglob('*')) if p.is_file()},
            'command': [v.replace(str(HERE), '$PACKAGE').replace(str(TOOLS), '$TOOLS') for v in cmd],
            'environment': {k: env[k] for k in ('CARGO_BUILD_JOBS','CARGO_INCREMENTAL','RAYON_NUM_THREADS','CARGO_NET_OFFLINE')},
            'exit': proc.returncode, 'stopped': stop, 'stdout': stdout,
            'stderr': stderr.replace(str(HERE), '$PACKAGE').replace(str(TOOLS), '$TOOLS'),
            'elapsed_seconds': round(time.monotonic()-started, 4),
            'samples': samples, 'peak_sampled_rss_kib': max((s['rss_kib'] for s in samples), default=0),
            'peak_sampled_scratch_bytes': max((s['scratch_bytes'] for s in samples), default=0),
            'final_scratch_bytes': final_scratch,
            'output': {'sha256': sha(OUT), 'bytes': OUT.stat().st_size} if OUT.exists() else None,
        }
        RESULTS.write_text(json.dumps(result, indent=2, ensure_ascii=False)+'\n')
        if proc.returncode != 0 or stop or not OUT.exists():
            raise RuntimeError(f'extraction failed or stopped: {proc.returncode} {stop}')
    finally:
        shutil.rmtree(WORK, ignore_errors=True)

if __name__ == '__main__':
    main()
