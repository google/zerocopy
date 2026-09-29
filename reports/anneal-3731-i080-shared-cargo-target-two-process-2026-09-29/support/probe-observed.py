#!/usr/bin/env python3
"""Bounded private Charon/Cargo shared-target contention and cancellation control."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parent
SRC = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports/anneal-3730-charon-warm-target-controls-2026-09-29/support/fixture/origin')
TOOLS = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RUST = TOOLS / 'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
CHARON = TOOLS / 'bin/charon'
WORK = ROOT / 'work'
LIMIT_RSS_KIB = 1536 * 1024
LIMIT_WORK_KIB = 4 * 1024 * 1024
TIMEOUT = 25

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def kib(path):
    out = subprocess.check_output(['/usr/bin/du', '-sk', str(path)], text=True)
    return int(out.split()[0])

def process_tree():
    out = subprocess.check_output(['/bin/ps', '-axo', 'pid=,ppid=,pgid=,rss=,state='], text=True)
    rows = []
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 5:
            rows.append((int(parts[0]), int(parts[1]), int(parts[2]), int(parts[3]), parts[4]))
    return rows

def descendants(pid, rows):
    found = {pid}
    while True:
        more = found | {p for p, parent, _, _, _ in rows if parent in found}
        if more == found:
            return found
        found = more

def env(target):
    e = dict(os.environ)
    e.update(RUSTUP_HOME=str(TOOLS/'rustup'), CARGO_HOME=str(TOOLS/'cargo'),
             CHARON_TOOLCHAIN_IS_IN_PATH='1', CARGO_BUILD_JOBS='1',
             CARGO_INCREMENTAL='0', RAYON_NUM_THREADS='1', CARGO_NET_OFFLINE='true',
             CARGO_TARGET_DIR=str(target), BUILD_VALUE='7',
             PATH=os.pathsep.join((str(RUST),str(TOOLS/'bin'),e.get('PATH',''))),
             DYLD_LIBRARY_PATH=os.pathsep.join((str(RUST.parent/'lib'),
                 str(RUST.parent/'lib/rustlib/aarch64-apple-darwin/lib'),e.get('DYLD_LIBRARY_PATH',''))))
    return e

def start(root, target, dest):
    argv = [str(CHARON), 'cargo', '--preset', 'aeneas', '--dest-file', str(dest), '--',
            '--manifest-path', str(root/'Cargo.toml'), '--package', 'warm_probe',
            '--lib', '--offline', '--locked']
    return subprocess.Popen(argv, cwd=root, env=env(target), stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, start_new_session=True)

def terminate(proc):
    if proc.poll() is None:
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait(timeout=2)

def snapshot(procs):
    rows = process_tree()
    each = {}
    for name, proc in procs.items():
        members = descendants(proc.pid, rows)
        live = [(p,rss) for p,_,pgid,rss,state in rows
                if (p in members or pgid == proc.pid) and not state.startswith('Z')]
        each[name] = {'pid':proc.pid, 'exit':proc.poll(), 'members':live,
                      'rss_sum_kib':sum(rss for _,rss in live)}
    return {'at':time.monotonic(), 'processes':each, 'work_kib':kib(WORK)}

def run_pair(label, cancel):
    target = WORK / f'{label}-shared-target'
    procs = {name:start(WORK/name, target, WORK/f'{label}-{name}.llbc') for name in ('A','B')}
    start_at = time.monotonic()
    samples = []
    cancelled = False
    reason = None
    try:
        while time.monotonic()-start_at < TIMEOUT:
            s=snapshot(procs); samples.append(s)
            if any(x['rss_sum_kib'] > LIMIT_RSS_KIB for x in s['processes'].values()):
                reason='rss_guard'; break
            if s['work_kib'] > LIMIT_WORK_KIB:
                reason='disk_guard'; break
            if cancel and not cancelled and (WORK/'A/app/.build-entered').exists() and procs['B'].poll() is None:
                terminate(procs['A']); cancelled=True
            if all(p.poll() is not None for p in procs.values()): break
            time.sleep(.05)
        else:
            reason='timeout'
    finally:
        if reason:
            for p in procs.values(): terminate(p)
    results={}
    for name,p in procs.items():
        out,err=p.communicate(timeout=2)
        dest=WORK/f'{label}-{name}.llbc'
        results[name]={'pid':p.pid,'exit':p.returncode,'stdout':out[-3000:],
                       'stderr':err[-3000:],'dest_sha256':sha(dest) if dest.exists() else None,
                       'dest_bytes':dest.stat().st_size if dest.exists() else None}
    return {'label':label,'cancel':cancel,'cancelled':cancelled,'guard':reason,
            'samples':samples,'results':results,'final_target_kib':kib(target) if target.exists() else 0}

if __name__ == '__main__':
    assert CHARON.is_file() and (RUST/'cargo').is_file()
    free=shutil.disk_usage(ROOT).free
    assert free > 10*1024**3, free
    assert not WORK.exists(), WORK
    WORK.mkdir()
    for name in ('A','B'):
        shutil.copytree(SRC, WORK/name)
        build=WORK/name/'app/build.rs'
        raw=build.read_text()
        raw=raw.replace('fn main() {', 'fn main() {\n  std::fs::write(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(".build-entered"), b"entered").unwrap();\n  std::thread::sleep(std::time::Duration::from_secs(2));')
        build.write_text(raw)
    preflight={'free_disk_bytes':free,'charon_sha256':sha(CHARON),
               'cargo_sha256':sha(RUST/'cargo'),'source_fixture':str(SRC),
               'baseline_work_kib':kib(WORK),'rss_guard_kib_each':LIMIT_RSS_KIB,
               'disk_guard_kib_total':LIMIT_WORK_KIB,'timeout_seconds':TIMEOUT}
    first=run_pair('complete',False)
    for name in ('A','B'):
        (WORK/name/'app/.build-entered').unlink(missing_ok=True)
    second=run_pair('cancel',True)
    result={'preflight':preflight,'runs':[first,second]}
    (ROOT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'preflight':preflight,'summary':[
        {'label':r['label'],'cancelled':r['cancelled'],'guard':r['guard'],
         'exits':{k:v['exit'] for k,v in r['results'].items()},
         'peak_rss_kib':{k:max(s['processes'][k]['rss_sum_kib'] for s in r['samples']) for k in ('A','B')},
         'peak_work_kib':max(s['work_kib'] for s in r['samples']),
         'final_target_kib':r['final_target_kib']} for r in (first,second)]},indent=2))
