#!/usr/bin/env python3
"""Bounded matched shared/isolated Lake writer gate and kill experiment."""
import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
TOOL = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
LAKE, LEAN = TOOL / 'lake', TOOL / 'lean'
RSS_LIMIT_KIB = 4_000_000


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def source(value):
    return '''import Lean
run_cmd do
  let marker ← IO.getEnv "WRITER_MARKER"
  let release ← IO.getEnv "WRITER_RELEASE"
  if let some marker := marker then
    IO.FS.writeFile marker "entered"
    if let some release := release then
      while !(← (System.FilePath.mk release).pathExists) do
        IO.sleep 10
def depValue : Nat := %d
''' % value


def env(home, marker=None, release=None, lean_path=None):
    e = dict(os.environ, HOME=str(home), LEAN_NUM_THREADS='1', LAKE_NO_NET='1',
             LAKE_ARTIFACT_CACHE='false', LAKE_NO_CACHE='1', ELAN_TOOLCHAIN='leanprover/lean4:v4.30.0-rc2')
    for k in ('WRITER_MARKER', 'WRITER_RELEASE'):
        e.pop(k, None)
    if marker is not None:
        e['WRITER_MARKER'] = str(marker)
        e['WRITER_RELEASE'] = str(release)
    if lean_path is not None:
        e['LEAN_PATH'] = str(lean_path)
    return e


def command(label, argv, cwd, home, lean_path=None):
    p = subprocess.run([str(x) for x in argv], cwd=cwd, env=env(home, lean_path=lean_path),
                       capture_output=True, text=True, timeout=40)
    return dict(label=label, argv=[Path(str(x)).name if str(x).startswith(str(TOOL)) else str(x) for x in argv],
                exit=p.returncode, stdout=p.stdout, stderr=p.stderr)


def rss_tree(roots):
    ps = subprocess.run(['ps', '-axo', 'pid=,ppid=,rss='], capture_output=True, text=True, timeout=5)
    rows = []
    for line in ps.stdout.splitlines():
        try:
            rows.append(tuple(map(int, line.split()[:3])))
        except ValueError:
            pass
    members = set(roots)
    for _ in range(8):
        members.update(pid for pid, parent, _ in rows if parent in members)
    return sum(rss for pid, _, rss in rows if pid in members), sorted(members)


def wait_markers(markers, procs, output):
    deadline = time.monotonic() + 30
    while not all(p.exists() for p in markers):
        rss, pids = rss_tree([p.pid for p in procs]); output['peak_sampled_rss_kib'] = max(output['peak_sampled_rss_kib'], rss)
        if rss > RSS_LIMIT_KIB:
            raise RuntimeError('summed RSS guard exceeded: %d KiB' % rss)
        if any(p.poll() is not None for p in procs):
            raise RuntimeError('writer exited before both gate markers')
        if time.monotonic() > deadline:
            raise TimeoutError('both gate markers')
        time.sleep(.05)
    output['gate_pids'] = rss_tree([p.pid for p in procs])[1]


def finish(proc, label):
    stdout, stderr = proc.communicate(timeout=40)
    return dict(label=label, exit=proc.returncode, stdout=stdout, stderr=stderr)


def preflight(root):
    assert LAKE.is_file() and LEAN.is_file()
    assert shutil.disk_usage(root).free > 10 * 1024**3
    p = subprocess.run(['memory_pressure'], capture_output=True, text=True, timeout=10)
    m = re.search(r'System-wide memory free percentage: (\d+)%', p.stdout)
    if not m or int(m.group(1)) < 35:
        raise RuntimeError('memory preflight under 35% available')
    return {'disk_free_bytes': shutil.disk_usage(root).free, 'memory_free_percent': int(m.group(1))}


def fixture(root, value):
    root.mkdir(parents=True)
    (root / 'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc2\n')
    (root / 'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage probe\n@[default_target]\nlean_lib Dep\n')
    (root / 'Dep.lean').write_text(source(value))


def cell(work, topology, victim):
    name = topology + '-kill-' + victim
    cellroot = work / name
    if cellroot.exists():
        shutil.rmtree(cellroot)
    home = cellroot / 'home'; home.mkdir(parents=True)
    aroot = cellroot / 'A'; broot = aroot if topology == 'shared' else cellroot / 'B'
    fixture(aroot, 7)
    if topology == 'isolated':
        fixture(broot, 9)
    out = dict(cell=name, preflight=preflight(work), events=[], records=[], peak_sampled_rss_kib=0)
    procs = []
    try:
        for label, root in [('prime_A', aroot), ('prime_B', broot)]:
            if label == 'prime_B' and topology == 'shared':
                continue
            rec = command(label, [LAKE, 'build', 'Dep'], root, home)
            out['records'].append(rec)
            if rec['exit'] != 0:
                raise RuntimeError(label + ' failed: ' + rec['stderr'])
            shutil.rmtree(root / '.lake' / 'build')
        ma, mb = cellroot / 'A.entered', cellroot / 'B.entered'
        ra, rb = cellroot / 'A.release', cellroot / 'B.release'
        a = subprocess.Popen([str(LAKE), 'build', 'Dep'], cwd=aroot, env=env(home, ma, ra),
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
        procs.append(a)
        wait_markers([ma], [a], out); out['events'].append('A_entered_7')
        if topology == 'shared':
            (aroot / 'Dep.lean').write_text(source(9))
            out['events'].append('shared_source_changed_to_9')
        b = subprocess.Popen([str(LAKE), 'build', 'Dep'], cwd=broot, env=env(home, mb, rb),
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
        procs.append(b)
        wait_markers([ma, mb], procs, out); out['events'].append('B_entered_9')
        killed, survived = (a, b) if victim == 'A' else (b, a)
        os.killpg(killed.pid, signal.SIGKILL); out['events'].append('killed_' + victim)
        out['records'].append(finish(killed, 'killed_' + victim))
        (rb if victim == 'A' else ra).write_text('release')
        out['events'].append('released_' + ('B' if victim == 'A' else 'A'))
        out['records'].append(finish(survived, 'survivor'))
        survivor_root = broot if victim == 'A' else aroot
        out['survivor_root'] = 'B' if victim == 'A' else 'A'
        out['source_sha256'] = sha(survivor_root / 'Dep.lean')
        artifact = survivor_root / '.lake/build/lib/lean/Dep.olean'
        trace = survivor_root / '.lake/build/lib/lean/Dep.trace'
        out['artifact_sha256'] = sha(artifact) if artifact.exists() else None
        if artifact.exists():
            dst = HERE / 'artifacts' / (name + '.olean'); dst.parent.mkdir(exist_ok=True)
            shutil.copy2(artifact, dst)
        out['trace_sha256'] = sha(trace) if trace.exists() else None
        if trace.exists():
            shutil.copy2(trace, HERE / 'artifacts' / (name + '.trace'))
        out['records'].append(command('no_build', [LAKE, '--no-build', 'build', 'Dep'], survivor_root, home))
        out['trace_after_no_build_sha256'] = sha(trace) if trace.exists() else None
        nobuild_trace = trace.with_name('Dep.trace.nobuild')
        out['no_build_trace_sha256'] = sha(nobuild_trace) if nobuild_trace.exists() else None
        (survivor_root / 'Check7.lean').write_text('import Dep\ntheorem check : depValue = 7 := by rfl\n#eval depValue\n')
        (survivor_root / 'Check9.lean').write_text('import Dep\ntheorem check : depValue = 9 := by rfl\n#eval depValue\n')
        for value in (7, 9):
            out['records'].append(command('fresh_' + str(value), [LEAN, 'Check%d.lean' % value], survivor_root, home,
                                          survivor_root / '.lake/build/lib/lean'))
        return out
    finally:
        for p in procs:
            if p.poll() is None:
                os.killpg(p.pid, signal.SIGKILL); p.wait()


def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--work', type=Path, default=HERE / '_work')
    ap.add_argument('--out', type=Path, default=HERE / 'results.json'); args = ap.parse_args()
    args.work.mkdir(parents=True, exist_ok=True)
    result = {'schema': 'i151-matched-lake-writer-isolation-v1', 'subject': {
        'lean_revision': '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc',
        'lake_sha256': sha(LAKE), 'lean_sha256': sha(LEAN)}, 'cells': []}
    for topology, victim in [('shared', 'A'), ('isolated', 'A'), ('shared', 'B'), ('isolated', 'B')]:
        result['cells'].append(cell(args.work, topology, victim))
        args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({c['cell']: [(r['label'], r['exit']) for r in c['records']] for c in result['cells']}))


if __name__ == '__main__':
    main()
