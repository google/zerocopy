#!/usr/bin/env python3
"""Bounded direct-Lean LSP scratch pool, with explicit admission control."""
import argparse
import hashlib
import json
import os
import re
import select
import shutil
import subprocess
import time
from pathlib import Path

DEP = 'def depValue : Nat := 7\n'
BAD = 'import Dep\n\ntheorem workerProof : depValue = 7 := by\n  exact ?_\n'
GOOD = 'import Dep\n\ntheorem workerProof : depValue = 7 := by\n  rfl\n'
CAP_BYTES = int(4.5 * (1 << 30))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cmd(argv, **kw):
    p = subprocess.run([str(x) for x in argv], text=True, capture_output=True,
                       timeout=kw.pop('timeout', 20), **kw)
    return {'argv': [str(x) for x in argv], 'exit': p.returncode,
            'stdout': p.stdout, 'stderr': p.stderr}


def mem_free():
    out = cmd(['/usr/bin/memory_pressure', '-Q'])
    m = re.search(r'System-wide memory free percentage: (\d+)%', out['stdout'])
    if out['exit'] or not m:
        raise RuntimeError(out)
    return {'free_percent': int(m.group(1)), 'command': out}


def child_pids(root):
    out = cmd(['/bin/ps', '-axo', 'pid=,ppid='])
    assert out['exit'] == 0
    children = {}
    for line in out['stdout'].splitlines():
        try:
            pid, ppid = map(int, line.split()[:2])
        except ValueError:
            continue
        children.setdefault(ppid, []).append(pid)
    found, queue = [], [root]
    while queue:
        pid = queue.pop()
        if pid not in found:
            found.append(pid)
            queue += children.get(pid, [])
    return sorted(found)


def physical_sample(servers):
    pids = sorted({p for s in servers for p in child_pids(s.p.pid)})
    rss = cmd(['/bin/ps', '-o', 'pid=,ppid=,rss=', '-p', ','.join(map(str, pids))])
    assert rss['exit'] == 0, rss
    rss_rows = []
    for line in rss['stdout'].splitlines():
        bits = line.split()
        if len(bits) >= 3:
            rss_rows.append({'pid': int(bits[0]), 'ppid': int(bits[1]),
                             'rss_kib': int(bits[2])})
    footprint = cmd(['/usr/bin/footprint', '--noCategories', '-f', 'bytes'] +
                    [str(p) for p in pids], timeout=30)
    # macOS prints one header per process, then a group Summary Footprint.
    match = re.search(r'Summary Footprint: ([\d,]+) B', footprint['stdout'])
    per_pid_physical = [int(x) for x in re.findall(r'^    phys_footprint: (\d+) B$',
                                                     footprint['stdout'], re.MULTILINE)]
    return {'pids': pids, 'rss_rows': rss_rows,
            'rss_sum_bytes': sum(x['rss_kib'] * 1024 for x in rss_rows),
            'footprint': footprint, 'parsed_footprint_bytes':
                int(match.group(1).replace(',', '')) if match else None,
            'per_pid_phys_footprint_bytes': per_pid_physical,
            'summed_phys_footprint_bytes': sum(per_pid_physical)}


def inventory(root):
    rows = []
    for base, dirs, files in os.walk(root, followlinks=False):
        for name in sorted(dirs + files):
            p = Path(base) / name
            st = p.lstat()
            rows.append({'path': str(p.relative_to(root)), 'kind': 'symlink' if p.is_symlink()
                         else ('directory' if p.is_dir() else 'file'),
                         'logical_bytes': st.st_size, 'blocks_bytes': st.st_blocks * 512,
                         'device': st.st_dev, 'inode': st.st_ino, 'nlink': st.st_nlink,
                         'sha256': sha(p) if p.is_file() and not p.is_symlink() else None})
    files = [r for r in rows if r['kind'] == 'file']
    return {'rows': rows, 'entries': len(rows), 'files': len(files),
            'payload_bytes': sum(r['logical_bytes'] for r in files),
            'allocated_charge_bytes': sum(r['blocks_bytes'] for r in files),
            'distinct_inodes': len({(r['device'], r['inode']) for r in rows})}


class Server:
    def __init__(self, lean, root, dep):
        self.root = root
        self.file = root / 'Proof.lean'
        self.buf = b''
        self.nextid = 2
        env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(dep))
        self.p = subprocess.Popen([str(lean), '--server'], cwd=root, env=env,
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, bufsize=0)
        self.send({'jsonrpc': '2.0', 'id': 1, 'method': 'initialize', 'params': {
            'processId': os.getpid(), 'rootUri': root.as_uri(), 'capabilities': {},
            'initializationOptions': {'hasWidgets': False}}})
        self.until(1)
        self.send({'jsonrpc': '2.0', 'method': 'initialized', 'params': {}})

    def send(self, obj):
        payload = json.dumps(obj, separators=(',', ':')).encode()
        self.p.stdin.write(b'Content-Length: ' + str(len(payload)).encode() + b'\r\n\r\n' + payload)
        self.p.stdin.flush()

    def read(self, timeout=20):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            if b'\r\n\r\n' in self.buf:
                header, body = self.buf.split(b'\r\n\r\n', 1)
                lengths = [int(x.split(b':', 1)[1]) for x in header.split(b'\r\n')
                           if x.lower().startswith(b'content-length:')]
                if lengths and len(body) >= lengths[0]:
                    raw, self.buf = body[:lengths[0]], body[lengths[0]:]
                    obj = json.loads(raw)
                    if obj.get('method') == 'client/registerCapability' and 'id' in obj:
                        self.send({'jsonrpc': '2.0', 'id': obj['id'], 'result': None})
                    return obj
            ready, _, _ = select.select([self.p.stdout], [], [], min(.1, end - time.monotonic()))
            if ready:
                more = os.read(self.p.stdout.fileno(), 65536)
                if not more:
                    break
                self.buf += more
        raise TimeoutError(f'LSP read from {self.p.pid}')

    def until(self, rid):
        for _ in range(100):
            obj = self.read()
            if obj.get('id') == rid:
                return obj
        raise TimeoutError(f'LSP request {rid}')

    def request(self, method, params):
        rid = self.nextid
        self.nextid += 1
        self.send({'jsonrpc': '2.0', 'id': rid, 'method': method, 'params': params})
        return self.until(rid)

    def open(self):
        self.send({'jsonrpc': '2.0', 'method': 'textDocument/didOpen', 'params': {
            'textDocument': {'uri': self.file.as_uri(), 'languageId': 'lean',
                             'version': 1, 'text': BAD}}})

    def edit(self):
        self.send({'jsonrpc': '2.0', 'method': 'textDocument/didChange', 'params': {
            'textDocument': {'uri': self.file.as_uri(), 'version': 2},
            'contentChanges': [{'text': GOOD}]}})

    def wait(self, version):
        return self.request('textDocument/waitForDiagnostics',
                            {'uri': self.file.as_uri(), 'version': version})

    def goal(self):
        return self.request('$/lean/plainGoal', {'textDocument': {'uri': self.file.as_uri()},
                                                    'position': {'line': 3, 'character': 10}})

    def stop(self):
        if self.p.poll() is not None:
            return {'exit': self.p.returncode, 'forced': False}
        try:
            reply = self.request('shutdown', None)
            self.send({'jsonrpc': '2.0', 'method': 'exit'})
            self.p.wait(timeout=5)
            return {'exit': self.p.returncode, 'shutdown': reply, 'forced': False,
                    'stderr': self.p.stderr.read().decode(errors='replace')}
        except Exception as exc:
            self.p.kill()
            self.p.wait(timeout=5)
            return {'exit': self.p.returncode, 'forced': True, 'error': repr(exc)}


def build_shared(lean, root):
    shared = root / 'shared'
    shared.mkdir()
    (shared / 'Dep.lean').write_text(DEP)
    (shared / 'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc2\n')
    start = time.monotonic()
    result = cmd([lean, '-o', 'Dep.olean', '-i', 'Dep.ilean', '-c', 'Dep.c', 'Dep.lean'],
                 cwd=shared, env=dict(os.environ, LEAN_NUM_THREADS='1'))
    result['seconds'] = round(time.monotonic() - start, 3)
    assert result['exit'] == 0, result
    return shared, result


def worker(lean, root, index, mode, shared):
    start = time.monotonic()
    path = root / f'worker-{index}'
    path.mkdir()
    dep = path / 'deps'
    if mode == 'warm':
        dep.symlink_to(shared, target_is_directory=True)
        preparation = {'method': 'symlink-prebuilt', 'compile': None}
    else:
        dep.mkdir()
        for src in (shared / 'Dep.lean', shared / 'lean-toolchain'):
            with src.open('rb') as i, (dep / src.name).open('wb') as o:
                while chunk := i.read(1 << 20):
                    o.write(chunk)
        build = cmd([lean, '-o', 'Dep.olean', '-i', 'Dep.ilean', '-c', 'Dep.c', 'Dep.lean'],
                    cwd=dep, env=dict(os.environ, LEAN_NUM_THREADS='1'))
        assert build['exit'] == 0, build
        preparation = {'method': 'local-source-build', 'compile': build}
    (path / 'Proof.lean').write_text(BAD)
    (path / 'lakefile.toml').write_text('name = "scratch-pool"\nversion = "0.1.0"\n')
    (path / 'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc2\n')
    preparation['seconds'] = round(time.monotonic() - start, 3)
    return path, dep, preparation


def cell(lean, base, n, mode):
    root = base / f'{mode}-{n}'
    root.mkdir()
    shared, dep_build = build_shared(lean, root)
    pairs = [worker(lean, root, i, mode, shared) for i in range(1, n + 1)]
    before = inventory(root)
    servers = []
    t0 = time.monotonic()
    result = {'mode': mode, 'workers': n, 'dep_build': dep_build,
              'worker_preparation': [x[2] for x in pairs],
              'disk_before': before,
              'memory_preflight': mem_free()}
    try:
        for path, dep, _ in pairs:
            servers.append(Server(lean, path, dep))
        result['launch_seconds'] = round(time.monotonic() - t0, 3)
        t1 = time.monotonic()
        for s in servers:
            s.open()
        wait1 = [s.wait(1) for s in servers]
        goal1 = [s.goal() for s in servers]
        result['open_query_seconds'] = round(time.monotonic() - t1, 3)
        result['wait1'] = wait1
        result['goal1'] = goal1
        result['memory_open'] = physical_sample(servers)
        if result['memory_open']['parsed_footprint_bytes'] is None or result['memory_open']['parsed_footprint_bytes'] > CAP_BYTES:
            raise RuntimeError('open-phase footprint missing or over cap')
        t2 = time.monotonic()
        for s in servers:
            s.edit()
        wait2 = [s.wait(2) for s in servers]
        goal2 = [s.goal() for s in servers]
        result['edit_query_seconds'] = round(time.monotonic() - t2, 3)
        result['wait2'] = wait2
        result['goal2'] = goal2
        result['memory_edited'] = physical_sample(servers)
        if result['memory_edited']['parsed_footprint_bytes'] is None or result['memory_edited']['parsed_footprint_bytes'] > CAP_BYTES:
            raise RuntimeError('edit-phase footprint missing or over cap')
        result['disk_live'] = inventory(root)
    finally:
        result['cleanup'] = [s.stop() for s in reversed(servers)]
        result['disk_after'] = inventory(root)
        result['memory_after'] = mem_free()
        for path, _, _ in pairs:
            shutil.rmtree(path)
        result['disk_reclaimed'] = inventory(root)
    return result


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--lean', type=Path, required=True)
    p.add_argument('--work', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    if a.work.exists():
        raise SystemExit('work path must be absent')
    a.work.mkdir(parents=True)
    a.out.mkdir(parents=True, exist_ok=True)
    results = {'lean': str(a.lean), 'lean_sha256': sha(a.lean),
               'host_ram_bytes': int(cmd(['/usr/sbin/sysctl', '-n', 'hw.memsize'])['stdout']),
               'cap_bytes': CAP_BYTES, 'initial_memory': mem_free(),
               'initial_df': cmd(['/bin/df', '-P', str(a.work)]),
               'admissions': {}, 'cells': {}, 'skipped': {}}
    max_observed_per_worker = None
    try:
        for n in (1, 2, 4, 8):
            free = mem_free()['free_percent'] * results['host_ram_bytes'] / 100
            estimate = int((max_observed_per_worker or (1.35 * (1 << 30))) * n * 1.12)
            # Leave 0.5 GiB of the current reported free memory untouched.
            allowed = estimate <= CAP_BYTES and estimate + (1 << 29) <= free
            results['admissions'][str(n)] = {'estimated_bytes': estimate,
                'free_estimated_bytes': int(free), 'cap_bytes': CAP_BYTES,
                'reserve_bytes': 1 << 29, 'allowed': allowed}
            if not allowed:
                results['skipped'][str(n)] = {'estimated_bytes': estimate,
                    'free_estimated_bytes': int(free), 'cap_bytes': CAP_BYTES,
                    'reason': 'projected aggregate exceeds 4.5 GiB cap or current free-memory reserve'}
                continue
            for mode in ('cold', 'warm'):
                outcome = cell(a.lean, a.work, n, mode)
                results['cells'][f'{mode}-{n}'] = outcome
                samples = [outcome[k]['parsed_footprint_bytes'] or outcome[k]['rss_sum_bytes']
                           for k in ('memory_open', 'memory_edited')]
                max_observed_per_worker = max(max_observed_per_worker or 0,
                                               max(samples) / n)
            (a.out / 'results.json').write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
    finally:
        (a.out / 'results.json').write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'cells': list(results['cells']), 'skipped': results['skipped']}, indent=2))


if __name__ == '__main__':
    main()
