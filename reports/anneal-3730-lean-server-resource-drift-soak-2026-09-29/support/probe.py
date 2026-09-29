#!/usr/bin/env python3
"""Guarded multi-restart direct Lean LSP resource soak (not Anneal)."""
import argparse
import hashlib
import json
import os
import re
import select
import signal
import subprocess
import time
from pathlib import Path

DEP = 'def depValue : Nat := 7\n'
PROOF = 'import Dep\n\ntheorem proof : depValue = 7 := by\n  exact ?_\n'
MAX_SECONDS = 390
SEGMENT_SECONDS = 110
ROUND_GAP_SECONDS = 5
MAX_RSS = int(4.5 * (1 << 30))
MAX_DISK = 20 * (1 << 20)
MIN_FREE_PERCENT = 25
MAX_TREE_PROCESSES = 4


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cmd(argv, **kw):
    p = subprocess.run([str(x) for x in argv], capture_output=True, text=True,
                       timeout=kw.pop('timeout', 20), **kw)
    return {'argv': [str(x) for x in argv], 'exit': p.returncode,
            'stdout': p.stdout, 'stderr': p.stderr}


def free_percent():
    out = cmd(['/usr/bin/memory_pressure', '-Q'])
    m = re.search(r'System-wide memory free percentage: (\d+)%', out['stdout'])
    if out['exit'] or not m:
        raise RuntimeError(out)
    return int(m.group(1))


def process_tree(pid):
    out = cmd(['/bin/ps', '-axo', 'pid=,ppid=,rss=,comm='])
    assert out['exit'] == 0
    all_rows = {}
    for line in out['stdout'].splitlines():
        parts = line.strip().split(maxsplit=3)
        if len(parts) < 4:
            continue
        try:
            p, parent, rss = map(int, parts[:3])
        except ValueError:
            continue
        all_rows[p] = {'pid': p, 'ppid': parent, 'rss_bytes': rss * 1024,
                       'command': parts[3]}
    found = {pid}
    while True:
        more = found | {p for p, r in all_rows.items() if r['ppid'] in found}
        if more == found:
            break
        found = more
    rows = [all_rows[p] for p in sorted(found) if p in all_rows]
    return {'rows': rows, 'processes': len(rows),
            'rss_sum_bytes': sum(r['rss_bytes'] for r in rows)}


def disk(root):
    rows = []
    paths = [root]
    for base, dirs, files in os.walk(root, followlinks=False):
        dirs.sort()
        files.sort()
        paths += [Path(base) / name for name in dirs + files]
    for path in paths:
        st = path.lstat()
        kind = 'symlink' if path.is_symlink() else ('directory' if path.is_dir() else 'file')
        rows.append({'path': str(path.relative_to(root)) or '.', 'kind': kind,
                     'logical_bytes': st.st_size, 'blocks_bytes': st.st_blocks * 512,
                     'device': st.st_dev, 'inode': st.st_ino,
                     'sha256': sha(path) if kind == 'file' else None})
    files = [r for r in rows if r['kind'] == 'file']
    return {'rows': rows, 'files': len(files), 'entries': len(rows),
            'payload_bytes': sum(r['logical_bytes'] for r in files),
            'blocks_bytes': sum(r['blocks_bytes'] for r in files),
            'distinct_inodes': len({(r['device'], r['inode']) for r in rows})}


def footprint(pids):
    if not pids:
        return {'exit': None, 'summary_bytes': None, 'raw': ''}
    out = cmd(['/usr/bin/footprint', '--noCategories', '--format', 'bytes'] +
              [str(p) for p in pids], timeout=30)
    m = re.search(r'Summary Footprint: ([\d,]+) B', out['stdout'])
    members = [int(x) for x in re.findall(r'^    phys_footprint: (\d+) B$',
                                            out['stdout'], re.M)]
    return {'exit': out['exit'], 'summary_bytes': int(m.group(1).replace(',', '')) if m else None,
            'per_pid_phys_footprint_bytes': members, 'raw': out['stdout'], 'stderr': out['stderr']}


class Server:
    def __init__(self, lean, root):
        self.root = root
        self.file = root / 'Proof.lean'
        self.buffer = b''
        self.nextid = 2
        self.p = subprocess.Popen([str(lean), '--server'], cwd=root,
            env=dict(os.environ, LEAN_PATH=str(root), LEAN_NUM_THREADS='1'),
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            bufsize=0, start_new_session=True)
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
            if b'\r\n\r\n' in self.buffer:
                head, body = self.buffer.split(b'\r\n\r\n', 1)
                lengths = [int(h.split(b':', 1)[1]) for h in head.split(b'\r\n')
                           if h.lower().startswith(b'content-length:')]
                if lengths and len(body) >= lengths[0]:
                    raw, self.buffer = body[:lengths[0]], body[lengths[0]:]
                    msg = json.loads(raw)
                    if msg.get('method') in ('client/registerCapability', 'workspace/inlayHint/refresh') and 'id' in msg:
                        self.send({'jsonrpc': '2.0', 'id': msg['id'], 'result': None})
                    return msg
            ready, _, _ = select.select([self.p.stdout], [], [], min(.1, end - time.monotonic()))
            if ready:
                chunk = os.read(self.p.stdout.fileno(), 65536)
                if not chunk:
                    break
                self.buffer += chunk
        raise TimeoutError('Lean LSP read')

    def until(self, rid):
        for _ in range(100):
            msg = self.read()
            if msg.get('id') == rid and 'method' not in msg:
                return msg
        raise TimeoutError(f'Lean request {rid}')

    def request(self, method, params):
        rid = self.nextid
        self.nextid += 1
        self.send({'jsonrpc': '2.0', 'id': rid, 'method': method, 'params': params})
        return self.until(rid)

    def open(self, source):
        self.send({'jsonrpc': '2.0', 'method': 'textDocument/didOpen', 'params': {
            'textDocument': {'uri': self.file.as_uri(), 'languageId': 'lean',
                             'version': 1, 'text': source}}})
        return self.wait(1)

    def edit(self, source, version):
        self.send({'jsonrpc': '2.0', 'method': 'textDocument/didChange', 'params': {
            'textDocument': {'uri': self.file.as_uri(), 'version': version},
            'contentChanges': [{'text': source}]}})
        return self.wait(version)

    def wait(self, version):
        return self.request('textDocument/waitForDiagnostics',
                            {'uri': self.file.as_uri(), 'version': version})

    def goal(self):
        return self.request('$/lean/plainGoal',
                            {'textDocument': {'uri': self.file.as_uri()},
                             'position': {'line': 3, 'character': 10}})

    def stop(self):
        if self.p.poll() is not None:
            return {'exit': self.p.returncode, 'forced': False}
        try:
            reply = self.request('shutdown', None)
            self.send({'jsonrpc': '2.0', 'method': 'exit'})
            self.p.wait(timeout=5)
            return {'exit': self.p.returncode, 'forced': False, 'reply': reply,
                    'stderr': self.p.stderr.read().decode(errors='replace')}
        except Exception as exc:
            os.killpg(self.p.pid, signal.SIGKILL)
            self.p.wait(timeout=5)
            return {'exit': self.p.returncode, 'forced': True, 'error': repr(exc)}


def sample(root, server, start, label, include_footprint):
    tree = process_tree(server.p.pid)
    files = disk(root)
    free = free_percent()
    if tree['processes'] > MAX_TREE_PROCESSES or tree['rss_sum_bytes'] > MAX_RSS or \
       files['blocks_bytes'] > MAX_DISK or free < MIN_FREE_PERCENT or \
       time.monotonic() - start > MAX_SECONDS:
        os.killpg(server.p.pid, signal.SIGKILL)
        raise RuntimeError(f'resource guard: {label}, tree={tree["processes"]}/'
                           f'{tree["rss_sum_bytes"]}, disk={files["blocks_bytes"]}, free={free}')
    fp = footprint([r['pid'] for r in tree['rows']]) if include_footprint else None
    if fp and (fp['exit'] or fp['summary_bytes'] is None or fp['summary_bytes'] > MAX_RSS):
        os.killpg(server.p.pid, signal.SIGKILL)
        raise RuntimeError(f'footprint guard: {label}: {fp}')
    return {'elapsed_seconds': round(time.monotonic() - start, 3), 'label': label,
            'tree': tree, 'disk': files, 'free_percent': free, 'footprint': fp}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    a = parser.parse_args()
    if a.work.exists():
        raise SystemExit('work path must be absent')
    a.work.mkdir(parents=True)
    a.out.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    results = {'lean_sha256': sha(a.lean), 'host_ram_bytes': int(cmd(
        ['/usr/sbin/sysctl', '-n', 'hw.memsize'])['stdout']),
        'preflight_free_percent': free_percent(),
        'disk_preflight': cmd(['/bin/df', '-P', str(a.work)]),
        'guards': {'max_seconds': MAX_SECONDS, 'segment_seconds': SEGMENT_SECONDS,
                   'round_gap_seconds': ROUND_GAP_SECONDS, 'max_rss_or_footprint_bytes': MAX_RSS,
                   'max_disk_bytes': MAX_DISK, 'min_free_percent': MIN_FREE_PERCENT,
                   'max_tree_processes': MAX_TREE_PROCESSES}, 'segments': []}
    assert results['preflight_free_percent'] >= 35
    assert int(results['disk_preflight']['stdout'].splitlines()[1].split()[3]) > 5 * (1 << 20)
    (a.work / 'Dep.lean').write_text(DEP)
    (a.work / 'Proof.lean').write_text(PROOF)
    compile_result = cmd([a.lean, '-o', 'Dep.olean', 'Dep.lean'], cwd=a.work,
                         env=dict(os.environ, LEAN_NUM_THREADS='1'))
    assert compile_result['exit'] == 0, compile_result
    results['dependency_build'] = compile_result
    results['dep_olean_sha256'] = sha(a.work / 'Dep.olean')
    results['initial_disk'] = disk(a.work)
    try:
        for segment_id in range(1, 4):
            server = Server(a.lean, a.work)
            segment = {'id': segment_id, 'server_pid': server.p.pid, 'rounds': [], 'samples': []}
            results['segments'].append(segment)
            try:
                text = (a.work / 'Proof.lean').read_text()
                opened = server.open(text)
                goal = server.goal()
                assert opened.get('result') == {} and '⊢ depValue = 7' in str(goal.get('result'))
                segment['initial'] = {'wait': opened, 'goal': goal,
                                      'disk_source_sha256': sha(a.work / 'Proof.lean')}
                segment['samples'].append(sample(a.work, server, start, 'segment-start', True))
                segment_start = time.monotonic()
                last_full_sample = time.monotonic()
                version = 1
                while time.monotonic() - segment_start < SEGMENT_SECONDS:
                    version += 1
                    text = PROOF + f'-- segment {segment_id}, version {version}\n'
                    wait = server.edit(text, version)
                    goal = server.goal()
                    assert wait.get('result') == {} and '⊢ depValue = 7' in str(goal.get('result'))
                    segment['rounds'].append({'version': version, 'source_sha256': hashlib.sha256(text.encode()).hexdigest(),
                                              'wait': wait, 'goal': goal})
                    if time.monotonic() - last_full_sample >= 10:
                        segment['samples'].append(sample(a.work, server, start, 'periodic', True))
                        last_full_sample = time.monotonic()
                    else:
                        sample(a.work, server, start, 'guard-only', False)
                    end_pause = time.monotonic() + ROUND_GAP_SECONDS
                    while time.monotonic() < end_pause:
                        time.sleep(min(.5, end_pause - time.monotonic()))
                        if time.monotonic() - start > MAX_SECONDS:
                            os.killpg(server.p.pid, signal.SIGKILL)
                            raise RuntimeError('duration cap')
                segment['samples'].append(sample(a.work, server, start, 'segment-end', True))
                segment['final_buffer_sha256'] = hashlib.sha256(text.encode()).hexdigest()
                (a.work / 'Proof.lean').write_text(text)
                segment['saved_disk_sha256'] = sha(a.work / 'Proof.lean')
                segment['elapsed_seconds'] = round(time.monotonic() - segment_start, 3)
            finally:
                segment['shutdown'] = server.stop()
                segment['tree_after_shutdown'] = process_tree(server.p.pid)
                segment['disk_after_shutdown'] = disk(a.work)
            (a.out / 'results.json').write_text(json.dumps(results, indent=2, sort_keys=True, ensure_ascii=False) + '\n')
    finally:
        results['total_seconds'] = round(time.monotonic() - start, 3)
        results['final_disk'] = disk(a.work)
        (a.out / 'results.json').write_text(json.dumps(results, indent=2, sort_keys=True, ensure_ascii=False) + '\n')
    print(json.dumps({'total_seconds': results['total_seconds'],
                      'rounds': [len(x['rounds']) for x in results['segments']],
                      'samples': [len(x['samples']) for x in results['segments']]}))


if __name__ == '__main__':
    main()
