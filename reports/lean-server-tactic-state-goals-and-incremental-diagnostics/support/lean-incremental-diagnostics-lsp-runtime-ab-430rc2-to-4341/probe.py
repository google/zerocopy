#!/usr/bin/env python3
"""Serialized, bounded Lean LSP diagnostic publication probe."""
import argparse
import hashlib
import json
import os
import re
import select
import signal
import subprocess
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
FIX = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports/lean-incremental-diagnostics-430rc2-to-4341-source-delta-2026-10-01/fixture')
TC = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains')
VERSIONS = {'old': ('leanprover--lean4---v4.30.0-rc2', '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc'), 'new': ('leanprover--lean4---v4.34.1', '5045d0056413266e57c625dcd7c365b10e377c52')}
CAP_KIB = 1536 * 1024

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def free_percent():
    p = subprocess.run(['/usr/bin/memory_pressure', '-Q'], capture_output=True, text=True, timeout=5)
    m = re.search(r'System-wide memory free percentage: (\d+)%', p.stdout)
    return int(m.group(1)) if m else None

def group_rows(pgid):
    p = subprocess.run(['/bin/ps', '-axo', 'pid=,pgid=,rss=,command='], capture_output=True, text=True, timeout=5)
    rows = []
    for line in p.stdout.splitlines():
        a = line.split(None, 3)
        if len(a) == 4:
            try:
                if int(a[1]) == pgid:
                    rows.append({'pid': int(a[0]), 'rss_kib': int(a[2]), 'command': a[3]})
            except ValueError:
                pass
    return rows

class Case:
    def __init__(self, version, capability):
        self.version, self.capability = version, capability
        self.label = f'{version}-{capability}'
        self.dir = ROOT / 'raw' / self.label
        if self.dir.exists():
            raise RuntimeError('case already exists: ' + str(self.dir))
        self.dir.mkdir(parents=True)
        self.bin = TC / VERSIONS[version][0] / 'bin/lean'
        self.p = None
        self.buf = b''
        self.n = 0
        self.events = []
        self.samples = []
        self.abort = None
        self.done = threading.Event()
        self.stdout_raw = (self.dir / 'server.stdout.lsp').open('wb')
        self.stderr_raw = (self.dir / 'server.stderr').open('wb')

    def event(self, kind, **kw):
        self.events.append({'seq': len(self.events), 'time_ns': time.time_ns(), 'kind': kind, **kw})

    def monitor(self):
        while not self.done.is_set():
            try:
                rows = group_rows(self.p.pid)
                rss = sum(r['rss_kib'] for r in rows)
                free = free_percent()
                sample = {'time_ns': time.time_ns(), 'rss_kib': rss, 'free_percent': free, 'rows': rows}
                self.samples.append(sample)
                if rss > CAP_KIB or (free is not None and free < 10):
                    self.abort = {'reason': 'resource guard', 'sample': sample, 'cap_kib': CAP_KIB}
                    os.killpg(self.p.pid, signal.SIGTERM)
                    self.done.set()
                    return
            except Exception as e:
                self.abort = {'reason': 'monitor error', 'error': repr(e)}
                self.done.set()
                return
            self.done.wait(.25)

    def send(self, m):
        if self.abort:
            raise RuntimeError(str(self.abort))
        data = json.dumps(m, separators=(',', ':'), ensure_ascii=False).encode('utf-8')
        framed = b'Content-Length: ' + str(len(data)).encode() + b'\r\n\r\n' + data
        self.p.stdin.write(framed)
        self.p.stdin.flush()
        self.event('client', message=m, framed_sha256=hashlib.sha256(framed).hexdigest())

    def read(self, deadline):
        while time.monotonic() < deadline:
            if self.abort:
                raise RuntimeError(str(self.abort))
            hsep = self.buf.find(b'\r\n\r\n')
            if hsep >= 0:
                head = self.buf[:hsep]
                m = re.search(rb'(?im)^Content-Length:\s*(\d+)\s*$', head)
                if not m:
                    raise RuntimeError('invalid LSP header: ' + repr(head))
                n = int(m.group(1))
                if len(self.buf) >= hsep + 4 + n:
                    raw = self.buf[hsep + 4:hsep + 4 + n]
                    self.buf = self.buf[hsep + 4 + n:]
                    msg = json.loads(raw)
                    self.event('server', message=msg, body_sha256=hashlib.sha256(raw).hexdigest())
                    if 'id' in msg and 'method' in msg:
                        self.send({'jsonrpc': '2.0', 'id': msg['id'], 'result': None})
                    return msg
            rd, _, _ = select.select([self.p.stdout], [], [], min(.25, max(0, deadline - time.monotonic())))
            if rd:
                chunk = os.read(self.p.stdout.fileno(), 65536)
                if not chunk:
                    raise EOFError('server stdout closed')
                self.stdout_raw.write(chunk)
                self.stdout_raw.flush()
                self.buf += chunk
        raise TimeoutError('LSP response timeout')

    def request(self, method, params, timeout=30):
        self.n += 1
        rid = self.n
        self.send({'jsonrpc': '2.0', 'id': rid, 'method': method, 'params': params})
        deadline = time.monotonic() + timeout
        while True:
            msg = self.read(deadline)
            if msg.get('id') == rid and 'method' not in msg:
                return msg

    def drain(self, seconds):
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            try:
                self.read(deadline)
            except TimeoutError:
                return

    def run(self):
        env = dict(os.environ, LEAN_NUM_THREADS='1')
        self.p = subprocess.Popen([str(self.bin), '--server'], cwd=self.dir, env=env,
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.stderr_raw,
                                  start_new_session=True, bufsize=0)
        self.event('start', pid=self.p.pid, binary=str(self.bin), binary_sha256=sha(self.bin),
                   version_output=subprocess.check_output([str(self.bin), '--version'], text=True).strip(),
                   expected_commit=VERSIONS[self.version][1], preflight_free_percent=free_percent())
        mon = threading.Thread(target=self.monitor, daemon=True)
        mon.start()
        clean = False
        try:
            caps = {}
            if self.capability != 'absent':
                caps['lean'] = {'incrementalDiagnosticSupport': self.capability == 'true'}
            init = {'processId': os.getpid(), 'rootUri': self.dir.as_uri(), 'capabilities': caps,
                    'initializationOptions': {'hasWidgets': False}}
            self.request('initialize', init)
            self.send({'jsonrpc': '2.0', 'method': 'initialized', 'params': {}})
            uri = (self.dir / 'Probe.lean').as_uri()
            self.send({'jsonrpc': '2.0', 'method': 'textDocument/didOpen',
                       'params': {'textDocument': {'uri': uri, 'languageId': 'lean', 'version': 1,
                                                   'text': (FIX / 'Open.lean').read_text()}}})
            self.request('textDocument/waitForDiagnostics', {'uri': uri, 'version': 1})
            self.drain(.5)
            self.send({'jsonrpc': '2.0', 'method': 'textDocument/didChange',
                       'params': {'textDocument': {'uri': uri, 'version': 2},
                                  'contentChanges': [{'text': (FIX / 'Edited.lean').read_text()}]}})
            self.request('textDocument/waitForDiagnostics', {'uri': uri, 'version': 2})
            self.drain(.5)
            self.send({'jsonrpc': '2.0', 'method': 'textDocument/didClose',
                       'params': {'textDocument': {'uri': uri}}})
            self.drain(.25)
            self.request('shutdown', None, timeout=10)
            self.send({'jsonrpc': '2.0', 'method': 'exit', 'params': None})
            self.p.wait(timeout=10)
            clean = self.p.returncode == 0 and not group_rows(self.p.pid)
            self.event('stop', returncode=self.p.returncode, clean=clean, remaining_group_rows=group_rows(self.p.pid))
        except Exception as e:
            self.event('error', error=repr(e))
        finally:
            if self.p.poll() is None:
                os.killpg(self.p.pid, signal.SIGTERM)
                try:
                    self.p.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(self.p.pid, signal.SIGKILL)
                    self.p.wait(timeout=5)
                self.event('forced_stop', returncode=self.p.returncode)
            self.done.set()
            mon.join(timeout=2)
            self.stdout_raw.close()
            self.stderr_raw.close()
            (self.dir / 'events.jsonl').write_text(''.join(json.dumps(e, ensure_ascii=False) + '\n' for e in self.events))
            (self.dir / 'resources.jsonl').write_text(''.join(json.dumps(s) + '\n' for s in self.samples))
            (self.dir / 'summary.json').write_text(json.dumps({'label': self.label, 'clean': clean,
                'abort': self.abort, 'peak_rss_kib': max((s['rss_kib'] for s in self.samples), default=0),
                'minimum_free_percent': min((s['free_percent'] for s in self.samples if s['free_percent'] is not None), default=None),
                'event_count': len(self.events)}, indent=2) + '\n')
        if not clean or self.abort:
            raise RuntimeError(f'{self.label} did not shut down cleanly; stop probe')

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('version', choices=VERSIONS)
    ap.add_argument('capability', choices=['absent', 'false', 'true'])
    args = ap.parse_args()
    Case(args.version, args.capability).run()

if __name__ == '__main__':
    main()
