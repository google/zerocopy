import hashlib
import json
import os
import select
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LEAN = Path('$CHECKOUT/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
SOURCES = {
    'a1': 'import Dep\ntheorem demo (n : Nat) (h : n = 1) : n + sharedValue = 1 + sharedValue := by\n  exact ?_\n',
    'a2': 'import Dep\ntheorem demo (n : Nat) (h : n = 1) : n + sharedValue = 1 + sharedValue := by\n  exact congrArg (fun x => x + sharedValue) h\n',
    'b1': 'import Dep\ntheorem demo (n : Nat) (h : n = 2) : n + sharedValue = 2 + sharedValue := by\n  exact ?_\n',
}
EVENTS = []
START = time.monotonic()
SERVERS = []

def record(kind, **data):
    EVENTS.append({'elapsed_ms': round((time.monotonic() - START) * 1000), 'kind': kind, **data})

def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()

def sample_memory():
    # Process enumeration is blocked in this sandbox (`ps` and `top` return EPERM).
    # Do not claim an RSS observation from this run.
    pass

class Server:
    def __init__(self, label, source):
        self.label = label
        self.root = ROOT / label
        self.root.mkdir(exist_ok=True)
        self.file = self.root / 'Proof.lean'
        self.file.write_text(source)
        self.buf = b''
        self.started = time.monotonic()
        self.next_id = 1
        env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(ROOT / 'shared'))
        self.p = subprocess.Popen([str(LEAN), '--server'], cwd=self.root, env=env,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
        SERVERS.append(self)
        record('start', server=label, pid=self.p.pid, argv=[str(LEAN), '--server'],
            cwd=str(self.root), env={'LEAN_NUM_THREADS': '1', 'LEAN_PATH': str(ROOT / 'shared')}, disk_sha256=sha(source))
        self.request('initialize', {'processId': os.getpid(), 'rootUri': self.root.as_uri(),
            'capabilities': {}, 'initializationOptions': {'hasWidgets': False}})
        self.send({'jsonrpc': '2.0', 'method': 'initialized', 'params': {}})
        self.send({'jsonrpc': '2.0', 'method': 'textDocument/didOpen', 'params': {
            'textDocument': {'uri': self.file.as_uri(), 'languageId': 'lean', 'version': 1, 'text': source}}})

    def send(self, msg):
        raw = json.dumps(msg, separators=(',', ':')).encode()
        self.p.stdin.write(b'Content-Length: ' + str(len(raw)).encode() + b'\r\n\r\n' + raw)
        self.p.stdin.flush()
        record('client', server=self.label, message=msg)

    def recv_until(self, predicate, limit=10):
        deadline = min(self.started + 29, time.monotonic() + limit)
        while time.monotonic() < deadline:
            sample_memory()
            while b'\r\n\r\n' in self.buf:
                header, body = self.buf.split(b'\r\n\r\n', 1)
                lengths = [int(x.split(b':', 1)[1]) for x in header.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if not lengths or len(body) < lengths[0]:
                    break
                raw, self.buf = body[:lengths[0]], body[lengths[0]:]
                msg = json.loads(raw)
                record('server', server=self.label, message=msg)
                if msg.get('method') == 'client/registerCapability' and 'id' in msg:
                    self.send({'jsonrpc': '2.0', 'id': msg['id'], 'result': None})
                if predicate(msg):
                    return msg
            ready, _, _ = select.select([self.p.stdout], [], [], min(0.2, max(0, deadline-time.monotonic())))
            if ready:
                chunk = os.read(self.p.stdout.fileno(), 65536)
                if not chunk:
                    break
                self.buf += chunk
        raise TimeoutError(f'{self.label}: no matching response before deadline')

    def request(self, method, params, limit=10):
        rid = self.next_id
        self.next_id += 1
        self.send({'jsonrpc': '2.0', 'id': rid, 'method': method, 'params': params})
        return self.recv_until(lambda m: m.get('id') == rid, limit)

    def settled(self, version):
        return self.request('textDocument/waitForDiagnostics', {'uri': self.file.as_uri(), 'version': version})

    def goal(self):
        return self.request('$/lean/plainGoal', {'textDocument': {'uri': self.file.as_uri()},
            'position': {'line': 2, 'character': 2}})

    def stop(self):
        if self.p.poll() is None:
            try:
                self.request('shutdown', None, limit=2)
                self.send({'jsonrpc': '2.0', 'method': 'exit'})
                self.p.wait(timeout=2)
            except Exception as exc:
                record('stop_exception', server=self.label, error=repr(exc))
                self.p.kill()
                self.p.wait(timeout=2)
        record('exit', server=self.label, returncode=self.p.returncode,
            wall_ms=round((time.monotonic()-self.started)*1000), stderr=self.p.stderr.read().decode(errors='replace'))

def main():
    shared = ROOT / 'shared'
    shared.mkdir(exist_ok=True)
    dep = shared / 'Dep.lean'
    dep.write_text('def sharedValue : Nat := 3\n')
    artifact = shared / 'Dep.olean'
    argv = [str(LEAN), '-o', str(artifact), str(dep)]
    p = subprocess.run(argv, cwd=shared, capture_output=True, text=True, timeout=20,
        env=dict(os.environ, LEAN_NUM_THREADS='1'))
    record('build_shared', argv=argv, cwd=str(shared), returncode=p.returncode,
        stdout=p.stdout, stderr=p.stderr, source_sha256=sha(dep.read_text()))
    if p.returncode:
        raise RuntimeError('shared dependency build failed')
    artifact.chmod(0o444)
    shared_before = hashlib.sha256(artifact.read_bytes()).hexdigest()
    record('shared_artifact', path=str(artifact), sha256=shared_before,
        bytes=artifact.stat().st_size, mode=oct(artifact.stat().st_mode & 0o777))
    for label, source in SOURCES.items():
        root = ROOT / label
        root.mkdir(exist_ok=True)
        f = root / 'Proof.lean'
        f.write_text(source)
        argv = [str(LEAN), '--json', str(f)]
        p = subprocess.run(argv, cwd=root, capture_output=True, text=True, timeout=20,
            env=dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(shared)))
        record('batch', label=label, argv=argv, cwd=str(root), file_sha256=sha(source),
            returncode=p.returncode, stdout=p.stdout, stderr=p.stderr)
    a = Server('a1', SOURCES['a1'])
    b = Server('b1', SOURCES['b1'])
    for s in (a, b):
        s.settled(1)
        s.goal()
    a.send({'jsonrpc': '2.0', 'method': 'textDocument/didChange', 'params': {
        'textDocument': {'uri': a.file.as_uri(), 'version': 2},
        'contentChanges': [{'text': SOURCES['a2']}]}})
    a.settled(2)
    a.goal()
    a.request('$/lean/plainGoal', {'textDocument': {'uri': a.file.as_uri()},
        'position': {'line': 2, 'character': len(SOURCES['a2'].splitlines()[2])}})
    b.goal()
    # An intentionally racy cancellation specimen; the protocol records which outcome won.
    rid = b.next_id
    b.next_id += 1
    b.send({'jsonrpc': '2.0', 'id': rid, 'method': '$/lean/plainGoal', 'params': {
        'textDocument': {'uri': b.file.as_uri()}, 'position': {'line': 2, 'character': 2}}})
    b.send({'jsonrpc': '2.0', 'method': '$/cancelRequest', 'params': {'id': rid}})
    try:
        b.recv_until(lambda m: m.get('id') == rid, limit=2)
    except TimeoutError:
        record('cancel_no_response_within_2s', server='b1', request_id=rid)
    a.send({'jsonrpc': '2.0', 'method': 'textDocument/didClose',
        'params': {'textDocument': {'uri': a.file.as_uri()}}})
    a.send({'jsonrpc': '2.0', 'method': 'textDocument/didOpen', 'params': {
        'textDocument': {'uri': a.file.as_uri(), 'languageId': 'lean', 'version': 3, 'text': SOURCES['a1']}}})
    a.settled(3)
    a.goal()
    # Simulate watchdog loss, reconstruct from explicit desired text in a new process.
    a.p.kill()
    a.p.wait(timeout=2)
    record('intentional_kill', server='a1', pid=a.p.pid, returncode=a.p.returncode)
    a.stop()
    restarted = Server('a1', SOURCES['a1'])
    restarted.settled(1)
    restarted.goal()
    restarted.stop()
    b.stop()
    record('shared_artifact_after', sha256=hashlib.sha256(artifact.read_bytes()).hexdigest(),
        same_bytes=hashlib.sha256(artifact.read_bytes()).hexdigest() == shared_before)

try:
    main()
except Exception as exc:
    record('exception', error=repr(exc))
finally:
    for server in SERVERS:
        if server.p.poll() is None:
            server.p.kill()
            server.p.wait(timeout=2)
            record('forced_exit', server=server.label, pid=server.p.pid)
    record('summary', memory_measurement='unavailable: ps/top EPERM in this sandbox')
    (ROOT / 'transcript.json').write_text(json.dumps(EVENTS, indent=2) + '\n')
