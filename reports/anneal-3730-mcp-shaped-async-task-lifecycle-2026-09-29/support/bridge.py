#!/usr/bin/env python3
"""Toy async JSON-RPC stdio task bridge to a real Lean LSP worker.

Not an MCP SDK, an existing adapter, or a claim of MCP conformance.
The durable task store and toy revision names are experimental policy.
"""
from __future__ import annotations

import hashlib
import json
import os
import select
import subprocess
import sys
import tempfile
import threading
import time
import uuid
from pathlib import Path

LEAN = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
ROOT = Path(sys.argv[2]).resolve()
SOURCE = ROOT / 'Proof.lean'
TASKS = ROOT / 'tasks'
OUT = threading.Lock()
WATCHERS = []


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def atomic_json(path: Path, obj: dict) -> None:
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix='.state-')
    try:
        with os.fdopen(fd, 'w') as f:
            json.dump(obj, f, indent=2, ensure_ascii=False)
            f.write('\n')
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


def state(handle: str) -> dict | None:
    if not isinstance(handle, str) or not handle.startswith('task-') or '/' in handle:
        return None
    path = TASKS / handle / 'state.json'
    try:
        return json.loads(path.read_text())
    except FileNotFoundError:
        return None


def emit(message: dict) -> None:
    with OUT:
        sys.stdout.write(json.dumps(message, ensure_ascii=False, separators=(',', ':')) + '\n')
        sys.stdout.flush()


def reply(identifier, result=None, error=None) -> None:
    message = {'jsonrpc': '2.0', 'id': identifier}
    if error is None:
        message['result'] = result
    else:
        message['error'] = error
    emit(message)


def watch(handle: str) -> None:
    last = None
    for _ in range(200):
        item = state(handle)
        if item is None:
            return
        phase = item['phase']
        if phase != last:
            emit({'jsonrpc': '2.0', 'method': 'notifications/progress',
                  'params': {'handle': handle, 'phase': phase, 'progressToken': handle}})
            last = phase
        if phase in ('complete', 'cancelled', 'failed'):
            return
        time.sleep(.025)


class LeanLSP:
    def __init__(self):
        env = dict(os.environ, ELAN_TOOLCHAIN='leanprover/lean4:v4.30.0-rc2', LEAN_NUM_THREADS='1', LEAN_PATH=str(ROOT))
        self.process = subprocess.Popen([str(LEAN), '--server'], cwd=ROOT, env=env,
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE, bufsize=0)
        self.buffer = b''
        self.diags = []
        self.send({'jsonrpc': '2.0', 'id': 1, 'method': 'initialize',
                   'params': {'processId': os.getpid(), 'rootUri': ROOT.as_uri(),
                              'capabilities': {}, 'initializationOptions': {'hasWidgets': False}}})
        self.until(1)
        self.send({'jsonrpc': '2.0', 'method': 'initialized', 'params': {}})

    def send(self, message):
        raw = json.dumps(message, separators=(',', ':'), ensure_ascii=False).encode()
        self.process.stdin.write(b'Content-Length: ' + str(len(raw)).encode() + b'\r\n\r\n' + raw)
        self.process.stdin.flush()

    def read(self, timeout=15):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            if b'\r\n\r\n' in self.buffer:
                header, body = self.buffer.split(b'\r\n\r\n', 1)
                sizes = [int(x.split(b':', 1)[1]) for x in header.split(b'\r\n')
                         if x.lower().startswith(b'content-length:')]
                if sizes and len(body) >= sizes[0]:
                    raw, self.buffer = body[:sizes[0]], body[sizes[0]:]
                    message = json.loads(raw)
                    if message.get('method') == 'textDocument/publishDiagnostics':
                        self.diags.append(message['params'])
                    if 'method' in message and 'id' in message:
                        self.send({'jsonrpc': '2.0', 'id': message['id'], 'result': None})
                    return message
            ready, _, _ = select.select([self.process.stdout], [], [], min(.1, max(0, end - time.monotonic())))
            if ready:
                data = os.read(self.process.stdout.fileno(), 65536)
                if not data:
                    break
                self.buffer += data
        raise TimeoutError('Lean LSP response')

    def until(self, identifier):
        for _ in range(100):
            message = self.read()
            if message.get('id') == identifier and 'method' not in message:
                return message
        raise TimeoutError(f'Lean LSP id {identifier}')

    def query(self, source: str) -> dict:
        uri = SOURCE.as_uri()
        self.send({'jsonrpc': '2.0', 'method': 'textDocument/didOpen',
                   'params': {'textDocument': {'uri': uri, 'languageId': 'lean', 'version': 1, 'text': source}}})
        self.send({'jsonrpc': '2.0', 'id': 2, 'method': 'textDocument/waitForDiagnostics',
                   'params': {'uri': uri, 'version': 1}})
        waited = self.until(2)
        self.send({'jsonrpc': '2.0', 'id': 3, 'method': '$/lean/plainGoal',
                   'params': {'textDocument': {'uri': uri}, 'position': {'line': 2, 'character': 4}}})
        goal = self.until(3)
        diagnostics = [d for d in self.diags if d.get('version') == 1]
        return {'lsp_pid': self.process.pid, 'wait': waited, 'goal': goal,
                'diagnostics': diagnostics[-1] if diagnostics else None}

    def close(self):
        if self.process.poll() is None:
            try:
                self.send({'jsonrpc': '2.0', 'id': 4, 'method': 'shutdown', 'params': None})
                self.until(4)
                self.send({'jsonrpc': '2.0', 'method': 'exit'})
                self.process.wait(timeout=3)
            except Exception:
                self.process.kill()
                self.process.wait()
        return self.process.returncode


def worker(handle: str) -> None:
    directory = TASKS / handle
    path = directory / 'state.json'
    item = state(handle)
    assert item is not None
    item['phase'] = 'waiting'
    atomic_json(path, item)
    for _ in range(300):
        if (directory / 'cancel').exists():
            item['phase'] = 'cancelled'
            atomic_json(path, item)
            return
        if (directory / 'release').exists():
            break
        time.sleep(.02)
    else:
        item['phase'] = 'failed'
        item['error'] = 'gate timeout'
        atomic_json(path, item)
        return
    item['phase'] = 'checking'
    atomic_json(path, item)
    lsp = None
    try:
        if (directory / 'cancel').exists():
            item['phase'] = 'cancelled'
            atomic_json(path, item)
            return
        lsp = LeanLSP()
        observed = lsp.query((directory / 'source.lean').read_text())
        item['partial'] = {'lsp_pid': observed['lsp_pid'], 'goal_observed': 'result' in observed['goal']}
        if item['inject_failure']:
            raise RuntimeError('injected failure after Lean goal before result publication')
        if (directory / 'cancel').exists():
            item['phase'] = 'cancelled'
            atomic_json(path, item)
            return
        item['result'] = observed
        item['phase'] = 'complete'
        item['completed_at'] = time.time()
        item['expires_at'] = item['completed_at'] + item['ttl_ms'] / 1000
        atomic_json(path, item)
    except Exception as error:
        item['phase'] = 'failed'
        item['error'] = str(error)
        atomic_json(path, item)
    finally:
        if lsp is not None:
            item['lsp_exit'] = lsp.close()
            atomic_json(path, item)


def stdio() -> None:
    revision = None
    TASKS.mkdir(parents=True, exist_ok=True)
    for line in sys.stdin:
        if not line.strip():
            continue
        try:
            message = json.loads(line)
        except ValueError:
            continue
        identifier = message.get('id')
        if identifier is None:
            continue
        method = message.get('method')
        params = message.get('params') or {}
        if method == 'initialize':
            requested = params.get('protocolVersion')
            revision = 'toy-async-v2' if requested == 'toy-async-v2' else 'toy-sync-v1'
            reply(identifier, {'protocolVersion': revision,
                               'capabilities': {'toyTasks': revision == 'toy-async-v2'},
                               'serverInfo': {'name': 'synthetic-lean-task-bridge', 'version': '0'}})
            continue
        if revision is None:
            reply(identifier, error={'code': -32000, 'message': 'initialize first'})
            continue
        if method == 'tools/list':
            reply(identifier, {'tools': [{'name': 'start_goal'}, {'name': 'get_task'},
                                         {'name': 'result_task'}, {'name': 'cancel_task'},
                                         {'name': 'release_task'}] if revision == 'toy-async-v2'
                               else [{'name': 'goal_sync'}]})
            continue
        if method != 'tools/call':
            reply(identifier, error={'code': -32601, 'message': 'unknown toy method'})
            continue
        name = params.get('name')
        args = params.get('arguments') or {}
        if revision == 'toy-sync-v1':
            if name == 'goal_sync':
                raw = SOURCE.read_bytes()
                if args.get('expected_sha256') != sha(raw):
                    reply(identifier, {'status': 'stale', 'source_sha256': sha(raw)})
                    continue
                lsp = LeanLSP()
                try:
                    observed = lsp.query(raw.decode())
                finally:
                    lsp.close()
                reply(identifier, {'status': 'complete', 'result': observed})
            else:
                reply(identifier, error={'code': -32602, 'message': 'async tool unsupported by negotiated revision'})
            continue
        if name == 'start_goal':
            raw = SOURCE.read_bytes()
            if args.get('expected_sha256') != sha(raw):
                reply(identifier, {'status': 'stale', 'source_sha256': sha(raw)})
                continue
            handle = 'task-' + uuid.uuid4().hex
            directory = TASKS / handle
            directory.mkdir()
            (directory / 'source.lean').write_bytes(raw)
            item = {'handle': handle, 'phase': 'queued', 'source_sha256': sha(raw),
                    'ttl_ms': int(args.get('ttl_ms', 1000)),
                    'inject_failure': bool(args.get('inject_failure', False))}
            atomic_json(directory / 'state.json', item)
            child = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), 'worker', str(ROOT), handle],
                                     cwd=ROOT, stdin=subprocess.DEVNULL,
                                     stdout=(directory / 'worker.stdout').open('wb'),
                                     stderr=(directory / 'worker.stderr').open('wb'), start_new_session=True)
            item['worker_pid'] = child.pid
            # Worker may already advance; this metadata is advisory only.
            (directory / 'worker.pid').write_text(str(child.pid) + '\n')
            reply(identifier, {'status': 'accepted', 'handle': handle, 'progressToken': handle})
            watcher = threading.Thread(target=watch, args=(handle,), daemon=True)
            WATCHERS.append(watcher)
            watcher.start()
        elif name in ('get_task', 'result_task', 'cancel_task', 'release_task'):
            handle = args.get('handle')
            item = state(handle)
            if item is None:
                reply(identifier, error={'code': -32602, 'message': 'unknown handle'})
                continue
            directory = TASKS / handle
            if name == 'cancel_task':
                (directory / 'cancel').touch()
                reply(identifier, {'status': 'cancel_requested', 'handle': handle})
            elif name == 'release_task':
                (directory / 'release').touch()
                reply(identifier, {'status': 'released', 'handle': handle})
            elif name == 'get_task':
                reply(identifier, {k: item.get(k) for k in ('handle', 'phase', 'source_sha256', 'partial', 'error')})
            elif name == 'result_task':
                if item['phase'] == 'complete' and time.time() >= item['expires_at']:
                    reply(identifier, {'status': 'expired', 'handle': handle})
                elif item['phase'] == 'complete':
                    reply(identifier, {'status': 'complete', 'handle': handle,
                                       'source_sha256': item['source_sha256'], 'result': item['result']})
                elif item['phase'] == 'failed':
                    reply(identifier, {'status': 'failed', 'handle': handle,
                                       'error': item.get('error'), 'partial': item.get('partial')})
                else:
                    reply(identifier, {'status': item['phase'], 'handle': handle})
        else:
            reply(identifier, error={'code': -32602, 'message': 'unknown toy tool'})


if __name__ == '__main__':
    assert LEAN.is_file() and SOURCE.is_file()
    if sys.argv[1] == 'stdio':
        stdio()
    elif sys.argv[1] == 'worker':
        worker(sys.argv[3])
