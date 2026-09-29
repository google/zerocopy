#!/usr/bin/env python3
"""Run the toy stdio task lifecycle against installed Lean LSP, without installs."""
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import select
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE / 'work'
SOURCE = 'import Lean\ntheorem checked (n : Nat) : n + 0 = n := by\n  skip\n'
SDK_NAMES = ('mcp', 'fastmcp', 'modelcontextprotocol')
EXEC_NAMES = ('lean-mcp', 'lean_mcp', 'leanmcp', 'mcp-lean', 'lean-server-mcp', 'lean-lsp-mcp')


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def inventory() -> dict:
    npm = subprocess.run(['npm', 'ls', '-g', '--depth=0', '--json'], capture_output=True, text=True, timeout=15)
    modules = {}
    for name in SDK_NAMES:
        spec = importlib.util.find_spec(name)
        modules[name] = spec.origin if spec is not None else None
    return {'python_executable': sys.executable, 'python_modules': modules,
            'npm_global_exit': npm.returncode,
            'npm_global_packages': sorted(json.loads(npm.stdout).get('dependencies', {})),
            'named_executables': {name: shutil.which(name) for name in EXEC_NAMES},
            'scope': 'active Python, global npm package list and named executables in current PATH; no machine-wide package search'}


class Client:
    def __init__(self, name: str):
        self.name = name
        self.p = subprocess.Popen([sys.executable, str(HERE / 'bridge.py'), 'stdio', str(ROOT)],
                                  cwd=ROOT, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, bufsize=0)
        self.buffer = b''
        self.log = []
        self.pending = {}
        self.next_id = 10

    def send(self, message: dict):
        raw = (json.dumps(message, separators=(',', ':'), ensure_ascii=False) + '\n').encode()
        self.p.stdin.write(raw)
        self.p.stdin.flush()
        self.log.append({'direction': 'client', 'message': message})

    def read(self, timeout=20):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            if b'\n' in self.buffer:
                line, self.buffer = self.buffer.split(b'\n', 1)
                message = json.loads(line)
                self.log.append({'direction': 'server', 'message': message})
                return message
            ready, _, _ = select.select([self.p.stdout], [], [], min(.1, max(0, end - time.monotonic())))
            if ready:
                data = os.read(self.p.stdout.fileno(), 65536)
                if not data:
                    break
                self.buffer += data
        raise TimeoutError(self.name + ' response')

    def until(self, identifier):
        if identifier in self.pending:
            return self.pending.pop(identifier)
        for _ in range(100):
            message = self.read()
            if message.get('id') == identifier:
                return message
            if 'id' in message:
                self.pending[message['id']] = message
        raise TimeoutError(self.name + ' request ' + str(identifier))

    def request(self, method: str, params: dict | None = None) -> dict:
        identifier = self.next_id
        self.next_id += 1
        self.send({'jsonrpc': '2.0', 'id': identifier, 'method': method, 'params': params or {}})
        return self.until(identifier)

    def tool(self, name: str, **arguments):
        return self.request('tools/call', {'name': name, 'arguments': arguments})

    def close(self) -> dict:
        self.p.stdin.close()
        self.p.wait(timeout=10)
        return {'bridge_pid': self.p.pid, 'bridge_exit': self.p.returncode,
                'bridge_stderr': self.p.stderr.read().decode(errors='replace')}


def poll(client: Client, handle: str, terminal: set[str], timeout=30) -> list[dict]:
    events = []
    end = time.monotonic() + timeout
    while time.monotonic() < end:
        result = client.tool('get_task', handle=handle)['result']
        events.append(result)
        if result['phase'] in terminal:
            return events
        time.sleep(.035)
    raise TimeoutError('task ' + handle)


def run() -> dict:
    if ROOT.exists():
        shutil.rmtree(ROOT)
    ROOT.mkdir()
    (ROOT / 'Proof.lean').write_text(SOURCE)
    digest = sha(SOURCE.encode())
    available = inventory()
    assert not any(available['python_modules'].values())
    assert not any(available['named_executables'].values())
    assert not any('mcp' in name.lower() for name in available['npm_global_packages'])
    assert available['npm_global_exit'] == 0

    a = Client('A')
    init_a = a.request('initialize', {'protocolVersion': 'toy-async-v2', 'capabilities': {'toyTasks': True}})
    list_a = a.request('tools/list')
    started = a.tool('start_goal', expected_sha256=digest, ttl_ms=2000)['result']
    handle = started['handle']
    awaiting = poll(a, handle, {'waiting'})
    pending = a.tool('result_task', handle=handle)['result']
    released = a.tool('release_task', handle=handle)['result']
    closed_a = a.close()  # Long-running worker remains, with no connected stdio client.

    c = Client('C-reconnected')
    init_c = c.request('initialize', {'protocolVersion': 'toy-async-v2'})
    recovered_poll = poll(c, handle, {'complete'})
    retrieved = c.tool('result_task', handle=handle)['result']
    task_state = json.loads((ROOT / 'tasks' / handle / 'state.json').read_text())
    sleep_for = max(0, task_state['expires_at'] - time.time()) + .08
    time.sleep(sleep_for)
    expired = c.tool('result_task', handle=handle)['result']

    cancelled_start = c.tool('start_goal', expected_sha256=digest, ttl_ms=2000)['result']
    cancel_handle = cancelled_start['handle']
    cancel_wait = poll(c, cancel_handle, {'waiting'})
    cancel_request = c.tool('cancel_task', handle=cancel_handle)['result']
    cancel_poll = poll(c, cancel_handle, {'cancelled'})
    cancel_result = c.tool('result_task', handle=cancel_handle)['result']

    failed_start = c.tool('start_goal', expected_sha256=digest, ttl_ms=2000, inject_failure=True)['result']
    failed_handle = failed_start['handle']
    failed_wait = poll(c, failed_handle, {'waiting'})
    c.tool('release_task', handle=failed_handle)
    failure_poll = poll(c, failed_handle, {'failed'})
    failure_result = c.tool('result_task', handle=failed_handle)['result']

    recovery_start = c.tool('start_goal', expected_sha256=digest, ttl_ms=4000)['result']
    recovery_handle = recovery_start['handle']
    recovery_wait = poll(c, recovery_handle, {'waiting'})
    c.tool('release_task', handle=recovery_handle)
    recovery_poll = poll(c, recovery_handle, {'complete'})
    recovery_result = c.tool('result_task', handle=recovery_handle)['result']
    closed_c = c.close()

    old = Client('legacy-fallback')
    init_old = old.request('initialize', {'protocolVersion': 'toy-unknown-request'})
    list_old = old.request('tools/list')
    rejected_async = old.tool('start_goal', expected_sha256=digest)
    sync = old.tool('goal_sync', expected_sha256=digest)['result']
    closed_old = old.close()

    traces = {'schema': 1, 'availability': available, 'lean_sha256': sha(Path(
        '/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean').read_bytes()),
        'fixture': {'text': SOURCE, 'sha256': digest},
        'negotiation': {'async': init_a, 'async_reconnect': init_c, 'async_tools': list_a,
                        'legacy': init_old, 'legacy_tools': list_old,
                        'legacy_rejected_async': rejected_async, 'legacy_sync': sync},
        'async_task': {'accepted': started, 'awaiting': awaiting, 'pending': pending,
                       'released': released, 'reconnect_poll': recovered_poll,
                       'retrieved': retrieved, 'expired': expired,
                       'disconnected_bridge': closed_a},
        'cancellation': {'accepted': cancelled_start, 'awaiting': cancel_wait,
                         'request': cancel_request, 'poll': cancel_poll, 'result': cancel_result},
        'partial_failure': {'accepted': failed_start, 'awaiting': failed_wait,
                            'poll': failure_poll, 'result': failure_result},
        'recovery': {'accepted': recovery_start, 'awaiting': recovery_wait,
                     'poll': recovery_poll, 'result': recovery_result},
        'client_transcripts': {'A': a.log, 'C': c.log, 'legacy': old.log},
        'processes': {'C': closed_c, 'legacy': closed_old},
        'task_states': {p.name: json.loads((p / 'state.json').read_text()) for p in sorted((ROOT / 'tasks').iterdir())},
        'boundary': 'Toy JSON-RPC stdio contract and durable task store over real Lean LSP; no MCP SDK, no existing adapter, no Anneal.'}
    (HERE / 'results.json').write_text(json.dumps(traces, indent=2, ensure_ascii=False) + '\n')
    return traces


if __name__ == '__main__':
    result = run()
    print(json.dumps({'tasks': len(result['task_states']),
                      'async_retrieved': result['async_task']['retrieved']['status'],
                      'expired': result['async_task']['expired']['status'],
                      'cancelled': result['cancellation']['result']['status'],
                      'failure': result['partial_failure']['result']['status'],
                      'recovery': result['recovery']['result']['status']}, indent=2))
