#!/usr/bin/env python3
"""Tiny direct Lean LSP import after unlink; no Anneal or GC lease implied."""
import hashlib
import json
import os
from pathlib import Path
import select
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
LEAN = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
TIMEOUT = 18

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

class Server:
    def __init__(self, root, env):
        self.root = root
        self.process = subprocess.Popen([str(LEAN), '--server'], cwd=root, env=env,
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE, bufsize=0)
        self.buffer = b''
        self.messages = []
        self.next_id = 1
        self.send('initialize', {'processId': os.getpid(), 'rootUri': root.as_uri(),
                                 'capabilities': {}, 'initializationOptions': {'hasWidgets': False}}, request=True)
        self.receive_reply(1)
        self.send('initialized', {})

    def send(self, method, params, request=False):
        msg = {'jsonrpc': '2.0', 'method': method, 'params': params}
        if request:
            msg['id'] = self.next_id
            self.next_id += 1
        body = json.dumps(msg, separators=(',', ':')).encode()
        self.process.stdin.write(b'Content-Length: ' + str(len(body)).encode() + b'\r\n\r\n' + body)
        self.process.stdin.flush()
        self.messages.append({'direction': 'client', 'message': msg})
        return msg.get('id')

    def read(self, timeout=TIMEOUT):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if b'\r\n\r\n' in self.buffer:
                header, body = self.buffer.split(b'\r\n\r\n', 1)
                lengths = [int(line.split(b':',1)[1]) for line in header.split(b'\r\n')
                           if line.lower().startswith(b'content-length:')]
                if lengths and len(body) >= lengths[0]:
                    raw, self.buffer = body[:lengths[0]], body[lengths[0]:]
                    msg = json.loads(raw)
                    self.messages.append({'direction': 'server', 'message': msg})
                    if 'method' in msg and 'id' in msg:
                        reply = {'jsonrpc': '2.0', 'id': msg['id'], 'result': None}
                        self.send_raw(reply)
                    return msg
            readable, _, _ = select.select([self.process.stdout], [], [], min(.1, deadline-time.monotonic()))
            if readable:
                data = os.read(self.process.stdout.fileno(), 65536)
                if not data:
                    raise EOFError('Lean server closed stdout')
                self.buffer += data
        raise TimeoutError('Lean LSP read deadline')

    def send_raw(self, msg):
        body = json.dumps(msg, separators=(',', ':')).encode()
        self.process.stdin.write(b'Content-Length: ' + str(len(body)).encode() + b'\r\n\r\n' + body)
        self.process.stdin.flush()
        self.messages.append({'direction': 'client', 'message': msg})

    def receive_reply(self, request_id):
        for _ in range(120):
            msg = self.read()
            if msg.get('id') == request_id and 'method' not in msg:
                return msg
        raise TimeoutError(f'no response {request_id}')

    def open_and_query(self, filename, text):
        uri = (self.root / filename).as_uri()
        self.send('textDocument/didOpen', {'textDocument': {'uri': uri, 'languageId': 'lean', 'version': 1, 'text': text}})
        wait = self.send('textDocument/waitForDiagnostics', {'uri': uri, 'version': 1}, request=True)
        self.receive_reply(wait)
        goal = self.send('$/lean/plainGoal', {'textDocument': {'uri': uri}, 'position': {'line': 2, 'character': 2}}, request=True)
        answer = self.receive_reply(goal)
        diagnostics = [r['message']['params'] for r in self.messages
                       if r['direction']=='server' and r['message'].get('method')=='textDocument/publishDiagnostics'
                       and r['message'].get('params',{}).get('uri')==uri]
        return {'goal': answer, 'diagnostics': diagnostics}

    def query(self, filename):
        uri = (self.root / filename).as_uri()
        goal = self.send('$/lean/plainGoal', {'textDocument': {'uri': uri}, 'position': {'line': 2, 'character': 2}}, request=True)
        return self.receive_reply(goal)

    def close(self):
        if self.process.poll() is None:
            try:
                request = self.send('shutdown', None, request=True)
                self.receive_reply(request)
                self.send('exit', None)
                self.process.wait(timeout=3)
            except Exception:
                self.process.kill()
                self.process.wait(timeout=3)
        stderr = self.process.stderr.read().decode(errors='replace')
        return {'exit': self.process.returncode, 'stderr': stderr, 'messages': self.messages}

def main():
    if not LEAN.exists():
        raise RuntimeError('cached Lean pin absent')
    scratch = Path(os.environ.get('ANNEAL_PROBE_SCRATCH', tempfile.gettempdir()))
    with tempfile.TemporaryDirectory(prefix='anneal-live-olean-', dir=scratch) as temp:
        root = Path(temp)
        (root/'Dep.lean').write_text('def depValue : Nat := 7\n')
        source = 'import Dep\ntheorem selected : depValue = 7 := by\n  decide\n'
        (root/'Proof.lean').write_text(source)
        (root/'Second.lean').write_text(source.replace('selected', 'second'))
        env = dict(os.environ, LEAN_PATH=str(root), LEAN_NUM_THREADS='1')
        build = subprocess.run([str(LEAN), '-o', 'Dep.olean', 'Dep.lean'], cwd=root, env=env,
                               text=True, capture_output=True, timeout=TIMEOUT)
        assert build.returncode == 0, build.stderr
        olean = root/'Dep.olean'
        original_hash = sha(olean)
        batch_before = subprocess.run([str(LEAN), '--json', 'Proof.lean'],cwd=root,env=env,
                                      text=True,capture_output=True,timeout=TIMEOUT)
        assert batch_before.returncode == 0, batch_before.stdout
        first_server = Server(root, env)
        try:
            first = first_server.open_and_query('Proof.lean', source)
            olean.unlink()
            same_document_after_unlink = first_server.query('Proof.lean')
            second_document_after_unlink = first_server.open_and_query('Second.lean', source.replace('selected','second'))
        finally:
            first_trace = first_server.close()
        batch_missing = subprocess.run([str(LEAN), '--json', 'Proof.lean'],cwd=root,env=env,
                                       text=True,capture_output=True,timeout=TIMEOUT)
        fresh_server = Server(root, env)
        try:
            fresh_missing = fresh_server.open_and_query('Proof.lean', source)
        finally:
            fresh_trace = fresh_server.close()
        rebuild = subprocess.run([str(LEAN), '-o', 'Dep.olean', 'Dep.lean'],cwd=root,env=env,
                                 text=True,capture_output=True,timeout=TIMEOUT)
        assert rebuild.returncode == 0
        batch_restored = subprocess.run([str(LEAN), '--json', 'Proof.lean'],cwd=root,env=env,
                                        text=True,capture_output=True,timeout=TIMEOUT)
        result = {
            'pin': {'lean_sha256': sha(LEAN), 'lean_version': subprocess.run([str(LEAN),'--version'],capture_output=True,text=True).stdout.strip()},
            'artifact_sha256_before': original_hash,
            'artifact_sha256_restored': sha(olean),
            'batch_before': {'exit':batch_before.returncode,'stdout':batch_before.stdout,'stderr':batch_before.stderr},
            'live_initial': first,
            'live_same_after_unlink': same_document_after_unlink,
            'live_second_after_unlink': second_document_after_unlink,
            'batch_missing': {'exit':batch_missing.returncode,'stdout':batch_missing.stdout,'stderr':batch_missing.stderr},
            'fresh_missing': fresh_missing,
            'batch_restored': {'exit':batch_restored.returncode,'stdout':batch_restored.stdout,'stderr':batch_restored.stderr},
            'first_server': first_trace,
            'fresh_server': fresh_trace,
        }
    (HERE/'results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'batch_exits':[batch_before.returncode,batch_missing.returncode,batch_restored.returncode],
                      'live_initial':first['goal'].get('result'),
                      'live_same_after_unlink':same_document_after_unlink.get('result'),
                      'live_second_after_unlink':second_document_after_unlink['goal'].get('result'),
                      'fresh_missing':fresh_missing['goal'].get('result')},indent=2))

if __name__ == '__main__':
    main()
