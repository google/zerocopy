import hashlib
import json
import os
import select
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LEAN = Path('$CHECKOUT/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
FILE = ROOT / 'Generated.lean'
V1 = 'theorem demo (n : Nat) (h : n = 0) : n + 0 = 0 := by\n  exact ?_\n'
V2 = 'theorem demo (n : Nat) (h : n = 0) : n + 0 = 0 := by\n  simpa using h\n'
FILE.write_text(V1)
events = []
def record(kind, data):
    events.append({'elapsed_ms': round((time.monotonic() - start) * 1000), 'kind': kind, 'data': data})

start = time.monotonic()
for label, source in [('v1', V1), ('v2', V2)]:
    FILE.write_text(source)
    p = subprocess.run([str(LEAN), '--json', str(FILE)], cwd=ROOT, capture_output=True, text=True, timeout=20)
    record('batch_' + label, {'argv': [str(LEAN), '--json', str(FILE)], 'returncode': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr, 'file_sha256': hashlib.sha256(source.encode()).hexdigest()})
FILE.write_text(V1)
log_dir = ROOT / 'server-logs'
log_dir.mkdir(exist_ok=True)
env = dict(os.environ, LEAN_SERVER_LOG_DIR=str(log_dir))
proc = subprocess.Popen([str(LEAN), '--server'], cwd=ROOT, env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
record('server_start', {'argv': [str(LEAN), '--server'], 'pid': proc.pid, 'cwd': str(ROOT)})
buf = b''
def send(msg):
    raw = json.dumps(msg, separators=(',', ':')).encode()
    proc.stdin.write(b'Content-Length: ' + str(len(raw)).encode() + b'\r\n\r\n' + raw)
    proc.stdin.flush()
    record('client', msg)

def receive_until(target, timeout=12):
    global buf
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        while b'\r\n\r\n' in buf:
            header, rest = buf.split(b'\r\n\r\n', 1)
            length = None
            for line in header.split(b'\r\n'):
                if line.lower().startswith(b'content-length:'):
                    length = int(line.split(b':', 1)[1])
            if length is None or len(rest) < length:
                break
            raw, buf = rest[:length], rest[length:]
            msg = json.loads(raw)
            record('server', msg)
            if msg.get('method') == 'client/registerCapability' and 'id' in msg:
                send({'jsonrpc': '2.0', 'id': msg['id'], 'result': None})
            if target(msg):
                return msg
        remain = max(0, deadline - time.monotonic())
        r, _, _ = select.select([proc.stdout], [], [], remain)
        if not r:
            break
        chunk = os.read(proc.stdout.fileno(), 65536)
        if not chunk:
            break
        buf += chunk
    raise TimeoutError(f'timeout waiting for {target}')

uri = FILE.as_uri()
try:
    send({'jsonrpc': '2.0', 'id': 1, 'method': 'initialize', 'params': {'processId': os.getpid(), 'rootUri': ROOT.as_uri(), 'capabilities': {}, 'initializationOptions': {'hasWidgets': False, 'logCfg': {'logDir': str(log_dir)}}}})
    receive_until(lambda m: m.get('id') == 1)
    send({'jsonrpc': '2.0', 'method': 'initialized', 'params': {}})
    send({'jsonrpc': '2.0', 'method': 'textDocument/didOpen', 'params': {'textDocument': {'uri': uri, 'languageId': 'lean', 'version': 1, 'text': V1}}})
    for ver, source in [(1, V1), (2, V2)]:
        if ver == 2:
            send({'jsonrpc': '2.0', 'method': 'textDocument/didChange', 'params': {'textDocument': {'uri': uri, 'version': ver}, 'contentChanges': [{'text': source}]}})
        send({'jsonrpc': '2.0', 'id': 10 + ver, 'method': 'textDocument/waitForDiagnostics', 'params': {'uri': uri, 'version': ver}})
        receive_until(lambda m: m.get('id') == 10 + ver)
        send({'jsonrpc': '2.0', 'id': 20 + ver, 'method': '$/lean/plainGoal', 'params': {'textDocument': {'uri': uri}, 'position': {'line': 1, 'character': 2}}})
        receive_until(lambda m: m.get('id') == 20 + ver)
        send({'jsonrpc': '2.0', 'id': 30 + ver, 'method': '$/lean/plainGoal', 'params': {'textDocument': {'uri': uri}, 'position': {'line': 1, 'character': len(source.splitlines()[1])}}})
        receive_until(lambda m: m.get('id') == 30 + ver)
    send({'jsonrpc': '2.0', 'id': 99, 'method': 'shutdown', 'params': None})
    receive_until(lambda m: m.get('id') == 99)
    send({'jsonrpc': '2.0', 'method': 'exit'})
except Exception as exc:
    record('exception', repr(exc))
finally:
    try:
        proc.wait(timeout=2)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait(timeout=2)
    record('server_exit', {'returncode': proc.returncode, 'stderr': proc.stderr.read().decode(errors='replace')})
    (ROOT / 'transcript.json').write_text(json.dumps(events, indent=2) + '\n')
