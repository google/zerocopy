#!/usr/bin/env python3
"""Bounded direct Lean LSP cancellation and independent Cargo process-group control."""
import hashlib
import json
import os
import re
import select
import shutil
import signal
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
WORK = ROOT / 'work'
LEAN = Path(os.environ['LEAN_BIN']).resolve()
CARGO = Path(os.environ.get('CARGO_BIN', shutil.which('cargo'))).resolve()
EVENTS = []
START = time.monotonic()

def log(kind, **fields):
    EVENTS.append({'kind':kind, 'seconds':round(time.monotonic()-START, 4), **fields})

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def prows(group):
    output = subprocess.check_output(['ps', '-axo', 'pid=,ppid=,pgid=,comm='], text=True)
    rows = []
    for line in output.splitlines():
        fields = line.split(maxsplit=3)
        if len(fields) == 4 and fields[2].isdigit() and int(fields[2]) == group:
            rows.append({'pid':int(fields[0]), 'ppid':int(fields[1]), 'pgid':int(fields[2]), 'command':fields[3]})
    return rows

def free_memory():
    out = subprocess.check_output(['memory_pressure', '-Q'], text=True, timeout=5)
    match = re.search(r'System-wide memory free percentage: (\d+)%', out)
    return int(match.group(1)) if match else None

class Server:
    def __init__(self, root):
        self.root = root
        self.buf = b''
        self.seq = 0
        self.proc = subprocess.Popen([str(LEAN), '--server'], cwd=root,
            env=dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(root)),
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            bufsize=0, start_new_session=True)
        log('lean_start', pid=self.proc.pid, argv=[str(LEAN), '--server'])
        self.request('initialize', {'processId':os.getpid(), 'rootUri':root.as_uri(),
            'capabilities':{}, 'initializationOptions':{'hasWidgets':False}}, timeout=10)
        self.send({'jsonrpc':'2.0', 'method':'initialized', 'params':{}})

    def send(self, msg):
        raw = json.dumps(msg, separators=(',',':')).encode()
        self.proc.stdin.write(b'Content-Length: ' + str(len(raw)).encode() + b'\r\n\r\n' + raw)
        self.proc.stdin.flush()
        log('client_message', message=msg)

    def receive(self, predicate, timeout=25):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            while b'\r\n\r\n' in self.buf:
                header, body = self.buf.split(b'\r\n\r\n', 1)
                sizes = [int(x.split(b':', 1)[1]) for x in header.split(b'\r\n')
                         if x.lower().startswith(b'content-length:')]
                if not sizes or len(body) < sizes[0]:
                    break
                raw, self.buf = body[:sizes[0]], body[sizes[0]:]
                msg = json.loads(raw)
                log('server_message', message=msg)
                if 'method' in msg and 'id' in msg:
                    self.send({'jsonrpc':'2.0', 'id':msg['id'], 'result':None})
                if predicate(msg):
                    return msg
            ready, _, _ = select.select([self.proc.stdout], [], [], min(0.1, max(0,end-time.monotonic())))
            if ready:
                part = os.read(self.proc.stdout.fileno(), 65536)
                if not part:
                    raise RuntimeError('Lean server closed stdout')
                self.buf += part
        raise TimeoutError('Lean LSP response deadline')

    def start_request(self, method, params):
        self.seq += 1
        self.send({'jsonrpc':'2.0', 'id':self.seq, 'method':method, 'params':params})
        return self.seq

    def request(self, method, params, timeout=25):
        rid = self.start_request(method, params)
        return self.receive(lambda m: 'method' not in m and m.get('id') == rid, timeout)

    def stop(self):
        if self.proc.poll() is None:
            try:
                self.request('shutdown', None, timeout=5)
                self.send({'jsonrpc':'2.0', 'method':'exit'})
                self.proc.wait(timeout=5)
            except Exception as exc:
                log('lean_shutdown_fallback', error=repr(exc))
                os.killpg(self.proc.pid, signal.SIGKILL)
                self.proc.wait(timeout=5)
        log('lean_exit', pid=self.proc.pid, returncode=self.proc.returncode,
            stderr=self.proc.stderr.read().decode(errors='replace'), group_after=prows(self.proc.pid))

def lean_cell():
    root = WORK / 'lean'
    root.mkdir()
    source = ('import Lean\nopen Lean Elab Tactic\nelab "pause" : tactic => do\n'
              '  IO.sleep 3000\n  evalTactic (← `(tactic| trivial))\n'
              'theorem slow : True := by\n  pause\n')
    path = root / 'Slow.lean'
    path.write_text(source)
    srv = Server(root)
    try:
        uri = path.as_uri()
        srv.send({'jsonrpc':'2.0', 'method':'textDocument/didOpen', 'params':{
            'textDocument':{'uri':uri, 'languageId':'lean', 'version':1, 'text':source}}})
        # This request waits for the delayed tactic; the cancel follows after a bounded
        # dispatch interval, while the document stays open and its file worker is alive.
        rid = srv.start_request('textDocument/waitForDiagnostics', {'uri':uri, 'version':1})
        time.sleep(0.35)
        before = prows(srv.proc.pid)
        srv.send({'jsonrpc':'2.0', 'method':'$/cancelRequest', 'params':{'id':rid}})
        cancelled = srv.receive(lambda m: 'method' not in m and m.get('id') == rid, timeout=25)
        after = srv.request('textDocument/waitForDiagnostics', {'uri':uri, 'version':1}, timeout=25)
        batch = subprocess.run([str(LEAN), '--json', str(path)], cwd=root,
            env=dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(root)),
            capture_output=True, text=True, timeout=25)
        log('lean_batch', returncode=batch.returncode, stdout=batch.stdout, stderr=batch.stderr)
        return {'source_sha256':sha(path), 'request_id':rid, 'cancel_response':cancelled,
                'later_wait_response':after, 'group_at_cancel':before,
                'batch_returncode':batch.returncode, 'batch_stdout':batch.stdout,
                'batch_stderr':batch.stderr}
    finally:
        srv.stop()

def cargo_fixture(root):
    root.mkdir()
    (root/'src').mkdir()
    (root/'Cargo.toml').write_text('[package]\nname = "cancel_probe"\nversion = "0.1.0"\nedition = "2021"\nbuild = "build.rs"\n')
    (root/'src'/'lib.rs').write_text('pub fn answer() -> u32 { 42 }\n')
    (root/'build.rs').write_text('''use std::{env, fs, process::{self, Command}};
fn main() {
    let root = env::var("CARGO_MANIFEST_DIR").unwrap();
    let mut child = Command::new("/bin/sleep").arg("5").spawn().unwrap();
    fs::write(format!("{root}/entered"), format!("{} {}\\n", process::id(), child.id())).unwrap();
    assert!(child.wait().unwrap().success());
    println!("cargo:rerun-if-changed=build.rs");
}
''')

def wait_marker(path, processes, timeout=20):
    end = time.monotonic()+timeout
    while time.monotonic()<end:
        if path.exists():
            return path.read_text().strip()
        if any(p.poll() is not None for p in processes):
            raise RuntimeError('Cargo process exited before marker')
        time.sleep(0.05)
    raise TimeoutError('Cargo build-script marker')

def cargo_cell():
    a = WORK/'cargo-victim'; b = WORK/'cargo-peer'
    cargo_fixture(a); cargo_fixture(b)
    env = dict(os.environ, CARGO_NET_OFFLINE='true', CARGO_BUILD_JOBS='1')
    command = [str(CARGO), 'build', '--offline', '--target-dir']
    processes = []
    try:
        victim = subprocess.Popen(command+[str(a/'target')], cwd=a, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
        processes.append(victim)
        victim_marker = wait_marker(a/'entered', [victim])
        peer = subprocess.Popen(command+[str(b/'target')], cwd=b, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
        processes.append(peer)
        peer_marker = wait_marker(b/'entered', [peer])
        before = {'victim':prows(victim.pid), 'peer':prows(peer.pid)}
        os.killpg(victim.pid, signal.SIGTERM)
        vout, verr = victim.communicate(timeout=8)
        peer_after_victim_cancel = {'poll':peer.poll(), 'group':prows(peer.pid)}
        pout, perr = peer.communicate(timeout=15)
        time.sleep(0.15)
        after = {'victim':prows(victim.pid), 'peer':prows(peer.pid)}
        victim_artifact_after_cancel = (a/'target'/'debug'/'libcancel_probe.rlib').exists()
        peer_artifact_after_completion = (b/'target'/'debug'/'libcancel_probe.rlib').exists()
        retry = subprocess.run(command+[str(a/'target')], cwd=a, env=env,
            capture_output=True, text=True, timeout=20)
        log('cargo_stage', victim_pid=victim.pid, peer_pid=peer.pid,
            victim_marker=victim_marker, peer_marker=peer_marker,
            before=before, after=after, peer_after_victim_cancel=peer_after_victim_cancel,
            victim_artifact_after_cancel=victim_artifact_after_cancel,
            peer_artifact_after_completion=peer_artifact_after_completion,
            victim_exit=victim.returncode,
            peer_exit=peer.returncode, retry_exit=retry.returncode,
            victim_stdout=vout, victim_stderr=verr, peer_stdout=pout,
            peer_stderr=perr, retry_stdout=retry.stdout, retry_stderr=retry.stderr)
        return {'victim_pid':victim.pid, 'peer_pid':peer.pid,
                'victim_marker':victim_marker, 'peer_marker':peer_marker,
                'victim_exit':victim.returncode, 'peer_exit':peer.returncode,
                'retry_exit':retry.returncode, 'before':before, 'after':after,
                'peer_after_victim_cancel':peer_after_victim_cancel,
                'victim_artifact_after_cancel':victim_artifact_after_cancel,
                'peer_artifact_after_completion':peer_artifact_after_completion,
                'victim_artifact_after_retry':(a/'target'/'debug'/'libcancel_probe.rlib').exists(),
                'cargo_toml_sha256':sha(a/'Cargo.toml'), 'build_script_sha256':sha(a/'build.rs')}
    finally:
        for proc in processes:
            if proc.poll() is None:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait(timeout=5)

def main():
    assert not WORK.exists(), 'copy package or remove only support/work before replay'
    preflight = {'free_memory_percent':free_memory(), 'disk_free_bytes':shutil.disk_usage(ROOT).free}
    assert preflight['free_memory_percent'] is not None and preflight['free_memory_percent'] >= 25
    assert preflight['disk_free_bytes'] >= 5*1024**3
    WORK.mkdir()
    lean = lean_cell()
    cargo = cargo_cell()
    result = {'lean_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),
        'lean_sha256':sha(LEAN), 'cargo_version':subprocess.check_output([str(CARGO),'--version'],text=True).strip(),
        'cargo_sha256':sha(CARGO), 'preflight':preflight, 'lean':lean, 'cargo':cargo,
        'events':EVENTS}
    normalized = json.dumps(result, indent=2, ensure_ascii=False)
    normalized = normalized.replace(str(WORK), '$WORK').replace(str(LEAN), '$LEAN_BIN').replace(str(CARGO), '$CARGO_BIN')
    (ROOT/'results.json').write_text(normalized+'\n')
    print(json.dumps({'lean_cancel_response':lean['cancel_response'],
        'lean_batch_returncode':lean['batch_returncode'], 'cargo_victim_exit':cargo['victim_exit'],
        'cargo_peer_exit':cargo['peer_exit'], 'cargo_retry_exit':cargo['retry_exit']}, indent=2))

if __name__ == '__main__':
    main()
