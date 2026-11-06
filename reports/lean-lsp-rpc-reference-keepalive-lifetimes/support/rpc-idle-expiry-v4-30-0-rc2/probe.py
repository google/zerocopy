#!/usr/bin/env python3
"""Pinned Lean idle RPC session/reference expiry control."""
import hashlib
import importlib.util
import json
import re
import shutil
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
WORK = HERE / 'work'
HARNESS = REPORTS / 'anneal-3730-lean-uri-history-import-boundaries-2026-09-29/support/probe.py'
spec = importlib.util.spec_from_file_location('cached_uri_harness', HARNESS)
harness = importlib.util.module_from_spec(spec)
spec.loader.exec_module(harness)
LEAN = harness.LEAN
SOURCE = 'theorem hole (n : Nat) : n = n := by\n  exact ?_\n'
POSITION = dict(line=1, character=8)
IDLE_SECONDS = 42


def sha(x):
    if isinstance(x, Path):
        x = x.read_bytes()
    if isinstance(x, str):
        x = x.encode()
    return hashlib.sha256(x).hexdigest()


def call(server, uri, sid, method, params):
    return server.request('$/lean/rpc/call', dict(textDocument=dict(uri=uri),
        position=POSITION, sessionId=sid, method=method, params=params), 10)


def ref_from(rich):
    return rich['result']['goals'][0]['hyps'][0]['type']['tag'][0]['info']


def main():
    pressure = subprocess.run(['memory_pressure','-Q'], capture_output=True,text=True,timeout=5)
    found = re.search(r'System-wide memory free percentage: (\d+)%', pressure.stdout)
    assert found and int(found.group(1)) >= 25
    if WORK.exists():
        shutil.rmtree(WORK)
    WORK.mkdir()
    path = WORK/'Proof.lean'
    path.write_text(SOURCE)
    uri = path.as_uri()
    server = harness.Server('rpc-idle-expiry',WORK,'direct')
    # Server-to-client refresh requests use low IDs on this pin. The borrowed
    # harness matches by number, so keep client request IDs far away.
    server.n = 1000
    try:
        wait = harness.open_uri(server,uri,SOURCE)
        connect = server.request('$/lean/rpc/connect',dict(uri=uri),10)
        sid = connect['result']['sessionId']
        rich = call(server,uri,sid,'Lean.Widget.getInteractiveGoals',
                    dict(textDocument=dict(uri=uri),position=POSITION))
        ref = ref_from(rich)
        before = call(server,uri,sid,'Lean.Widget.InteractiveDiagnostics.infoToInteractive',ref)
        assert 'result' in before
        started = time.monotonic()
        time.sleep(IDLE_SECONDS)  # Deliberately send no keepAlive or other message.
        elapsed = round(time.monotonic()-started,3)
        expired = call(server,uri,sid,'Lean.Widget.InteractiveDiagnostics.infoToInteractive',ref)
        new_connect = server.request('$/lean/rpc/connect',dict(uri=uri),10)
        reopen = None
        if 'result' not in new_connect:
            server.send(dict(jsonrpc='2.0',method='textDocument/didClose',
                             params={'textDocument': {'uri': uri}}))
            reopen = harness.open_uri(server,uri,SOURCE)
            new_connect = server.request('$/lean/rpc/connect',dict(uri=uri),10)
        if 'result' in new_connect:
            new_sid = new_connect['result']['sessionId']
            recovered = call(server,uri,new_sid,'Lean.Widget.getInteractiveGoals',
                             dict(textDocument=dict(uri=uri),position=POSITION))
        else:
            recovered = None
        result = dict(subject=dict(lean_sha256=sha(LEAN),harness_sha256=sha(HARNESS),
                                   probe_sha256=sha(Path(__file__)),
                                   host_free_percent=int(found.group(1))),
                      source=SOURCE,source_sha256=sha(SOURCE),idle_seconds=elapsed,
                      wait=wait,connect=connect,rich=rich,reference=ref,
                      before=before,expired=expired,reopen=reopen,new_connect=new_connect,
                      recovered=recovered,wire_events=harness.prior.EVENTS)
    finally:
        server.stop()
    (HERE/'results.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(dict(idle_seconds=elapsed,expired=expired,
                          reconnect=new_connect,recovered=recovered is not None)))


if __name__=='__main__':
    main()
