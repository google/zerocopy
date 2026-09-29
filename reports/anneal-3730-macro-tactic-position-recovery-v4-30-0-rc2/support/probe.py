#!/usr/bin/env python3
"""Bounded direct Lean macro-tactic goal and batch recovery grid."""
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
WORK = HERE / "work"
SOURCE = REPORTS / "anneal-3730-lean-uri-history-import-boundaries-2026-09-29/support/probe.py"
spec = importlib.util.spec_from_file_location("cached_uri_harness", SOURCE)
harness = importlib.util.module_from_spec(spec)
spec.loader.exec_module(harness)
LEAN = harness.LEAN
ENV = harness.ENV
Server = harness.Server
BASE = ('syntax "solve_macro" term : tactic\n'
        'macro_rules | `(tactic| solve_macro $t) => `(tactic| exact $t)\n'
        'theorem q (h : True) : True := by\n'
        '  solve_macro {term}\n')
POSITIONS = [(3, col) for col in (0, 2, 8, 14, 16, 20)] + [(4, col) for col in (0, 2)]


def sha(data):
    if isinstance(data, Path):
        data = data.read_bytes()
    if isinstance(data, str):
        data = data.encode()
    return hashlib.sha256(data).hexdigest()


def batch(label, path):
    command = [str(LEAN), '--json', path.name]
    p = subprocess.run(command, cwd=WORK, env=ENV, capture_output=True, text=True, timeout=20)
    return dict(label=label, argv=command, rc=p.returncode, stdout=p.stdout,
                stderr=p.stderr, source_sha256=sha(path))


def matrix(server, uri):
    out = []
    for line, col in POSITIONS:
        reply = server.request('$/lean/plainGoal',
            dict(textDocument=dict(uri=uri), position=dict(line=line, character=col)), 8)
        out.append(dict(line=line, character=col, reply=reply))
    return out


def case(server, path, uri, label, term, version, initial=False):
    source = BASE.format(term=term)
    path.write_text(source)
    fresh = batch(label, path)
    if initial:
        server.send(dict(jsonrpc='2.0', method='textDocument/didOpen', params={
            'textDocument': dict(uri=uri, languageId='lean', version=version, text=source)}))
    else:
        server.send(dict(jsonrpc='2.0', method='textDocument/didChange', params={
            'textDocument': dict(uri=uri, version=version),
            'contentChanges': [dict(text=source)]}))
    wait = server.request('textDocument/waitForDiagnostics', dict(uri=uri, version=version), 8)
    return dict(label=label, term=term, version=version, source=source,
                fresh_batch=fresh, wait=wait, diagnostics=server.diags.get(uri),
                positions=matrix(server, uri))


def main():
    assert LEAN.is_file()
    pressure = subprocess.run(['memory_pressure', '-Q'], capture_output=True, text=True, timeout=5)
    match = re.search(r'System-wide memory free percentage: (\d+)%', pressure.stdout)
    assert match and int(match.group(1)) >= 25
    if WORK.exists():
        shutil.rmtree(WORK)
    WORK.mkdir()
    path = WORK / 'Macro.lean'
    uri = path.as_uri()
    server = Server('macro-position', WORK, 'direct')
    try:
        rows = [case(server, path, uri, 'unsolved-v1', '?_', 1, initial=True),
                case(server, path, uri, 'solved-v2', 'h', 2),
                case(server, path, uri, 'unsolved-v3', '?_', 3)]
    finally:
        server.stop()
    def goal(row, line, col):
        return next(x['reply'].get('result') for x in row['positions']
                    if x['line'] == line and x['character'] == col)
    assert rows[0]['fresh_batch']['rc'] != 0 and rows[2]['fresh_batch']['rc'] != 0
    assert rows[1]['fresh_batch']['rc'] == 0
    assert '⊢ True' in str(goal(rows[0], 3, 0))
    assert '⊢ True' in str(goal(rows[2], 3, 0))
    assert not goal(rows[1], 3, 8).get('goals')
    result = dict(subject=dict(lean_binary_sha256=sha(LEAN),
                               harness_sha256=sha(SOURCE),
                               probe_sha256=sha(Path(__file__)),
                               host_free_percent=int(match.group(1))),
                  positions=POSITIONS, cases=rows, wire_events=harness.prior.EVENTS)
    (HERE / 'results.json').write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({row['label']: row['fresh_batch']['rc'] for row in rows}, sort_keys=True))


if __name__ == '__main__':
    main()
