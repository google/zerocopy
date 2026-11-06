#!/usr/bin/env python3
"""Synthetic one-shot, project-worker, and broker contract comparison.

This is deliberately not an Anneal backend. Its stage result is a SHA-256 of
fully supplied toy input. Run from this package with `python3 support/topology_probe.py`.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import platform
import statistics
import subprocess
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve()
OUT = HERE.parent / 'topology-results.json'
TOOL = {'name': 'toy-stage', 'revision': 'v1'}

def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()

def semantic_key(req):
    return {k: req[k] for k in ('project', 'source', 'model')} | {'tool': TOOL}

def digest(req):
    return hashlib.sha256(canonical(semantic_key(req))).hexdigest()

def child(once):
    cache = {}
    for line in sys.stdin:
        req = json.loads(line)
        key = canonical(semantic_key(req))
        hit = key in cache
        if not hit:
            # Synthetic compiler work; the deliberately specified delay makes
            # the scheduling comparison visible and is not a Lean measurement.
            time.sleep(req.get('delay_ms', 25) / 1000)
            cache[key] = digest(req)
        status = req.get('status', 'ok')
        print(f'diagnostic-looking stderr: ERROR marker req={req["id"]}', file=sys.stderr, flush=True)
        if status == 'ok':
            response = {'request_id': req['id'], 'status': 'ok', 'semantic_digest': cache[key],
                        'cache_hit': hit, 'worker_pid': os.getpid()}
            print(json.dumps(response, sort_keys=True), flush=True)
        elif status == 'failed':
            response = {'request_id': req['id'], 'status': 'failed',
                        'partial_digest': cache[key], 'cache_hit': hit, 'worker_pid': os.getpid()}
            print(json.dumps(response, sort_keys=True), flush=True)
        elif status == 'malformed':
            print('{not-json', flush=True)
        else:
            raise ValueError(status)
        if once:
            break

def accept(req, raw):
    try:
        value = json.loads(raw)
    except json.JSONDecodeError:
        return 'invalid-result', None, None
    if value.get('request_id') != req['id']:
        return 'wrong-echo', None, value
    if value.get('status') != 'ok':
        return 'process-failed', None, value
    if value.get('semantic_digest') != digest(req):
        return 'wrong-digest', None, value
    return 'accepted', value['semantic_digest'], value

class Topology:
    def __init__(self, kind):
        self.kind = kind
        self.procs = {}
        self.locks = {}
        self.launches = 0
        self.pids = set()

    def _spawn(self):
        proc = subprocess.Popen([sys.executable, str(HERE), 'child'], stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.launches += 1
        self.pids.add(proc.pid)
        return proc

    def _send(self, proc, req):
        assert proc.stdin and proc.stdout
        proc.stdin.write(json.dumps(req, sort_keys=True) + '\n')
        proc.stdin.flush()
        raw = proc.stdout.readline().strip()
        return raw

    def run(self, req):
        start = time.perf_counter()
        if self.kind == 'one-shot':
            proc = subprocess.run([sys.executable, str(HERE), 'child', '--once'],
                                  input=json.dumps(req)+'\n', capture_output=True, text=True)
            self.launches += 1
            raw = proc.stdout.strip()
            # stderr is deliberately ignored as a semantic channel.
            assert 'diagnostic-looking stderr' in proc.stderr
            os_exit = proc.returncode
        else:
            slot = req['project'] if self.kind == 'per-project' else '*'
            if slot not in self.procs:
                self.procs[slot] = self._spawn()
                self.locks[slot] = threading.Lock()
            with self.locks[slot]:
                raw = self._send(self.procs[slot], req)
            os_exit = None
        disposition, result, value = accept(req, raw)
        elapsed = (time.perf_counter()-start)*1000
        return {'id': req['id'], 'project': req['project'], 'disposition': disposition,
                'digest': result, 'cache_hit': value.get('cache_hit') if value else None,
                'worker_pid': value.get('worker_pid') if value else None,
                'os_exit': os_exit, 'elapsed_ms': round(elapsed, 3)}

    def restart(self, project):
        if self.kind == 'one-shot':
            return
        slot = project if self.kind == 'per-project' else '*'
        proc = self.procs.pop(slot, None)
        self.locks.pop(slot, None)
        if proc:
            proc.stdin.close()
            proc.wait(timeout=5)
            proc.stderr.close()
            proc.stdout.close()

    def close(self):
        for slot in list(self.procs):
            self.restart(slot)

def req(id, project, source, model, status='ok', delay_ms=25):
    return dict(id=id, project=project, source=source, model=model,
                status=status, delay_ms=delay_ms)

def trial(kind):
    host = Topology(kind)
    try:
        inputs = [req('a1','alpha','S','A'), req('b1','beta','S','B'),
                  req('a1-repeat','alpha','S','A'), req('b-fail','beta','S2','B','failed'),
                  req('b-after','beta','S','B'), req('a-bad','alpha','S2','A','malformed')]
        sequential = [host.run(x) for x in inputs]
        assert [x['disposition'] for x in sequential] == [
            'accepted','accepted','accepted','process-failed','accepted','invalid-result']
        assert sequential[0]['digest'] == sequential[2]['digest']
        assert sequential[1]['digest'] == sequential[4]['digest']
        assert sequential[0]['digest'] != sequential[1]['digest']
        host.restart('alpha')
        reconstructed = host.run(req('a-restart','alpha','S','A'))
        assert reconstructed['digest'] == sequential[0]['digest']
        pair = [req('a-par','alpha','P','A',delay_ms=120),
                req('b-par','beta','P','B',delay_ms=120)]
        start=time.perf_counter()
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            concurrent_results=list(pool.map(host.run,pair))
        concurrent_ms=round((time.perf_counter()-start)*1000,3)
        assert all(x['disposition']=='accepted' for x in concurrent_results)
        assert concurrent_results[0]['digest'] != concurrent_results[1]['digest']
        return {'kind':kind,'sequential':sequential,'reconstructed':reconstructed,
                'concurrent':concurrent_results,'concurrent_pair_wall_ms':concurrent_ms,
                'launches':host.launches,'persistent_worker_pids':sorted(host.pids),
                'accepted_digests':[x['digest'] for x in sequential if x['digest']]}
    finally:
        host.close()

def main():
    trials=[trial(x) for x in ('one-shot','per-project','shared-broker')]
    assert len({tuple(x['accepted_digests']) for x in trials})==1
    result={'host':{'python':platform.python_version(),'system':platform.platform(),
                    'machine':platform.machine()}, 'tool':TOOL, 'trials':trials,
            'conclusions':{'same_accepted_digests':True,
                           'isolation_after_failure':True,
                           'reconstruction_from_full_request':True}}
    OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'topologies':[x['kind'] for x in trials],
                      'launches':[x['launches'] for x in trials],
                      'concurrent_pair_wall_ms':[x['concurrent_pair_wall_ms'] for x in trials]},sort_keys=True))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('mode',nargs='?',default='probe',choices=['probe','child'])
    p.add_argument('--once',action='store_true');args=p.parse_args()
    if args.mode=='child':child(args.once)
    else:main()
