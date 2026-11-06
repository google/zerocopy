#!/usr/bin/env python3
"""One-shot guarded compiler/Lean copied-empty-line v2 edit probe."""

import hashlib
import json
import os
from pathlib import Path
import re
import select
import shutil
import signal
import subprocess
import time
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
LEAN = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
LEAN_SHA = 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
RUSTC = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin/rustc')
RUSTC_SHA = '2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc'
RAW = HERE / 'raw'
WORK = HERE / 'work'
RESULT = HERE / 'results.json'
MIN_ADMIT_PERCENT = 30.0
MIN_LIVE_PERCENT = 20.0
MIN_DISK_BYTES = 10 * 1024**3
MAX_RSS_KIB = 1200 * 1024
MAX_RUST_RSS_KIB = 512 * 1024
MAX_SCRATCH_BYTES = 100 * 1024**2
MAX_SESSION_SECONDS = 30.0


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def headroom():
    stat = subprocess.check_output(['/usr/bin/vm_stat'], text=True, timeout=5)
    size = int(re.search(r'page size of (\d+) bytes', stat).group(1))
    pages = {key: int(re.search(rf'Pages {key}:\s+(\d+)\.', stat).group(1))
             for key in ('free', 'inactive', 'speculative')}
    physical = int(subprocess.check_output(['/usr/sbin/sysctl', '-n', 'hw.memsize'], text=True, timeout=5))
    return {'estimated_reclaimable_percent': round(100 * size * sum(pages.values()) / physical, 4),
            'free_disk_bytes': shutil.disk_usage(HERE).free,
            'page_size': size, 'pages': pages, 'physical_memory_bytes': physical}


def rss_kib(pgid):
    if pgid is None:
        return 0
    raw = subprocess.check_output(['/bin/ps', '-axo', 'pgid=,rss=,state='], text=True, timeout=5)
    return sum(int(fields[1]) for line in raw.splitlines()
               if len(fields := line.split()) == 3 and fields[0] == str(pgid)
               and not fields[2].startswith('Z'))


def scratch_bytes():
    return sum(path.stat().st_size for path in WORK.rglob('*') if path.is_file()) if WORK.exists() else 0


def sample(pgid, start):
    host = headroom()
    row = {'elapsed_seconds': round(time.monotonic() - start, 4), 'host': host,
           'process_group_rss_kib': rss_kib(pgid), 'scratch_bytes': scratch_bytes()}
    reason = None
    if host['estimated_reclaimable_percent'] < MIN_LIVE_PERCENT:
        reason = 'memory_guard'
    elif host['free_disk_bytes'] < MIN_DISK_BYTES:
        reason = 'disk_guard'
    elif row['process_group_rss_kib'] > MAX_RSS_KIB:
        reason = 'rss_guard'
    elif row['scratch_bytes'] > MAX_SCRATCH_BYTES:
        reason = 'scratch_guard'
    elif row['elapsed_seconds'] > MAX_SESSION_SECONDS:
        reason = 'timeout_guard'
    return row, reason


def admit():
    row, reason = sample(None, time.monotonic())
    if not reason and row['host']['estimated_reclaimable_percent'] <= MIN_ADMIT_PERCENT:
        reason = 'admission_memory'
    return row, reason


def stop(proc):
    if proc.poll() is not None:
        return
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        proc.wait(timeout=2)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.wait(timeout=2)


def main():
    assert not any(path.exists() for path in (RAW, WORK, RESULT)), 'one-shot output already exists'
    assert sha(LEAN.read_bytes()) == LEAN_SHA
    assert sha(RUSTC.read_bytes()) == RUSTC_SHA
    oracle_raw = (HERE / 'oracle.json').read_bytes()
    oracle = json.loads(oracle_raw)
    host = (HERE / 'fixture/Host.rs').read_bytes()
    original = (HERE / 'fixture/ProjectedV1.lean').read_bytes()
    patched = (HERE / 'fixture/ProjectedV2.lean').read_bytes()
    assert sha(host) == oracle['sha256']['Host.rs']
    assert sha(original) == oracle['sha256']['ProjectedV1.lean']
    assert sha(patched) == oracle['sha256']['ProjectedV2.lean']
    assert original[:oracle['points']['projected_empty_insertion']['byte_offset']] + oracle['edit']['text'].encode() + original[oracle['points']['projected_empty_insertion']['byte_offset']:] == patched
    result = {'schema': 1, 'observed_utc': now(), 'lean_sha256': LEAN_SHA, 'rustc_sha256': RUSTC_SHA,
              'oracle_prelaunch_sha256': sha(oracle_raw),
              'fixture_sha256': {'host': sha(host), 'original': sha(original), 'patched': sha(patched)},
              'limits': {'minimum_admission_reclaimable_percent': MIN_ADMIT_PERCENT,
                         'minimum_live_reclaimable_percent': MIN_LIVE_PERCENT,
                         'minimum_free_disk_bytes': MIN_DISK_BYTES,
                         'maximum_lean_process_group_rss_kib': MAX_RSS_KIB,
                         'maximum_rust_process_group_rss_kib': MAX_RUST_RSS_KIB,
                         'maximum_scratch_bytes': MAX_SCRATCH_BYTES,
                         'maximum_session_seconds': MAX_SESSION_SECONDS},
              'sessions': {}, 'batch': {}, 'rust': {}, 'status': 'prepared', 'stop_reason': None}
    first, reason = admit()
    result['preflight'] = first
    if reason:
        result['status'] = 'admission_denied'
        result['stop_reason'] = reason
        RESULT.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
        print(json.dumps({'status': result['status'], 'reason': reason}))
        return
    RAW.mkdir()
    WORK.mkdir()
    env = dict(os.environ)
    env['LEAN_NUM_THREADS'] = '1'

    def guarded_command(tag, argv, max_rss_kib, command_env):
        preflight, refusal = admit()
        record = {'argv': argv, 'preflight': preflight, 'status': 'admission_denied' if refusal else 'running',
                  'stop_reason': refusal, 'samples': [], 'cwd': str(WORK)}
        if refusal:
            return record
        started = time.monotonic()
        record['started_utc'] = now()
        proc = subprocess.Popen(argv, cwd=WORK, env=command_env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                start_new_session=True)
        record['pid'] = proc.pid
        while True:
            row, reason = sample(proc.pid, started)
            if not reason and row['process_group_rss_kib'] > max_rss_kib:
                reason = 'rss_guard'
            record['samples'].append(row)
            if reason or proc.poll() is not None:
                break
            time.sleep(.05)
        if reason:
            stop(proc)
        stdout, stderr = proc.communicate(timeout=3)
        (RAW / f'{tag}.stdout').write_bytes(stdout)
        (RAW / f'{tag}.stderr').write_bytes(stderr)
        record.update({'status': 'guard_stopped' if reason else 'completed', 'stop_reason': reason,
                       'exit': proc.returncode, 'ended_utc': now(), 'stdout_sha256': sha(stdout),
                       'stderr_sha256': sha(stderr), 'postrun_group_rss_kib': rss_kib(proc.pid)})
        return record

    def run_session(tag, offered, edit_range):
        preflight, refusal = admit()
        record = {'offered': offered, 'preflight': preflight, 'status': 'admission_denied' if refusal else 'running',
                  'stop_reason': refusal, 'events': [], 'samples': [],
                  'argv': [str(LEAN), '--server'], 'environment': {'LEAN_NUM_THREADS': '1'}}
        if refusal:
            return record
        work = WORK / tag
        work.mkdir()
        source_file = work / 'Projected.lean'
        source_file.write_bytes(original)
        log_dir = work / 'logs'
        log_dir.mkdir()
        local_env = dict(env, LEAN_SERVER_LOG_DIR=str(log_dir))
        record['environment']['LEAN_SERVER_LOG_DIR'] = str(log_dir)
        record['cwd'] = str(work)
        record['uri'] = source_file.as_uri()
        client_wire, server_wire = RAW / f'{tag}.client-wire', RAW / f'{tag}.server-wire'
        client_out, server_out = client_wire.open('wb'), server_wire.open('wb')
        start = time.monotonic()
        record['started_utc'] = now()
        record['start_monotonic_ns'] = time.monotonic_ns()
        proc = subprocess.Popen(record['argv'], cwd=work, env=local_env,
                                stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, start_new_session=True, bufsize=0)
        record['pid'] = proc.pid
        buffer = b''

        def guard():
            row, reason = sample(proc.pid, start)
            record['samples'].append(row)
            if reason:
                raise RuntimeError(reason)

        def send(message):
            encoded = json.dumps(message, separators=(',', ':'), ensure_ascii=False).encode('utf-8')
            frame = b'Content-Length: ' + str(len(encoded)).encode() + b'\r\n\r\n' + encoded
            proc.stdin.write(frame)
            proc.stdin.flush()
            client_out.write(frame)
            record['events'].append({'side': 'client', 'elapsed_seconds': round(time.monotonic()-start, 4),
                                     'message': message})

        def pop_message():
            nonlocal buffer
            if b'\r\n\r\n' not in buffer:
                return None
            header, body = buffer.split(b'\r\n\r\n', 1)
            matches = [int(line.split(b':', 1)[1]) for line in header.split(b'\r\n')
                       if line.lower().startswith(b'content-length:')]
            assert len(matches) == 1
            if len(body) < matches[0]:
                return None
            encoded, buffer = body[:matches[0]], body[matches[0]:]
            message = json.loads(encoded)
            record['events'].append({'side': 'server', 'elapsed_seconds': round(time.monotonic()-start, 4),
                                     'message': message})
            if 'method' in message and 'id' in message:
                send({'jsonrpc': '2.0', 'id': message['id'], 'result': None})
            return message

        def receive_until(target_id):
            while True:
                guard()
                message = pop_message()
                if message is not None:
                    if message.get('id') == target_id and 'result' in message and 'method' not in message:
                        return message
                    continue
                ready, _, _ = select.select([proc.stdout], [], [], 0.05)
                if ready:
                    chunk = os.read(proc.stdout.fileno(), 65536)
                    if not chunk:
                        raise RuntimeError('server_stdout_closed')
                    server_out.write(chunk)
                    nonlocal_buffer_append(chunk)
                elif proc.poll() is not None:
                    raise RuntimeError('server_exited_early')

        def nonlocal_buffer_append(chunk):
            nonlocal buffer
            buffer += chunk

        def settled_diagnostics(version, request_id):
            send({'jsonrpc': '2.0', 'id': request_id,
                  'method': 'textDocument/waitForDiagnostics',
                  'params': {'uri': source_file.as_uri(), 'version': version}})
            response = receive_until(request_id)
            publications = [event['message'] for event in record['events']
                            if event['side'] == 'server' and
                            event['message'].get('method') == 'textDocument/publishDiagnostics']
            assert publications, 'no diagnostic publication'
            return {'wait_response': response, 'publications': publications,
                    'last': publications[-1]['params']['diagnostics']}

        try:
            capabilities = {'general': {'positionEncodings': offered},
                            'textDocument': {'synchronization': {'didSave': False}}}
            send({'jsonrpc': '2.0', 'id': 1, 'method': 'initialize',
                  'params': {'processId': os.getpid(), 'rootUri': work.as_uri(),
                             'capabilities': capabilities,
                             'initializationOptions': {'hasWidgets': False,
                                                       'logCfg': {'logDir': str(log_dir)}}}})
            record['initialize'] = receive_until(1)
            send({'jsonrpc': '2.0', 'method': 'initialized', 'params': {}})
            send({'jsonrpc': '2.0', 'method': 'textDocument/didOpen',
                  'params': {'textDocument': {'uri': source_file.as_uri(), 'languageId': 'lean',
                                              'version': 1, 'text': original.decode('utf-8')}}})
            record['before'] = settled_diagnostics(1, 2)
            send({'jsonrpc': '2.0', 'method': 'textDocument/didChange',
                  'params': {'textDocument': {'uri': source_file.as_uri(), 'version': 2},
                             'contentChanges': [{'range': edit_range,
                                                 'text': oracle['edit']['text']}]}})
            record['after'] = settled_diagnostics(2, 3)
            record['disk_sha256_after_v2'] = sha(source_file.read_bytes())
            send({'jsonrpc': '2.0', 'id': 4, 'method': 'shutdown', 'params': None})
            record['shutdown'] = receive_until(4)
            send({'jsonrpc': '2.0', 'method': 'exit', 'params': None})
            proc.wait(timeout=3)
            record['status'] = 'completed' if proc.returncode == 0 else 'command_failed'
        except Exception as error:
            record['status'] = 'guard_or_protocol_failed'
            record['stop_reason'] = str(error)
            stop(proc)
        finally:
            if proc.poll() is None:
                stop(proc)
            record['ended_utc'] = now()
            record['end_monotonic_ns'] = time.monotonic_ns()
            record['exit'] = proc.returncode
            client_out.close(); server_out.close()
            stderr = proc.stderr.read()
            stderr_path = RAW / f'{tag}.stderr'
            stderr_path.write_bytes(stderr)
            record['wire_sha256'] = {'client': sha(client_wire.read_bytes()),
                                     'server': sha(server_wire.read_bytes()),
                                     'stderr': sha(stderr)}
            record['postrun_process_group_rss_kib'] = rss_kib(proc.pid)
        return record

    try:
        (WORK / 'Host.rs').write_bytes(host)
        rust_env = dict(env, RUSTUP_HOME='/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/rustup',
                        CARGO_HOME='/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/cargo')
        result['rust'] = guarded_command('rust', [str(RUSTC), '--crate-type=lib', '--edition=2021',
                                                  '--crate-name=i025_empty_bridge', '--emit=metadata',
                                                  'Host.rs'], MAX_RUST_RSS_KIB, rust_env)
        if result['rust']['status'] != 'completed' or result['rust']['exit'] != 0:
            result['status'] = 'stopped_after_rust'
            result['stop_reason'] = result['rust']['stop_reason'] or 'rust_failed'
            return
        result['sessions']['utf16'] = run_session('utf16', ['utf-16'], oracle['edit']['range'])
        if result['sessions']['utf16']['status'] != 'completed':
            result['status'] = 'stopped_after_server'
            result['stop_reason'] = result['sessions']['utf16']['stop_reason']
            return
        for key, source in (('original', original), ('patched', patched)):
            path = WORK / f'{key}.lean'
            path.write_bytes(source)
            argv = [str(LEAN), '--json', str(path)]
            result['batch'][key] = guarded_command(f'batch-{key}', argv, MAX_RSS_KIB, env)
            if result['batch'][key]['status'] != 'completed':
                result['status'] = 'stopped_during_batch'
                result['stop_reason'] = result['batch'][key]['stop_reason']
                return
        result['status'] = 'completed'
    finally:
        result['postrun_host'] = headroom()
        result['cleanup'] = {'work_exists': WORK.exists()}
        if WORK.exists():
            shutil.rmtree(WORK)
            result['cleanup']['work_exists_after'] = WORK.exists()
        RESULT.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
        print(json.dumps({'status': result['status'], 'stop_reason': result['stop_reason'],
                          'sessions': {k: v['status'] for k, v in result['sessions'].items()},
                          'batch': {k: v['status'] for k, v in result['batch'].items()}}))


if __name__ == '__main__':
    main()
