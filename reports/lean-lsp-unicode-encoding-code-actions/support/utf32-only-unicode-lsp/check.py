#!/usr/bin/env python3
"""Offline verification of retained Lean UTF-32-only offer wire and resource evidence."""

import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def parse_wire(raw):
    messages = []
    while raw:
        header, sep, rest = raw.partition(b'\r\n\r\n')
        assert sep
        lengths = [int(line.split(b':', 1)[1]) for line in header.split(b'\r\n')
                   if line.lower().startswith(b'content-length:')]
        assert len(lengths) == 1 and len(rest) >= lengths[0]
        messages.append(json.loads(rest[:lengths[0]]))
        raw = rest[lengths[0]:]
    return messages


def main():
    oracle_raw = (HERE / 'oracle.json').read_bytes()
    oracle = json.loads(oracle_raw)
    original = (HERE / 'fixture/Encoding.lean').read_bytes()
    patched = (HERE / 'fixture/EncodingPatched.lean').read_bytes()
    result = json.loads((HERE / 'results.json').read_text())
    assert result['status'] == 'completed' and result['stop_reason'] is None
    assert result['oracle_prelaunch_sha256'] == sha(oracle_raw)
    assert result['fixture_sha256'] == {'original': sha(original), 'patched': sha(patched)}
    assert oracle['original_sha256'] == sha(original)
    assert oracle['patched_sha256'] == sha(patched)
    source = original.decode('utf-8')
    token = oracle['token']
    start, end = oracle['source_scalar_range']
    assert source[start:end] == token and source[:start] + oracle['replacement'] + source[end:] == patched.decode('utf-8')
    assert oracle['begin'] == {'unicode_scalars': 15, 'utf16_code_units': 16, 'utf8_bytes': 19}
    assert oracle['end'] == {'unicode_scalars': 26, 'utf16_code_units': 27, 'utf8_bytes': 30}
    assert len(set(oracle['begin'].values())) == 3
    assert result['preflight']['host']['estimated_reclaimable_percent'] > 30
    assert result['preflight']['host']['free_disk_bytes'] > 10 * 1024**3
    assert result['cleanup']['work_exists_after'] is False
    assert not (HERE / 'work').exists()

    sessions = result['sessions']
    assert list(sessions) == ['utf32_only']
    summary = {}
    for tag, offered, edit_range in (('utf32_only', ['utf-32'], oracle['utf32_only_change_range']),):
        record = sessions[tag]
        assert record['status'] == 'completed' and record['stop_reason'] is None
        assert record['exit'] == 0 and record['postrun_process_group_rss_kib'] == 0
        assert record['offered'] == offered
        assert record['preflight']['host']['estimated_reclaimable_percent'] > 30
        assert record['preflight']['host']['free_disk_bytes'] > 10 * 1024**3
        assert record['samples']
        limits = result['limits']
        for sample in record['samples']:
            assert sample['host']['estimated_reclaimable_percent'] >= limits['minimum_live_reclaimable_percent']
            assert sample['host']['free_disk_bytes'] >= limits['minimum_free_disk_bytes']
            assert sample['process_group_rss_kib'] <= limits['maximum_process_group_rss_kib']
            assert sample['scratch_bytes'] <= limits['maximum_scratch_bytes']
            assert sample['elapsed_seconds'] <= limits['maximum_session_seconds']
        client_raw = (HERE / 'raw' / f'{tag}.client-wire').read_bytes()
        server_raw = (HERE / 'raw' / f'{tag}.server-wire').read_bytes()
        stderr = (HERE / 'raw' / f'{tag}.stderr').read_bytes()
        assert record['wire_sha256'] == {'client': sha(client_raw), 'server': sha(server_raw),
                                         'stderr': sha(stderr)}
        clients, servers = parse_wire(client_raw), parse_wire(server_raw)
        assert clients == [e['message'] for e in record['events'] if e['side'] == 'client']
        assert servers == [e['message'] for e in record['events'] if e['side'] == 'server']
        init = next(e for e in clients if e.get('method') == 'initialize')
        assert init['id'] == 1
        assert init['params']['capabilities']['general']['positionEncodings'] == offered
        def raw_response(request_id):
            hits = [(index, message) for index, message in enumerate(servers)
                    if message.get('id') == request_id and ('result' in message or 'error' in message)]
            assert len(hits) == 1, (request_id, hits)
            return hits[0]
        assert raw_response(1)[1] == record['initialize']
        assert record['initialize']['result']['capabilities'].get('positionEncoding') is None
        opens = [e for e in clients if e.get('method') == 'textDocument/didOpen']
        assert len(opens) == 1
        opened = opens[0]['params']['textDocument']
        assert opened['version'] == 1 and opened['text'] == source
        assert opened['uri'] == record['uri'] and opened['languageId'] == 'lean'
        changes = [e for e in clients if e.get('method') == 'textDocument/didChange']
        assert len(changes) == 1
        assert changes[0]['params']['textDocument']['version'] == 2
        assert changes[0]['params']['contentChanges'] == [{'range': edit_range,
                                                             'text': oracle['replacement']}]
        for phase, version in (('before', 1), ('after', 2)):
            request_id = 2 if phase == 'before' else 3
            waits = [e for e in clients if e.get('method') == 'textDocument/waitForDiagnostics' and e.get('id') == request_id]
            assert len(waits) == 1 and waits[0]['params'] == {'uri': record['uri'], 'version': version}
            response_index, response = raw_response(request_id)
            assert response == record[phase]['wait_response']
            raw_publications = [message for message in servers[:response_index]
                                if message.get('method') == 'textDocument/publishDiagnostics']
            assert raw_publications == record[phase]['publications']
            assert record[phase]['last'] == raw_publications[-1]['params']['diagnostics']
            assert record[phase]['wait_response']['result'] == {}
            assert record[phase]['publications']
            assert record[phase]['publications'][-1]['params']['version'] == version
        shutdowns = [e for e in clients if e.get('method') == 'shutdown']
        assert len(shutdowns) == 1 and shutdowns[0]['id'] == 4
        assert raw_response(4)[1] == record['shutdown']
        initial = [d for d in record['before']['last'] if d.get('severity') == 1]
        assert len(initial) == 1 and token in initial[0]['message']
        assert initial[0]['range'] == oracle['utf16_only_change_range']
        after = record['after']['last']
        errors = [d for d in after if d.get('severity') == 1]
        assert len(errors) == 1 and 'Unknown constant `Nat.zeroe`' in errors[0]['message']
        assert errors[0]['range'] == {'start': {'line': 0, 'character': 15}, 'end': {'line': 0, 'character': 24}}
        summary[tag] = {
            'offered': offered,
            'selected_position_encoding': record['initialize']['result']['capabilities'].get('positionEncoding'),
            'initial_error_range': initial[0]['range'],
            'after_error_messages': [d['message'] for d in after if d.get('severity') == 1],
            'max_sampled_rss_kib': max(s['process_group_rss_kib'] for s in record['samples']),
            'min_sampled_reclaimable_percent': min(s['host']['estimated_reclaimable_percent'] for s in record['samples']),
            'min_sampled_free_disk_bytes': min(s['host']['free_disk_bytes'] for s in record['samples']),
            'max_sampled_scratch_bytes': max(s['scratch_bytes'] for s in record['samples']),
            'sample_count': len(record['samples']), 'exit': record['exit'],
        }

    batch = result['batch']
    assert set(batch) == {'original', 'patched'}
    batch_summary = {}
    for key, wanted_exit in (('original', 1), ('patched', 0)):
        b = batch[key]
        assert b['status'] == 'completed' and b['stop_reason'] is None
        assert b['exit'] == wanted_exit and b['postrun_process_group_rss_kib'] == 0
        assert b['preflight']['host']['estimated_reclaimable_percent'] > 30
        assert b['preflight']['host']['free_disk_bytes'] > 10 * 1024**3
        assert b['samples'] and all(s['process_group_rss_kib'] <= result['limits']['maximum_process_group_rss_kib']
                                    and s['host']['estimated_reclaimable_percent'] >= 20
                                    and s['host']['free_disk_bytes'] >= 10 * 1024**3
                                    and s['scratch_bytes'] <= 100 * 1024**2
                                    and s['elapsed_seconds'] <= 30 for s in b['samples'])
        stdout, stderr = ((HERE / 'raw' / f'batch-{key}.{stream}').read_bytes()
                          for stream in ('stdout', 'stderr'))
        assert sha(stdout) == b['stdout_sha256'] and sha(stderr) == b['stderr_sha256']
        entries = [json.loads(line) for line in stdout.decode().splitlines()]
        if key == 'original':
            error = [x for x in entries if x['severity'] == 'error']
            assert len(error) == 1 and token in error[0]['data']
            assert error[0]['pos'] == {'line': 1, 'column': oracle['begin']['unicode_scalars']}
            assert error[0]['endPos'] == {'line': 1, 'column': oracle['end']['unicode_scalars']}
        else:
            assert not any(x['severity'] == 'error' for x in entries)
            assert any('Nat.zero' in x['data'] for x in entries)
        batch_summary[key] = {'exit': b['exit'], 'message_count': len(entries),
                              'max_sampled_rss_kib': max(s['process_group_rss_kib'] for s in b['samples']),
                              'min_sampled_reclaimable_percent': min(s['host']['estimated_reclaimable_percent'] for s in b['samples']),
                              'min_sampled_free_disk_bytes': min(s['host']['free_disk_bytes'] for s in b['samples'])}
    comparison = {'schema': 1, 'lean_sha256': result['lean_sha256'],
                  'oracle_prelaunch_sha256': result['oracle_prelaunch_sha256'],
                  'fixture_sha256': result['fixture_sha256'],
                  'coordinate_oracle': {'begin': oracle['begin'], 'end': oracle['end']},
                  'sessions': summary, 'batch': batch_summary,
                  'negative_controls': {'utf32_offer_did_not_change_utf16_diagnostic': True,
                                        'scalar_ranged_edit_did_not_repair': True,
                                        'fresh_batch_patched_succeeded': True},
                  'cleanup': result['cleanup']}
    serialized = json.dumps(comparison, indent=2, ensure_ascii=False) + '\n'
    if '--write' in sys.argv[1:]:
        (HERE / 'comparison.json').write_text(serialized)
    else:
        assert (HERE / 'comparison.json').read_text() == serialized
    metadata_path = HERE / 'REPORT.json'
    if metadata_path.exists():
        metadata = json.loads(metadata_path.read_text())
        assert metadata['observed_at'] == '2026-09-30'
        identities = [s['identity'] for s in metadata['subjects']]
        assert any(i.get('lean_sha256') == result['lean_sha256'] for i in identities)
        assert any(i.get('results_sha256') == sha((HERE / 'results.json').read_bytes())
                   and i.get('original_sha256') == sha(original)
                   and i.get('patched_sha256') == sha(patched)
                   and i.get('oracle_prelaunch_sha256') == sha(oracle_raw)
                   for i in identities)
    print(json.dumps({'sessions': {k: {'exit': v['exit'], 'after_errors': len(v['after_error_messages'])}
                                    for k, v in summary.items()},
                      'batch_exits': {k: v['exit'] for k, v in batch_summary.items()},
                      'initial_range': oracle['utf16_only_change_range']}))


if __name__ == '__main__':
    main()
