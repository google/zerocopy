#!/usr/bin/env python3
"""Offline verification and exact v4.29/v4.30-rc2 LSP comparison."""

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
    baseline_raw = (HERE / 'baseline-v430-results.json').read_bytes()
    assert sha(baseline_raw) == 'a81a7fbbecc428f1cf4ce91eea2f03d49185a4a4b694ca3b0b48c6f46ea38469'
    baseline = json.loads(baseline_raw)
    assert result['lean_sha256'] == '2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37'
    assert baseline['lean_sha256'] == 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
    assert result['fixture_sha256'] == baseline['fixture_sha256']
    assert result['oracle_prelaunch_sha256'] == baseline['oracle_prelaunch_sha256']
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
    assert list(sessions) == ['utf8_only', 'utf16_only']
    assert sessions['utf8_only']['end_monotonic_ns'] < sessions['utf16_only']['start_monotonic_ns']
    summary = {}
    version_differences = {}
    for tag, offered, edit_range in (
        ('utf8_only', ['utf-8'], oracle['utf8_only_change_range']),
        ('utf16_only', ['utf-16'], oracle['utf16_only_change_range']),
    ):
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
        assert init['params']['capabilities']['general']['positionEncodings'] == offered
        assert record['initialize']['result']['capabilities'].get('positionEncoding') is None
        changes = [e for e in clients if e.get('method') == 'textDocument/didChange']
        assert len(changes) == 1
        assert changes[0]['params']['textDocument']['version'] == 2
        assert changes[0]['params']['contentChanges'] == [{'range': edit_range,
                                                             'text': oracle['replacement']}]
        for phase, version in (('before', 1), ('after', 2)):
            assert record[phase]['wait_response']['result'] == {}
            assert record[phase]['publications']
            assert record[phase]['publications'][-1]['params']['version'] == version
        initial = [d for d in record['before']['last'] if d.get('severity') == 1]
        assert len(initial) == 1 and token in initial[0]['message']
        assert initial[0]['range'] == oracle['utf16_only_change_range']
        after = record['after']['last']
        if tag == 'utf8_only':
            errors = [d for d in after if d.get('severity') == 1]
            assert len(errors) == 1 and 'unexpected end of input' in errors[0]['message']
            assert not any('Nat.zero' in d.get('message', '') for d in after)
        else:
            assert not any(d.get('severity') == 1 for d in after)
            assert any('Nat.zero' in d.get('message', '') for d in after)
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
        prior = baseline['sessions'][tag]
        assert prior['status'] == 'completed' and prior['exit'] == 0
        assert prior['offered'] == offered
        assert prior['initialize']['result']['capabilities'].get('positionEncoding') is None
        assert prior['before']['last'] == record['before']['last']
        assert prior['after']['last'] == record['after']['last']
        assert prior['before']['wait_response'] == record['before']['wait_response']
        assert prior['after']['wait_response'] == record['after']['wait_response']
        assert prior['shutdown'] == record['shutdown']
        current_caps = record['initialize']['result']['capabilities']
        prior_caps = prior['initialize']['result']['capabilities']
        current_without_rpc_wire = json.loads(json.dumps(current_caps))
        prior_without_rpc_wire = json.loads(json.dumps(prior_caps))
        assert current_without_rpc_wire['experimental']['rpcProvider'].get('rpcWireFormat') is None
        assert prior_without_rpc_wire['experimental']['rpcProvider'].pop('rpcWireFormat') == 'v1'
        assert current_without_rpc_wire == prior_without_rpc_wire
        version_differences[tag] = {
            'capability_delta': {'path': '/experimental/rpcProvider/rpcWireFormat',
                                 'lean_429': None, 'lean_430_rc2': 'v1'},
            'diagnostics_equal': True,
            'wait_responses_equal': True,
            'server_notification_counts': {
                'lean_429': sum(e['side'] == 'server' for e in record['events']),
                'lean_430_rc2': sum(e['side'] == 'server' for e in prior['events'])},
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
        prior_batch = baseline['batch'][key]
        assert prior_batch['status'] == 'completed' and prior_batch['exit'] == wanted_exit
        prior_stdout = (HERE / f'baseline-v430-batch-{key}.stdout').read_bytes()
        assert sha(prior_stdout) == prior_batch['stdout_sha256']
        prior_entries = [json.loads(line) for line in prior_stdout.decode().splitlines()]
        assert [{field: value for field, value in entry.items() if field != 'fileName'}
                for entry in entries] == [
                {field: value for field, value in entry.items() if field != 'fileName'}
                for entry in prior_entries]
        if key == 'original':
            error = [x for x in entries if x['severity'] == 'error']
            assert len(error) == 1 and token in error[0]['data']
            assert error[0]['pos'] == {'line': 1, 'column': oracle['begin']['unicode_scalars']}
            assert error[0]['endPos'] == {'line': 1, 'column': oracle['end']['unicode_scalars']}
        else:
            assert not any(x['severity'] == 'error' for x in entries)
            assert any('Nat.zero' in x['data'] for x in entries)
        batch_summary[key] = {'exit': b['exit'], 'message_count': len(entries),
                              'v430_exit': prior_batch['exit'], 'messages_equal_excluding_filename': True,
                              'max_sampled_rss_kib': max(s['process_group_rss_kib'] for s in b['samples']),
                              'min_sampled_reclaimable_percent': min(s['host']['estimated_reclaimable_percent'] for s in b['samples']),
                              'min_sampled_free_disk_bytes': min(s['host']['free_disk_bytes'] for s in b['samples'])}
    comparison = {'schema': 1, 'lean_sha256': result['lean_sha256'],
                  'baseline_lean_sha256': baseline['lean_sha256'],
                  'baseline_results_sha256': sha(baseline_raw),
                  'oracle_prelaunch_sha256': result['oracle_prelaunch_sha256'],
                  'fixture_sha256': result['fixture_sha256'],
                  'coordinate_oracle': {'begin': oracle['begin'], 'end': oracle['end']},
                  'sessions': summary, 'batch': batch_summary,
                  'version_differences': version_differences,
                  'negative_controls': {'utf8_offer_not_selection': True,
                                        'utf8_ranged_edit_did_not_repair': True,
                                        'utf16_ranged_edit_repaired': True},
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
                   and i.get('baseline_results_sha256') == sha(baseline_raw)
                   for i in identities)
    print(json.dumps({'sessions': {k: {'exit': v['exit'], 'after_errors': len(v['after_error_messages'])}
                                    for k, v in summary.items()},
                      'batch_exits': {k: v['exit'] for k, v in batch_summary.items()},
                      'initial_range': oracle['utf16_only_change_range']}))


if __name__ == '__main__':
    main()
