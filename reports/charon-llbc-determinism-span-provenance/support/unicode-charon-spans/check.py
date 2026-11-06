#!/usr/bin/env python3
"""Independently compare retained Charon item spans with source coordinates."""
import hashlib
import json
from pathlib import Path
import sys
import unicodedata

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'fixture/src/lib.rs'
LLBC = HERE / 'unicode.llbc'
RESULTS = HERE / 'results.json'
COMPARISON = HERE / 'comparison.json'
META = HERE / 'REPORT.json'

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def columns(text):
    return {
        'utf8_bytes': len(text.encode('utf-8')),
        'unicode_scalars': len(text),
        'utf16_code_units': len(text.encode('utf-16-le')) // 2,
        # Deliberately narrow independent fixture oracle: combining marks
        # occupy zero display cells; East Asian Wide/Fullwidth occupy two.
        'fixture_display_cells': sum(0 if unicodedata.combining(ch)
            else 2 if unicodedata.east_asian_width(ch) in ('W', 'F') else 1
            for ch in text),
    }

def main():
    source_bytes = SOURCE.read_bytes()
    source = source_bytes.decode('utf-8')
    artifact_bytes = LLBC.read_bytes()
    result = json.loads(RESULTS.read_text())
    llbc = json.loads(artifact_bytes)
    meta = json.loads(META.read_text())
    assert set(meta) == {'topics', 'subjects', 'observed_at'}
    assert meta['observed_at'] == '2026-09-30'
    assert meta['subjects'][0]['identity']['sha256'] == result['versions']['charon_sha256']
    assert meta['subjects'][1]['identity']['cargo_sha256'] == result['versions']['cargo_sha256']
    assert meta['subjects'][1]['identity']['rustc_sha256'] == result['versions']['rustc_sha256']
    assert meta['subjects'][2]['identity']['src_lib_rs_sha256'] == sha(source_bytes)
    assert result['exit'] == 0 and result['stopped'] is None
    assert result['preflight']['free_memory_percent'] >= result['limits']['min_free_memory_percent']
    assert result['preflight']['free_disk_bytes'] >= result['limits']['min_free_disk_bytes']
    assert result['peak_sampled_rss_kib'] < result['limits']['max_extra_rss_kib']
    assert result['peak_sampled_scratch_bytes'] < result['limits']['max_scratch_bytes']
    assert result['final_scratch_bytes'] < result['limits']['max_scratch_bytes']
    assert result['fixture_sha256']['src/lib.rs'] == sha(source_bytes)
    assert result['output'] == {'sha256': sha(artifact_bytes), 'bytes': len(artifact_bytes)}
    assert llbc['has_errors'] is False
    local = [f for f in llbc['translated']['files'] if f['id'] == 0]
    assert len(local) == 1 and local[0]['name']['Local'] == 'src/lib.rs'
    assert local[0]['contents'].encode('utf-8') == source_bytes
    lines = source.splitlines(keepends=False)
    expected_names = {
        'unicode_span_probe::EMOJI', 'unicode_span_probe::COMBINING',
        'unicode_span_probe::after_emoji',
        'unicode_span_probe::after_combining',
        'unicode_span_probe::unicode_body',
    }
    observations = []
    excluded = []
    for category in ('fun_decls', 'global_decls'):
        for item in llbc['translated'][category]:
            meta = item['item_meta']
            span = meta['span']['data']
            name = '::'.join(part['Ident'][0] for part in meta['name'] if 'Ident' in part)
            if span['file_id'] != 0:
                excluded.append({'category': category, 'name': name, 'file_id': span['file_id']})
                continue
            assert name in expected_names
            text = meta['source_text']
            assert text and source.count(text) == 1
            assert span['beg']['line'] == span['end']['line']
            lineno = span['beg']['line']
            assert 1 <= lineno <= len(lines)
            line = lines[lineno-1]
            assert line.count(text) == 1
            start = line.index(text)
            end = start + len(text)
            begin = columns(line[:start])
            finish = columns(line[:end])
            observed = {'beg': span['beg']['col'], 'end': span['end']['col']}
            matched = {mode: (begin[mode] == observed['beg'] and finish[mode] == observed['end'])
                       for mode in begin}
            assert matched['fixture_display_cells'], (category, name, observed, begin, finish)
            observations.append({'category': category, 'name': name, 'line': lineno,
                'source_text': text, 'observed': observed,
                'predicted_begin': begin, 'predicted_end': finish, 'matched': matched})
    assert {o['name'] for o in observations} == expected_names
    assert len(observations) == 7  # two constants are serialized twice
    assert len(excluded) == 1 and excluded[0]['name'] == 'core::str::len'
    mismatches = {mode: sum(not o['matched'][mode] for o in observations)
                  for mode in observations[0]['matched']}
    assert mismatches['fixture_display_cells'] == 0
    assert all(mismatches[mode] > 0 for mode in
               ('utf8_bytes', 'unicode_scalars', 'utf16_code_units'))
    # Rejected controls: shifting the local declaration start or using an
    # inclusive end no longer matches the independently located source text.
    assert any(o['observed']['beg'] + 1 != o['predicted_begin']['fixture_display_cells']
               for o in observations)
    assert any(o['observed']['end'] + 1 != o['predicted_end']['fixture_display_cells']
               for o in observations)
    comparison = {'source_sha256': sha(source_bytes), 'llbc_sha256': sha(artifact_bytes),
        'observations': observations, 'excluded_nonlocal': excluded,
        'mismatch_counts': mismatches,
        'controls': {'begin_plus_one_rejected': True, 'inclusive_end_rejected': True,
                     'changed_source_text_control': 'not_run'}}
    serialized = json.dumps(comparison, indent=2, ensure_ascii=False) + '\n'
    if len(sys.argv) == 2 and sys.argv[1] == '--write':
        COMPARISON.write_text(serialized)
    else:
        assert COMPARISON.read_text() == serialized
    print(json.dumps({'local_records': len(observations), 'excluded_nonlocal': len(excluded),
        'mismatch_counts': mismatches, 'source_sha256': comparison['source_sha256'],
        'llbc_sha256': comparison['llbc_sha256']}, ensure_ascii=False))

if __name__ == '__main__':
    main()
