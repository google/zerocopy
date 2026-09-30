#!/usr/bin/env python3
"""Prepare the exact hand-authored Rust-doc to Lean fixture and oracle."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIX = HERE / 'fixture'
PREFIX = b'///| '
HEADER = b'import Lean\r\n\r\n'  # line 1 is a synthetic empty line
FIRST = '#check "🙂e\u0301"'.encode()
INSERT = '#check ("🙂e\u0301", missingEmpty)'.encode()
HOST = b'// UTF-8/CRLF source fixture\r\n' + PREFIX + FIRST + b'\r\n' + PREFIX + b'\r\n' + b'pub fn probe() {}\r\n'
V1 = HEADER + FIRST + b'\r\n\r\n'
V2 = HEADER + FIRST + b'\r\n' + INSERT + b'\r\n'

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def point(raw, offset):
    assert 0 <= offset <= len(raw)
    preceding = raw[:offset]
    line = preceding.count(b'\n')
    column_bytes = preceding.rsplit(b'\n', 1)[-1]
    column_text = column_bytes.decode('utf-8')
    return {'byte_offset': offset, 'line': line, 'byte_column': len(column_bytes),
            'scalar_column': len(column_text),
            'utf16_column': len(column_text.encode('utf-16-le')) // 2}

def main():
    assert not FIX.exists(), 'fixture already prepared'
    FIX.mkdir()
    files = {'Host.rs': HOST, 'ProjectedV1.lean': V1, 'ProjectedV2.lean': V2}
    for name, raw in files.items():
        (FIX / name).write_bytes(raw)
    host_first = HOST.index(FIRST)
    host_empty = HOST.index(PREFIX, host_first + len(FIRST)) + len(PREFIX)
    projected_first = V1.index(FIRST)
    projected_empty = len(V1) - 2
    assert V1[projected_empty:] == b'\r\n'
    assert HOST[host_empty:] .startswith(b'\r\n')
    target = INSERT.index(b'missingEmpty')
    oracle = {
        'schema': 1, 'bridge': 'hand-authored exact byte copy; not Anneal',
        'sha256': {name: digest(raw) for name, raw in files.items()},
        'prefix_hex': PREFIX.hex(), 'header_hex': HEADER.hex(), 'first_payload_hex': FIRST.hex(),
        'insert_hex': INSERT.hex(),
        'owned_segments': [
            {'kind': 'copied_nonempty', 'host_start': host_first, 'host_end': host_first + len(FIRST),
             'projected_start': projected_first, 'projected_end': projected_first + len(FIRST)},
            {'kind': 'owned_empty_line', 'host_start': host_empty, 'host_end': host_empty,
             'projected_start': projected_empty, 'projected_end': projected_empty}
        ],
        'points': {
            'host_first_end': point(HOST, host_first + len(FIRST)),
            'projected_first_end': point(V1, projected_first + len(FIRST)),
            'host_empty_insertion': point(HOST, host_empty),
            'projected_empty_insertion': point(V1, projected_empty),
            'v2_token_start': point(V2, projected_empty + target),
            'v2_token_end': point(V2, projected_empty + target + len(b'missingEmpty')),
        },
        'edit': {'version_from': 1, 'version_to': 2,
                 'range': {'start': {'line': point(V1, projected_empty)['line'], 'character': 0},
                           'end': {'line': point(V1, projected_empty)['line'], 'character': 0}},
                 'text': INSERT.decode('utf-8')},
        'negative_controls': ['synthetic_header', 'synthetic_blank_line', 'crlf_interior',
                              'wrong_document_version', 'utf16_surrogate_interior'],
    }
    (HERE / 'oracle.json').write_text(json.dumps(oracle, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'fixture': oracle['sha256'], 'oracle_sha256': digest((HERE/'oracle.json').read_bytes()),
                      'points': oracle['points']}, ensure_ascii=False))

if __name__ == '__main__':
    main()
